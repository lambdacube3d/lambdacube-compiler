{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module LambdaCube.Compiler.Parser
    ( parseLC
    , runDefParser
    , ParseWarning (..)
    , DesugarInfo
    , Module
    ) where

import Data.Monoid
import Data.Maybe
import Data.List
import Data.Char
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.RWS
import Control.Arrow hiding ((<+>))
import Control.Applicative

import LambdaCube.Compiler.Utils
import LambdaCube.Compiler.DeBruijn
import LambdaCube.Compiler.Pretty hiding (Doc, braces, parens)
import LambdaCube.Compiler.Lexer
import LambdaCube.Compiler.DesugaredSource
import LambdaCube.Compiler.Patterns
import LambdaCube.Compiler.Statements

-------------------------------------------------------------------------------- parser type

type BodyParser = Parse DesugarInfo PostponedCheck

type PostponedCheck = Either (Maybe LCParseError) ParseCheck

runCheck :: Parse DesugarInfo ParseCheck a -> BodyParser a
runCheck = mapRWST $ fmap $ \(a, b, c) -> (a, b, Right <$> c)

data LCParseError
    = MultiplePatternVars [[SIName]]
    | OperatorMismatch SIName SIName
    | UndefinedConstructor SIName
    | ParseError ParseError

data ParseWarning
    = Unreachable Range
    | Uncovered SIName [PatList]

instance PShow LCParseError where
    pShow = \case
        MultiplePatternVars xs -> vcat $ "multiple pattern vars:":
            concat [(shortForm (pShow $ head ns) <+> "is defined at"): map pShow ns | ns <- xs]
        OperatorMismatch op op' -> "Operator precedences don't match:" <$$> pShow (fromJust $ nameFixity op) <+> "at" <+> pShow op <$$> pShow (fromJust $ nameFixity op') <+> "at" <+> pShow op'
        UndefinedConstructor n -> "Constructor" <+> shortForm (pShow n) <+> "is not defined at" <+> pShow n
        ParseError p -> text $ show p

instance PShow ParseWarning where
    pShow = \case
        Unreachable si -> "Source code is not reachable:" <+> pShow si
        Uncovered sn pss -> "Uncovered pattern(s) at" <+> pShow (sourceInfo sn) <$$>
            nest 4 (shortForm $ vcat $ "Missing case(s):" :
                    [ addG (foldl DApp (pShow sn) (pShow <$> ps)) [DOp "<-" (Infix (-1)) (pShow p) (pShow e) | (p, e) <- gs]
                    | (ps, gs) <- pss]
            )
          where
            addG x [] = x
            addG x xs = DOp "|" (Infix (-5)) x $ foldr1 (DOp "," (InfixR (-4))) xs

trackSI :: SourceInfo a => BodyParser a -> BodyParser a
trackSI p = do
    x <- p
    tell $ Right . TrackedCode <$> maybeToList (getRange $ sourceInfo x)
    return x

addFixity :: BodyParser SIName -> BodyParser SIName
addFixity p = f <$> asks (fixityMap . desugarInfo) <*> p
  where
    f :: Map.Map SName Fixity -> SIName -> SIName
    f fm sn@(SIName_ si _ n) = SIName_ si (Just $ defaultFixity $ Map.lookup n fm) n

addFixity' :: BodyParser SIName -> BodyParser SIName
addFixity' p = f <$> asks (fixityMap . desugarInfo) <*> p
  where
    f :: Map.Map SName Fixity -> SIName -> SIName
    f fm sn@(SIName_ si _ n) = SIName_ si (Map.lookup n fm) n

addConsInfo :: BodyParser SIName -> BodyParser (SIName, ConsInfo)
addConsInfo p = join $ f <$> asks (consMap . desugarInfo) <*> p
  where
    f :: Map.Map String ConsInfo -> SIName -> BodyParser (SIName, ConsInfo)
    f adts s = do
        tell [Left $ either (Just . UndefinedConstructor) (const Nothing) x]
        return $ either (const $ error "impossible @ Parser 826") id x
      where
        x :: Either SIName (SIName, ConsInfo)
        x = case Map.lookup (sName s) adts of
            Nothing -> throwError s
            Just i -> return (s, i)

addForalls' :: BodyParser SExp -> BodyParser SExp
addForalls' p = addForalls_ mempty <*> p

addForalls_ :: [SIName] -> BodyParser (SExp -> SExp)
addForalls_ s = addForalls . (Set.fromList (sName <$> s) <>) <$> asks (definedSet . desugarInfo)

-------------------------------------------------------------------------------- desugar info

-- TODO: filter this in module imports
data DesugarInfo = DesugarInfo
    { fixityMap  :: Map.Map SName Fixity
    , consMap    :: Map.Map SName ConsInfo
    , definedSet :: DefinedSet
    }

instance Monoid DesugarInfo where
    mempty = DesugarInfo mempty mempty mempty
#if !MIN_VERSION_base(4,11,0)
    DesugarInfo a b c `mappend` DesugarInfo a' b' c' = DesugarInfo (a <> a') (b <> b') (c <> c')
#else
instance Semigroup DesugarInfo where
    DesugarInfo a b c <> DesugarInfo a' b' c' = DesugarInfo (a <> a') (b <> b') (c <> c')
#endif

mkDesugarInfo :: [Stmt] -> DesugarInfo
mkDesugarInfo ss = DesugarInfo
    { fixityMap = Map.fromList $ ("'EqCTt", Infix (-1)): [(sName s, f) | PrecDef s f <- ss]
    , consMap = Map.fromList $
        [(sName cn, Left ((CaseName $ sName t, pars ty), second pars <$> cs)) | Data t ps ty cs <- ss, (cn, ct) <- cs]
     ++ [(sName t, Right $ pars $ UncurryS ps ty) | Data t ps ty _ <- ss]
--     ++ [(t, Right $ length xs) | StLet (_, t) _ (Just ty) xs _ <- ss]
     ++ [("'Type", Right 0)]
    , definedSet = Set.singleton "'Type" <> foldMap defined ss
    }
  where
    pars :: SExp' a -> Int
    pars (UncurryS l _) = length $ filter ((== Visible) . fst) l -- todo

    defined :: Stmt -> Set.Set SName
    defined = \case
        StLet sn _ _ -> Set.singleton $ sName sn
        Data sn _ _ cs -> Set.fromList $ sName sn: map (sName . fst) cs
        PrecDef{} -> mempty

-------------------------------------------------------------------------------- expression parsing

hiddenTerm :: BodyParser a -> BodyParser a -> BodyParser (Visibility, a)
hiddenTerm p q = (,) Hidden <$ reservedOp "@" <*> typeNS p  <|>  (,) Visible <$> q

parseType :: Maybe SExp -> BodyParser SExp
parseType mb = maybe id option mb (reservedOp "::" *> typeNS (setR parseTermLam))

typedIds :: DeBruijnify SIName a => (BodyParser SExp -> BodyParser a) -> [SIName] -> BodyParser [(SIName, a)]
typedIds f ds = (\ns t -> (,) <$> ns <*> pure t) <$> commaSep1 upperLower <*> (deBruijnify (ds :: [SIName]) <$> f (parseType Nothing))

telescope :: Maybe SExp -> BodyParser ([SIName], [(Visibility, SExp)])
telescope mb = fmap mkTelescope $ many $ hiddenTerm
    (typedId <|> maybe empty (tvar . pure) mb)
    (try_ "::" typedId <|> maybe ((,) (SIName mempty "") <$> typeNS (setR parseTermAtom)) (tvar . pure) mb)
  where
    tvar :: BodyParser SExp -> BodyParser (SIName, SExp)
    tvar x = (,) <$> patVar <*> x

    typedId :: BodyParser (SIName, SExp)
    typedId = parens $ tvar $ parseType mb

mkTelescope :: [(Visibility,(SIName,SExp))] -> ([SIName],[(Visibility,SExp)])
mkTelescope (unzip -> (vs, ns)) = second (zip vs) $ mkTelescope' $ first (:[]) <$> ns

mkTelescope' :: DeBruijnify SIName a => [([SIName],a)] -> ([SIName],[a])
mkTelescope' = go []
  where
    go :: DeBruijnify SIName a => [SIName] -> [([SIName],a)] -> ([SIName],[a])
    go ns [] = (ns, [])
    go ns ((n, e): ts) = second (deBruijnify ns e:) $ go (n ++ ns) ts

parseTermLam :: BodyParser SExp
parseTermLam =
         do level parseTermAnn $ \t ->
                mkPi <$> (Visible <$ reservedOp "->" <|> Hidden <$ reservedOp "=>") <*> pure t <*> setR parseTermLam
     <|> mkIf <$ reserved "if"   <*> setR parseTermLam
              <* reserved "then" <*> setR parseTermLam
              <* reserved "else" <*> setR parseTermLam
     <|> do (fe, ts) <- reserved "forall" *> telescope (Just $ Wildcard SType)
            f <- SPi . const Hidden <$ reservedOp "." <|> SPi . const Visible <$ reservedOp "->"
            t' <- deBruijnify fe <$> setR parseTermLam
            return $ foldr (uncurry f) t' ts
     <|> do expNS $ do
                (fe, ts) <- reservedOp "\\" *> telescopePat <* reservedOp "->"
                foldr (\e m -> runCheck . uncurry (patLam id) e =<< m) (deBruijnify fe <$> setR parseTermLam) ts
     <|> do join $ (runCheck .) . compileCase <$ reserved "case" <*> setR parseTermLam <* reserved "of" <*> do
                identation False $ do
                    (fe, p) <- longPattern
                    (,) p . deBruijnify fe <$> parseRHS "->"
  where
    mkIf :: SExp -> SExp -> SExp -> SExp
    mkIf b t f = SBuiltin FprimIfThenElse `SAppV` b `SAppV` t `SAppV` f

    mkPi :: Visibility -> SExp -> SExp -> SExp
    mkPi Hidden xs b = foldr (\a b -> SPi Hidden a $ up1 b) b $ map SCW $ getTTuple xs
    mkPi Visible a b = SPi Visible a $ up1 b

parseTermAnn :: BodyParser SExp
parseTermAnn = level parseTermOp $ \t -> SAnn t <$> parseType Nothing

parseTermOp :: BodyParser SExp
parseTermOp = (notOp False <|> notExp) >>= calculatePrecs
  where
    notExp :: BodyParser [Either SIName SExp]
    notExp = (++) <$> ope <*> notOp True

    notOp :: Bool -> BodyParser [Either SIName SExp]
    notOp x = (++) <$> try_ "expression" ((++) <$> ex parseTermApp <*> option [] ope) <*> notOp True
         <|> if x then option [] (try_ "lambda" $ ex parseTermLam) else mzero

    ope :: BodyParser [Either SIName SExp]
    ope = pure . Left <$> addFixity (rhsOperator <|> appRange (flip SIName "'EqCTt" <$ reservedOp "~"))

    ex :: BodyParser SExp -> BodyParser [Either SIName SExp]
    ex pr = pure . Right <$> setR pr

    calculatePrecs :: [Either SIName SExp] -> BodyParser SExp
    calculatePrecs = go where

        go :: [Either SIName SExp] -> BodyParser SExp
        go (Right e: xs)         = waitOp False e [] xs
        go xs@(Left (sName -> "-"): _) = waitOp False (mkLit $ LInt 0) [] xs
        go (Left op: xs)         = Section . SLamV <$> waitExp True (sVar "leftSection" 0) [] op xs
        go _                     = error "impossible @ Parser 479"

        waitExp :: Bool -> SExp -> [(SIName, SExp)] -> SIName -> [Either SIName SExp] -> BodyParser SExp
        waitExp lsec e acc op (Right t: xs)  = waitOp lsec e ((op, if lsec then up 1 t else t): acc) xs
        waitExp lsec e acc op [] | lsec      = fail "two-sided section is not allowed"
                                 | otherwise = fmap (Section . SLamV) . calcPrec' e $ (op, sVar "rightSection" 0): map (second (up 1)) acc
        waitExp _ _ _ _ _                    = fail "two operator is not allowed next to each-other"

        waitOp :: Bool -> SExp -> [(SIName, SExp)] -> [Either SIName SExp] -> BodyParser SExp
        waitOp lsec e acc (Left op: xs) = waitExp lsec e acc op xs
        waitOp lsec e acc []            = calcPrec' e acc
        waitOp lsec e acc _             = error "impossible @ Parser 488"

        calcPrec' :: SExp -> [(SIName, SExp)] -> BodyParser SExp
        calcPrec' e = postponedCheck id . calcPrec (\op x y -> SGlobal op `SAppV` x `SAppV` y) (fromJust . nameFixity) e . reverse

parseTermApp :: BodyParser SExp
parseTermApp =
        AppsS <$> try_ "record" (SGlobal <$> upperCase <* symbol "{")
              <*> commaSep ((,) Visible <$ lowerCase{-TODO-} <* reservedOp "=" <*> setR parseTermLam)
              <*  symbol "}"
     <|> AppsS <$> setR parseTermSwiz <*> many (hiddenTerm (setR parseTermSwiz) $ setR parseTermSwiz)

parseTermSwiz :: BodyParser SExp
parseTermSwiz = level parseTermProj $ \t ->
    mkSwizzling t <$> lexeme (try_ "swizzling" $ char '%' *> count' 1 4 (satisfy (`elem` ("xyzwrgba" :: String))))
  where
    mkSwizzling :: SExp -> String -> SExp
    mkSwizzling term = swizzcall . map (SBuiltin . sc . synonym)
      where
        swizzcall :: [SExp] -> SExp
        swizzcall []  = error "impossible: swizzling parsing returned empty pattern"
        swizzcall [x] = SBuiltin Fswizzscalar `SAppV` term `SAppV` x
        swizzcall xs  = SBuiltin Fswizzvector `SAppV` term `SAppV` foldl SAppV (SBuiltin $ f (length xs)) xs

        sc :: Char -> FNameTag
        sc 'x' = FSx
        sc 'y' = FSy
        sc 'z' = FSz
        sc 'w' = FSw

        f :: Int -> FNameTag
        f 2 = FV2
        f 3 = FV3
        f 4 = FV4

        synonym :: Char -> Char
        synonym 'r' = 'x'
        synonym 'g' = 'y'
        synonym 'b' = 'z'
        synonym 'a' = 'w'
        synonym c   = c

parseTermProj :: BodyParser SExp
parseTermProj = level parseTermAtom $ \t ->
    try_ "projection" $ mkProjection t <$ char '.' <*> sepBy1 lowerCase (char '.')
  where
    mkProjection :: SExp -> [SIName] -> SExp
    mkProjection = foldl $ \exp field -> SBuiltin Fproject `SAppV` litString field `SAppV` exp

parseTermAtom :: BodyParser SExp
parseTermAtom =
         mkLit <$> try_ "literal" parseLit
     <|> Wildcard (Wildcard SType) <$ reserved "_"
     <|> mkLets <$ reserved "let" <*> parseDefs sLHS <* reserved "in" <*> setR parseTermLam
     <|> SGlobal <$> lowerCase
     <|> SGlobal <$> upperCase_
     <|> braces (mkRecord <$> commaSep ((,) <$> lowerCase <* symbol ":" <*> setR parseTermLam))
     <|> char '\'' *> ppa switchNamespace
     <|> ppa id
  where
    ppa :: (Namespace -> Namespace) -> BodyParser SExp
    ppa tick =
         brackets ( (setR parseTermLam >>= \e ->
                mkDotDot e <$ reservedOp ".." <*> setR parseTermLam
            <|> join (foldr (=<<) (pure $ BCons e BNil) <$ reservedOp "|" <*> commaSep (generator <|> letdecl <|> boolExpression))
            <|> mkList . tick <$> asks namespace <*> ((e:) <$> option [] (symbol "," *> commaSep1 (setR parseTermLam)))
            ) <|> mkList . tick <$> asks namespace <*> pure [])
     <|> parens (SGlobal <$> try_ "opname" (symbols <* lookAhead (symbol ")"))
             <|> mkTuple . tick <$> asks namespace <*> commaSep (setR parseTermLam))

    mkTuple :: Namespace -> [SExp] -> SExp
    mkTuple _      [Section e] = e
    mkTuple ExpNS  [Parens e]  = HCons e HNil
    mkTuple TypeNS [Parens e]  = HList $ BCons e BNil
    mkTuple _      [x]         = Parens x
    mkTuple ExpNS  xs          = foldr HCons HNil xs
    mkTuple TypeNS xs          = HList $ foldr BCons BNil xs

    mkList :: Namespace -> [SExp] -> SExp
    mkList TypeNS [x] = BList x
    mkList _      xs  = foldr BCons BNil xs

    -- Creates: RecordCons @[("x", _), ("y", _), ("z", _)] (1.0, 2.0, 3.0)))
    mkRecord :: [(SIName, SExp)] -> SExp
    mkRecord (unzip -> (names, values))
        = SBuiltin FRecordCons `SAppH` foldr BCons BNil (mkRecItem <$> names) `SAppV` foldr HCons HNil values

    mkRecItem :: SIName -> SExp
    mkRecItem l = SBuiltin FRecItem `SAppV` litString l `SAppV` Wildcard SType

    mkDotDot :: SExp -> SExp -> SExp
    mkDotDot e f = SBuiltin FfromTo `SAppV` e `SAppV` f

    generator, letdecl, boolExpression :: BodyParser (SExp -> ErrorFinder SExp)
    generator = do
        (dbs, pat) <- try_ "generator" $ longPattern <* reservedOp "<-"
        checkPattern dbs
        exp <- setR parseTermLam
        return $ \e -> do
            cf <- runCheck $ compileGuardTree id id (Just $ SIName (sourceInfo pat) "") [(Visible, Wildcard SType)]
                           $ compilePatts [pat] (noGuards $ deBruijnify dbs e) `mappend` noGuards BNil
            return $ SBuiltin FconcatMap `SAppV` cf `SAppV` exp

    letdecl = (return .) . mkLets <$ reserved "let" <*> (runCheck . compileStmt' =<< valueDef)

    boolExpression = (\pred e -> return $ SBuiltin FprimIfThenElse `SAppV` pred `SAppV` e `SAppV` BNil) <$> setR parseTermLam


level :: BodyParser SExp -> (SExp -> BodyParser SExp) -> BodyParser SExp
level pr f = pr >>= \t -> option t $ f t

litString :: SIName -> SExp
litString (SIName si n) = SLit si $ LString n

mkLit :: Lit -> SExp
mkLit n@LInt{} = SBuiltin FfromInt `SAppV` sLit n
mkLit l = sLit l

-------------------------------------------------------------------------------- pattern parsing

setR :: SetSourceInfo a => BodyParser a -> BodyParser a
setR p = appRange $ flip setSI <$> p

parsePatAnn :: BodyParser ParPat
parsePatAnn = patType <$> setR parsePatOp <*> parseType (Just $ Wildcard SType)
  where
    patType :: ParPat -> SExp -> ParPat
    patType p (Wildcard SType) = p
    patType p t = PatTypeSimp p t

parsePatOp :: BodyParser ParPat
parsePatOp = join $ calculatePatPrecs <$> setR parsePatApp <*> option [] (oper >>= p)
  where
    oper :: BodyParser (SIName, ConsInfo)
    oper = addConsInfo $ addFixity colonSymbols

    p :: (SIName,ConsInfo) -> BodyParser [((SIName, ConsInfo), ParPat)]
    p op = do (exp, op') <- try_ "pattern" $ (,) <$> setR parsePatApp <*> oper
              ((op, exp):) <$> p op'
       <|> pure . (,) op <$> setR parsePatAnn

    calculatePatPrecs :: ParPat -> [((SIName, ConsInfo), ParPat)] -> BodyParser ParPat
    calculatePatPrecs e xs = postponedCheck fst $ calcPrec (\op x y -> PConSimp op [x, y]) (fromJust . nameFixity . fst) e xs

parsePatApp :: BodyParser ParPat
parsePatApp =
         PConSimp <$> addConsInfo upperCase_ <*> many (setR parsePatAt)
     <|> parsePatAt

parsePatAt :: BodyParser ParPat
parsePatAt = concatParPats <$> sepBy1 (setR parsePatAtom) (noSpaceBefore $ reservedOp "@")
  where
    concatParPats :: [ParPat] -> ParPat
    concatParPats ps = ParPat $ concat [p | ParPat p <- ps]

parsePatAtom :: BodyParser ParPat
parsePatAtom =
         mkLit <$> asks namespace <*> try_ "literal" parseLit
     <|> flip PConSimp [] <$> addConsInfo upperCase_
     <|> mkPVar <$> patVar
     <|> char '\'' *> ppa switchNamespace
     <|> ppa id
  where
    mkLit :: Namespace -> Lit -> ParPat
    mkLit TypeNS (LInt n) = iterateN (fromIntegral n) cSucc cZero        -- todo: elim this alternative
    mkLit _ n@LInt{} = litP (SBuiltin FfromInt `SAppV` sLit n)
    mkLit _ n = litP (sLit n)

    ppa :: (Namespace -> Namespace) -> BodyParser ParPat
    ppa tick =
         brackets (mkListPat . tick <$> asks namespace <*> patlist)
     <|> parens   (parseViewPat <|> mkTupPat  . tick <$> asks namespace <*> patlist)

    mkListPat :: Namespace -> [ParPat] -> ParPat
    mkListPat TypeNS [p] = cList p
    mkListPat ns ps      = foldr cCons cNil ps

    mkTupPat :: Namespace -> [ParPat] -> ParPat
    mkTupPat TypeNS [PParens x] = mkTTup [x]
    mkTupPat ns     [PParens x] = mkTup [x]
    mkTupPat _      [x]         = PParens x
    mkTupPat TypeNS ps          = mkTTup ps
    mkTupPat ns     ps          = mkTup ps

    mkTTup = cHList . mkListPat ExpNS
    mkTup ps = foldr cHCons cHNil ps

    parseViewPat :: BodyParser ParPat
    parseViewPat = ViewPatSimp <$> try_ "view pattern" (setR parseTermOp <* reservedOp "->") <*> setR parsePatAnn

    mkPVar :: SIName -> ParPat
    mkPVar (SIName si "") = PWildcard si
    mkPVar s = PVarSimp s

    litP :: SExp -> ParPat
    litP = flip ViewPatSimp cTrue . SAppV (SGlobal $ SIName_ mempty (Just $ Infix 4) "==")

    patlist :: BodyParser [ParPat]
    patlist = commaSep $ setR parsePatAnn

longPattern :: BodyParser ([SIName], ParPat)
longPattern = setR parsePatAnn <&> (reverse . getPVars &&& id)

telescopePat :: BodyParser ([SIName], [((Visibility,SExp),ParPat)])
telescopePat = do
    (a, b) <- fmap (reverse . foldMap (getPVars . snd) &&& id) $ many $ uncurry f <$> hiddenTerm (setR parsePatAt) (setR parsePatAt)
    checkPattern a
    return (a, b)
  where
    f :: Visibility -> ParPat -> ((Visibility,SExp),ParPat)
    f h (PParens p) = second PParens $ f h p
    f h (PatTypeSimp p t) = ((h, t), p)
    f h p = ((h, Wildcard SType), p)

checkPattern :: [SIName] -> BodyParser ()
checkPattern ns = tell $ pure $ Left $ 
   case [reverse ns' | ns'@(_:_:_) <- group . sort . filter (not . null . sName) $ ns] of
    [] -> Nothing
    xs -> Just $ MultiplePatternVars xs

postponedCheck :: (a -> SIName) -> Either (a,a) b -> BodyParser b
postponedCheck pr x = do
    tell [Left $ either (\(a, b) -> Just $ OperatorMismatch (pr a) (pr b)) (const Nothing) x]
    return $ either (const $ error "impossible @ Parser 725") id x

type ErrorFinder = BodyParser

-------------------------------------------------------------------------------- declaration parsing

parseDef :: BodyParser [PreStmt]
parseDef =
     do reserved "data" *> do
            x <- typeNS upperCase
            (npsd, ts) <- telescope (Just SType)
            t <- deBruijnify npsd <$> parseType (Just SType)
            adf <- addForalls_ npsd
            let mkConTy :: Bool -> ([SIName], [(Visibility, SExp)]) -> (Maybe [SIName], SExp)
                mkConTy mk (nps', ts') =
                    ( if mk then Just $ reverse nps' else Nothing
                    , deBruijnify npsd $ foldr (uncurry SPi) (foldl SAppV (SGlobal x) $ SGlobal <$> reverse npsd) ts'
                    )
            (af, cs) <- option (True, []) $
                 (,) True . map (second $ (,) Nothing) . concat <$ reserved "where" <*> identation True (typedIds id npsd)
             <|> (,) False <$ reservedOp "=" <*>
                      sepBy1 ((,) <$> (addFixity' upperCase <|> parens (addFixity colonSymbols))
                                  <*> (mkConTy True <$> braces telescopeDataFields <|> mkConTy False <$> telescope Nothing)
                             )
                             (reservedOp "|")
            mkData x ts t $ second (second $ if af then adf else id) <$> cs
 <|> do reserved "class" *> do
            x <- typeNS upperCase
            (nps, ts) <- telescope (Just SType)
            cs <- option [] $ concat <$ reserved "where" <*> identation True (typedIds id nps)
            return $ pure $ Class x (map snd ts) cs
 <|> do reserved "instance" *> do
          typeNS $ do
            constraints <- option [] $ try_ "constraint" $ getTTuple <$> setR parseTermOp <* reservedOp "=>"
            x <- upperCase
            (nps, args) <- telescopePat
            cs <- expNS $ option [] $ reserved "where" *> identation False ({-deBruijnify nps <$> -} funAltDef (Just lhsOperator) varId)
            pure . Instance x ({-todo-}map snd args) (deBruijnify nps <$> constraints) <$> runCheck (compileStmt' cs)
 <|> do reserved "type" *> do
            typeNS $ do
                reserved "family" *> do
                    x <- upperCase
                    (nps, ts) <- telescope (Just SType)
                    t <- deBruijnify nps <$> parseType (Just SType)
                    option {-open type family-}[TypeFamily x $ UncurryS ts t] $ do
                        cs <- (reserved "where" >>) $ identation True $ funAltDef Nothing $ mfilter (== x) upperCase
                        -- closed type family desugared here
                        runCheck $ fmap Stmt <$> compileStmt SLHS (compileGuardTrees id . const Nothing) [TypeAnn x $ UncurryS ts t] cs
             <|> pure <$ reserved "instance" <*> funAltDef Nothing upperCase
             <|> do x <- upperCase
                    (nps, ts) <- telescope $ Just (Wildcard SType)
                    rhs <- deBruijnify nps <$ reservedOp "=" <*> setR parseTermLam
                    runCheck $ fmap Stmt <$> compileStmt SLHS (compileGuardTrees id . const Nothing)
                        [{-TypeAnn x $ UncurryS ts $ SType-}{-todo-}]
                        [funAlt' x ts (map PVarSimp $ reverse nps) $ noGuards rhs]
 <|> do try_ "typed ident" $ map (uncurry TypeAnn) <$> typedIds addForalls' []
 <|> fmap . (Stmt .) . flip PrecDef <$> parseFixity <*> commaSep1 rhsOperator
 <|> pure <$> funAltDef (Just lhsOperator) varId
 <|> valueDef
  where
    telescopeDataFields :: BodyParser ([SIName], [(Visibility, SExp)]) 
    telescopeDataFields = mkTelescope <$> commaSep ((,) Visible <$> ((,) <$> lowerCase <*> parseType Nothing))

    mkData :: SIName -> [(Visibility, SExp)] -> SExp -> [(SIName, (Maybe [SIName], SExp))] -> BodyParser [PreStmt]
    mkData x ts t cs
        = (Stmt (Data x ts t (second snd <$> cs)):) . concat <$> traverse mkProj (nub $ concat [fs | (_, (Just fs, _)) <- cs])
      where
        mkProj :: SIName -> BodyParser [PreStmt]
        mkProj fn = sequence
            [ do
                cn' <- addConsInfo $ pure cn

                return $ funAlt' fn [(Visible, Wildcard SType)]
                                    [PConSimp cn' [if i == j then PVarSimp (dummyName "x") else PWildcard mempty | j <- [0..length fs-1]]]
                       $ noGuards $ sVar "proj" 0
            | (cn, (Just fs, _)) <- cs, (i, fn') <- zip [0..] fs, fn' == fn
            ]

parseRHS :: String -> BodyParser GuardTrees
parseRHS tok = do
    mkGuards <$> some (reservedOp "|" *> guard) <*> option [] (reserved "where" *> parseDefs sLHS)
  <|> do
    rhs <- reservedOp tok *> setR parseTermLam
    f <- option id $ mkLets <$ reserved "where" <*> parseDefs sLHS
    noGuards <$> trackSI (pure $ f rhs)
  where
    guard :: BodyParser ([(ParPat, SExp)], SExp)
    guard = do
        (nps, ps) <- mkTelescope' <$> commaSep1 guardPiece <* reservedOp tok
        e <- trackSI $ setR parseTermLam
        return (ps, deBruijnify nps e)

    guardPiece :: BodyParser ([SIName], (ParPat, SExp))
    guardPiece = getVars <$> option cTrue (try_ "pattern guard" $ setR parsePatOp <* reservedOp "<-") <*> setR parseTermOp
      where
        getVars :: ParPat -> SExp -> ([SIName], (ParPat, SExp))
        getVars p e = (reverse $ getPVars p, (p, e))

    mkGuards :: [([(ParPat, SExp)], SExp)] -> [Stmt] -> GuardTrees
    mkGuards gs wh = mkLets_ lLet wh $ mconcat [foldr (uncurry guardNode') (noGuards e) ge | (ge, e) <- gs]

parseDefs :: (SIName -> SExp -> SExp) -> BodyParser [Stmt]
parseDefs lhs = identation True parseDef >>= runCheck . compileStmt'_ lhs SRHS SRHS . concat

funAltDef :: Maybe (BodyParser SIName) -> BodyParser SIName -> BodyParser PreStmt
funAltDef parseOpName parseName = do
    (n, (fee, tss)) <-
        case parseOpName of
          Nothing -> mzero
          Just opName -> try_ "operator definition" $ do
            (e', a1) <- longPattern
            n <- opName
            (e'', a2) <- longPattern <* lookAhead (reservedOp "=" <|> reservedOp "|")
            let fee :: [SIName]
                fee = e'' <> e'
            checkPattern fee
            return (n, (fee, (,) (Visible, Wildcard SType) <$> [a1, deBruijnify e' a2]))
      <|> do try_ "lhs" $ (,) <$> parseName <*> telescopePat <* lookAhead (reservedOp "=" <|> reservedOp "|")
    funAlt n tss . deBruijnify fee <$> parseRHS "="

valueDef :: BodyParser [PreStmt]
valueDef = do
    (dns, p) <- try_ "pattern" $ longPattern <* reservedOp "="
    checkPattern dns
    runCheck . desugarValueDef p =<< setR parseTermLam

-------------------------------------------------------------------------------- modules

parseExport :: HeaderParser Export
parseExport =
        ExportModule <$ reserved "module" <*> moduleName
    <|> ExportId <$> varId

importlist :: HeaderParser [SIName]
importlist = parens $ commaSep upperLower

parseExtensions :: HeaderParser [Extension]
parseExtensions
    = try_ "pragma" (symbol "{-#") *> symbol "LANGUAGE" *> commaSep (lexeme ext) <* symbolWithoutSpace "#-}" <* simpleSpace
  where
    ext = do
        s <- some $ satisfy isAlphaNum
        maybe
          (fail $ "language extension expected instead of " ++ s)
          return
          (Map.lookup s extensionMap)

type Module = Module_ DefParser

type DefParser = DesugarInfo -> Either ParseError ([Stmt], [PostponedCheck])

type HeaderParser = Parse () ()

parseModule :: HeaderParser Module
parseModule = do
    exts <- concat <$> many parseExtensions
    whiteSpace
    header <- optional $ do
        modn <- reserved "module" *> moduleName
        exps <- optional (parens $ commaSep parseExport) <* reserved "where"
        return (modn, exps)
    let mkIDef :: Maybe SI -> SIName -> Maybe [SIName] -> Maybe [SIName] -> Maybe SIName -> (SIName, ImportItems)
        mkIDef _ n i h _ = (n, f i h)
          where
            f :: Maybe [SIName] -> Maybe [SIName] -> ImportItems
            f Nothing Nothing = ImportAllBut []
            f (Just h) Nothing = ImportAllBut h
            f Nothing (Just i) = ImportJust i
    idefs <- many $
          mkIDef <$  reserved "import"
                 <*> optional (reserved "qualified")
                 <*> moduleName
                 <*> optional (reserved "hiding" *> importlist)
                 <*> optional importlist
                 <*> optional (reserved "as" *> moduleName)
    (env, st) <- getParseState
    return Module
        { extensions    = exts
        , moduleImports = [(SIName mempty "Prelude", ImportAllBut []) | NoImplicitPrelude `notElem` exts] ++ idefs
        , moduleExports = join $ snd <$> header
        , definitions   = \ge -> runParse (parseDefs SLHS <* eof) (env { desugarInfo = ge }, st)
        }

parseLC :: FileInfo -> Either ParseError Module
parseLC fi
    = fmap fst $ runParse parseModule $ parseState fi ()

runDefParser :: (MonadFix m, MonadError LCParseError m) => DesugarInfo -> DefParser -> m ([Stmt], [ParseWarning], DesugarInfo)
runDefParser ds_ dp = do

    (defs, dns, ds) <- mfix $ \ ~(_, _, ds) -> do
        let x :: Either ParseError ([Stmt], [PostponedCheck])
            x = dp (ds <> ds_)
        (defs, dns) <- either (throwError . ParseError) return x
        return (defs, dns, mkDesugarInfo defs)

    mapM_ throwError [x | Left (Just x) <- dns]

    let ism :: Set.Set Range
        ism = Set.fromList [is | Right (Reachable is) <- dns]
        f :: ParseCheck -> Maybe ParseWarning
        f (TrackedCode is) | is `Set.notMember` ism = Just $ Unreachable is
        f (Uncovered' si x) | not $ null $ filter (not . null . fst) x = Just $ Uncovered si x
        f _ = Nothing

    return (concatMap desugarMutual $ sortDefs defs, catMaybes [f w | Right w <- dns], ds)

