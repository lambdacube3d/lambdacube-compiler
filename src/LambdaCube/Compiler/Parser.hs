{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
import Control.DeepSeq

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

instance NFData ParseWarning
 where
    rnf = \case
        Unreachable r -> rnf r
        Uncovered si r -> () --rnf si -- TODO --rnf r

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

trackSI p = do
    x <- p
    tell $ Right . TrackedCode <$> maybeToList (getRange $ sourceInfo x)
    return x

addFixity :: BodyParser SIName -> BodyParser SIName
addFixity p = f <$> asks (fixityMap . desugarInfo) <*> p
  where
    f fm sn@(SIName_ si _ n) = SIName_ si (Just $ defaultFixity $ Map.lookup n fm) n

addFixity' :: BodyParser SIName -> BodyParser SIName
addFixity' p = f <$> asks (fixityMap . desugarInfo) <*> p
  where
    f fm sn@(SIName_ si _ n) = SIName_ si (Map.lookup n fm) n

addConsInfo p = join $ f <$> asks (consMap . desugarInfo) <*> p
  where
    f adts s = do
        tell [Left $ either (Just . UndefinedConstructor) (const Nothing) x]
        return $ either (const $ error "impossible @ Parser 826") id x
      where
        x = case Map.lookup (sName s) adts of
            Nothing -> throwError s
            Just i -> return (s, i)

addForalls' :: BodyParser SExp -> BodyParser SExp
addForalls' p = addForalls_ mempty <*> p

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
    DesugarInfo a b c `mappend` DesugarInfo a' b' c' = DesugarInfo (a <> a') (b <> b') (c <> c')

mkDesugarInfo :: [Stmt] -> DesugarInfo
mkDesugarInfo ss = DesugarInfo
    { fixityMap = Map.fromList $ ("'EqCTt", Infix (-1)): [(sName s, f) | PrecDef s f <- ss]
    , consMap = Map.fromList $
        [(sName cn, Left ((CaseName $ sName t, pars ty), second pars <$> cs)) | Data t ps ty cs <- ss, (cn, ct) <- cs]
     ++ [(sName t, Right $ pars $ UncurryS ps ty) | Data t ps ty _ <- ss]
--     ++ [(t, Right $ length xs) | Let (_, t) _ (Just ty) xs _ <- ss]
     ++ [("'Type", Right 0)]
    , definedSet = Set.singleton "'Type" <> foldMap defined ss
    }
  where
    pars (UncurryS l _) = length $ filter ((== Visible) . fst) l -- todo

    defined = \case
        Let sn _ _ -> Set.singleton $ sName sn
        Data sn _ _ cs -> Set.fromList $ sName sn: map (sName . fst) cs
        PrecDef{} -> mempty

-------------------------------------------------------------------------------- expression parsing

hiddenTerm p q = (,) Hidden <$ reservedOp "@" <*> typeNS p  <|>  (,) Visible <$> q

parseType mb = maybe id option mb (reservedOp "::" *> typeNS (setR parseTermLam))

typedIds f ds = (\ns t -> (,) <$> ns <*> pure t) <$> commaSep1 upperLower <*> (deBruijnify (ds :: [SIName]) <$> f (parseType Nothing))

telescope mb = fmap mkTelescope $ many $ hiddenTerm
    (typedId <|> maybe empty (tvar . pure) mb)
    (try_ "::" typedId <|> maybe ((,) (SIName mempty "") <$> typeNS (setR parseTermAtom)) (tvar . pure) mb)
  where
    tvar x = (,) <$> patVar <*> x
    typedId = parens $ tvar $ parseType mb

mkTelescope (unzip -> (vs, ns)) = second (zip vs) $ mkTelescope' $ first (:[]) <$> ns

mkTelescope' = go []
  where
    go ns [] = (ns, [])
    go ns ((n, e): ts) = second (deBruijnify ns e:) $ go (n ++ ns) ts

--parseTerm... :: BodyParser SExp
parseTermLam =
         do level parseTermAnn $ \t ->
                mkPi <$> (Visible <$ reservedOp "->" <|> Hidden <$ reservedOp "=>") <*> pure t <*> setR parseTermLam
     <|> mkIf <$ reserved "if"   <*> setR parseTermLam
              <* reserved "then" <*> setR parseTermLam
              <* reserved "else" <*> setR parseTermLam
     <|> do reserved "forall"
            (fe, ts) <- telescope $ Just $ Wildcard SType
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
    mkIf b t f = SBuiltin "primIfThenElse" `SAppV` b `SAppV` t `SAppV` f

    mkPi Hidden xs b = foldr (\a b -> SPi Hidden a $ up1 b) b $ map SCW $ getTTuple xs
    mkPi Visible a b = SPi Visible a $ up1 b

parseTermAnn = level parseTermOp $ \t -> SAnn t <$> parseType Nothing

parseTermOp = (notOp False <|> notExp) >>= calculatePrecs
  where
    notExp = (++) <$> ope <*> notOp True
    notOp x = (++) <$> try_ "expression" ((++) <$> ex parseTermApp <*> option [] ope) <*> notOp True
         <|> if x then option [] (try_ "lambda" $ ex parseTermLam) else mzero
    ope = pure . Left <$> addFixity (rhsOperator <|> appRange (flip SIName "'EqCTt" <$ reservedOp "~"))
    ex pr = pure . Right <$> setR pr

    calculatePrecs :: [Either SIName SExp] -> BodyParser SExp
    calculatePrecs = go where

        go (Right e: xs)         = waitOp False e [] xs
        go xs@(Left (sName -> "-"): _) = waitOp False (mkLit $ LInt 0) [] xs
        go (Left op: xs)         = Section . SLamV <$> waitExp True (sVar "leftSection" 0) [] op xs
        go _                     = error "impossible @ Parser 479"

        waitExp lsec e acc op (Right t: xs)  = waitOp lsec e ((op, if lsec then up 1 t else t): acc) xs
        waitExp lsec e acc op [] | lsec      = fail "two-sided section is not allowed"
                                 | otherwise = fmap (Section . SLamV) . calcPrec' e $ (op, sVar "rightSection" 0): map (second (up 1)) acc
        waitExp _ _ _ _ _                    = fail "two operator is not allowed next to each-other"

        waitOp lsec e acc (Left op: xs) = waitExp lsec e acc op xs
        waitOp lsec e acc []            = calcPrec' e acc
        waitOp lsec e acc _             = error "impossible @ Parser 488"

        calcPrec' e = postponedCheck id . calcPrec (\op x y -> SGlobal op `SAppV` x `SAppV` y) (fromJust . nameFixity) e . reverse

parseTermApp =
        AppsS <$> try_ "record" (SGlobal <$> upperCase <* symbol "{")
              <*> commaSep ((,) Visible <$ lowerCase{-TODO-} <* reservedOp "=" <*> setR parseTermLam)
              <*  symbol "}"
     <|> AppsS <$> setR parseTermSwiz <*> many (hiddenTerm (setR parseTermSwiz) $ setR parseTermSwiz)

parseTermSwiz = level parseTermProj $ \t ->
    mkSwizzling t <$> lexeme (try_ "swizzling" $ char '%' *> count' 1 4 (satisfy (`elem` ("xyzwrgba" :: String))))
  where
    mkSwizzling term = swizzcall . map (sc . synonym)
      where
        swizzcall []  = error "impossible: swizzling parsing returned empty pattern"
        swizzcall [x] = SBuiltin "swizzscalar" `SAppV` term `SAppV` x
        swizzcall xs  = SBuiltin "swizzvector" `SAppV` term `SAppV` foldl SAppV (SBuiltin $ "V" ++ show (length xs)) xs

        sc c = SBuiltin ['S', c]

        synonym 'r' = 'x'
        synonym 'g' = 'y'
        synonym 'b' = 'z'
        synonym 'a' = 'w'
        synonym c   = c

parseTermProj = level parseTermAtom $ \t ->
    try_ "projection" $ mkProjection t <$ char '.' <*> sepBy1 lowerCase (char '.')
  where
    mkProjection = foldl $ \exp field -> SBuiltin "project" `SAppV` litString field `SAppV` exp

parseTermAtom =
         mkLit <$> try_ "literal" parseLit
     <|> Wildcard (Wildcard SType) <$ reserved "_"
     <|> mkLets <$ reserved "let" <*> parseDefs <* reserved "in" <*> setR parseTermLam
     <|> SGlobal <$> lowerCase
     <|> SGlobal <$> upperCase_
     <|> braces (mkRecord <$> commaSep ((,) <$> lowerCase <* symbol ":" <*> setR parseTermLam))
     <|> char '\'' *> ppa switchNamespace
     <|> ppa id
  where
    ppa tick =
         brackets ( (setR parseTermLam >>= \e ->
                mkDotDot e <$ reservedOp ".." <*> setR parseTermLam
            <|> join (foldr (=<<) (pure $ BCons e BNil) <$ reservedOp "|" <*> commaSep (generator <|> letdecl <|> boolExpression))
            <|> mkList . tick <$> asks namespace <*> ((e:) <$> option [] (symbol "," *> commaSep1 (setR parseTermLam)))
            ) <|> mkList . tick <$> asks namespace <*> pure [])
     <|> parens (SGlobal <$> try_ "opname" (symbols <* lookAhead (symbol ")"))
             <|> mkTuple . tick <$> asks namespace <*> commaSep (setR parseTermLam))

    mkTuple _      [Section e] = e
    mkTuple ExpNS  [Parens e]  = HCons e HNil
    mkTuple TypeNS [Parens e]  = HList $ BCons e BNil
    mkTuple _      [x]         = Parens x
    mkTuple ExpNS  xs          = foldr HCons HNil xs
    mkTuple TypeNS xs          = HList $ foldr BCons BNil xs

    mkList TypeNS [x] = BList x
    mkList _      xs  = foldr BCons BNil xs

    -- Creates: RecordCons @[("x", _), ("y", _), ("z", _)] (1.0, 2.0, 3.0)))
    mkRecord (unzip -> (names, values))
        = SBuiltin "RecordCons" `SAppH` foldr BCons BNil (mkRecItem <$> names) `SAppV` foldr HCons HNil values

    mkRecItem l = SBuiltin "RecItem" `SAppV` litString l `SAppV` Wildcard SType

    mkDotDot e f = SBuiltin "fromTo" `SAppV` e `SAppV` f

    generator, letdecl, boolExpression :: BodyParser (SExp -> ErrorFinder SExp)
    generator = do
        (dbs, pat) <- try_ "generator" $ longPattern <* reservedOp "<-"
        checkPattern dbs
        exp <- setR parseTermLam
        return $ \e -> do
            cf <- runCheck $ compileGuardTree id id (Just $ SIName (sourceInfo pat) "") [(Visible, Wildcard SType)]
                           $ compilePatts [pat] (noGuards $ deBruijnify dbs e) `mappend` noGuards BNil
            return $ SBuiltin "concatMap" `SAppV` cf `SAppV` exp

    letdecl = (return .) . mkLets <$ reserved "let" <*> (runCheck . compileStmt' =<< valueDef)

    boolExpression = (\pred e -> return $ SBuiltin "primIfThenElse" `SAppV` pred `SAppV` e `SAppV` BNil) <$> setR parseTermLam


level pr f = pr >>= \t -> option t $ f t

litString (SIName si n) = SLit si $ LString n

mkLit n@LInt{} = SBuiltin "fromInt" `SAppV` sLit n
mkLit l = sLit l

-------------------------------------------------------------------------------- pattern parsing

setR p = appRange $ flip setSI <$> p

--parsePat... :: BodyParser ParPat
parsePatAnn = patType <$> setR parsePatOp <*> parseType (Just $ Wildcard SType)
  where
    patType p (Wildcard SType) = p
    patType p t = PatTypeSimp p t

parsePatOp = join $ calculatePatPrecs <$> setR parsePatApp <*> option [] (oper >>= p)
  where
    oper = addConsInfo $ addFixity colonSymbols
    p op = do (exp, op') <- try_ "pattern" $ (,) <$> setR parsePatApp <*> oper
              ((op, exp):) <$> p op'
       <|> pure . (,) op <$> setR parsePatAnn

    calculatePatPrecs e xs = postponedCheck fst $ calcPrec (\op x y -> PConSimp op [x, y]) (fromJust . nameFixity . fst) e xs

parsePatApp =
         PConSimp <$> addConsInfo upperCase_ <*> many (setR parsePatAt)
     <|> parsePatAt

parsePatAt = concatParPats <$> sepBy1 (setR parsePatAtom) (reservedOp "@")
  where
    concatParPats ps = ParPat $ concat [p | ParPat p <- ps]

parsePatAtom =
         mkLit <$> asks namespace <*> try_ "literal" parseLit
     <|> flip PConSimp [] <$> addConsInfo upperCase_
     <|> mkPVar <$> patVar
     <|> char '\'' *> ppa switchNamespace
     <|> ppa id
  where
    mkLit TypeNS (LInt n) = unfoldNat cZero cSucc n        -- todo: elim this alternative
    mkLit _ n@LInt{} = litP (SBuiltin "fromInt" `SAppV` sLit n)
    mkLit _ n = litP (sLit n)

    ppa tick =
         brackets (mkListPat . tick <$> asks namespace <*> patlist)
     <|> parens   (parseViewPat <|> mkTupPat  . tick <$> asks namespace <*> patlist)

    mkListPat TypeNS [p] = cList p
    mkListPat ns ps      = foldr cCons cNil ps

    --mkTupPat :: [Pat] -> Pat
    mkTupPat TypeNS [PParens x] = mkTTup [x]
    mkTupPat ns     [PParens x] = mkTup [x]
    mkTupPat _      [x]         = PParens x
    mkTupPat TypeNS ps          = mkTTup ps
    mkTupPat ns     ps          = mkTup ps

    mkTTup = cHList . mkListPat ExpNS
    mkTup ps = foldr cHCons cHNil ps

    parseViewPat = ViewPatSimp <$> try_ "view pattern" (setR parseTermOp <* reservedOp "->") <*> setR parsePatAnn

    mkPVar (SIName si "") = PWildcard si
    mkPVar s = PVarSimp s

    litP = flip ViewPatSimp cTrue . SAppV (SGlobal $ SIName_ mempty (Just $ Infix 4) "==")

    patlist = commaSep $ setR parsePatAnn

longPattern = setR parsePatAnn <&> (reverse . getPVars &&& id)

telescopePat = do
    (a, b) <- fmap (reverse . foldMap (getPVars . snd) &&& id) $ many $ uncurry f <$> hiddenTerm (setR parsePatAtom) (setR parsePatAtom)
    checkPattern a
    return (a, b)
  where
    f h (PParens p) = second PParens $ f h p
    f h (PatTypeSimp p t) = ((h, t), p)
    f h p = ((h, Wildcard SType), p)

checkPattern :: [SIName] -> BodyParser ()
checkPattern ns = tell $ pure $ Left $ 
   case [reverse ns' | ns'@(_:_:_) <- group . sort . filter (not . null . sName) $ ns] of
    [] -> Nothing
    xs -> Just $ MultiplePatternVars xs

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
            let mkConTy mk (nps', ts') =
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
                        runCheck $ fmap Stmt <$> compileStmt (compileGuardTrees id . const Nothing) [TypeAnn x $ UncurryS ts t] cs
             <|> pure <$ reserved "instance" <*> funAltDef Nothing upperCase
             <|> do x <- upperCase
                    (nps, ts) <- telescope $ Just (Wildcard SType)
                    rhs <- deBruijnify nps <$ reservedOp "=" <*> setR parseTermLam
                    runCheck $ fmap Stmt <$> compileStmt (compileGuardTrees id . const Nothing)
                        [{-TypeAnn x $ UncurryS ts $ SType-}{-todo-}]
                        [funAlt' x ts (map PVarSimp $ reverse nps) $ noGuards rhs]
 <|> do try_ "typed ident" $ map (uncurry TypeAnn) <$> typedIds addForalls' []
 <|> fmap . (Stmt .) . flip PrecDef <$> parseFixity <*> commaSep1 rhsOperator
 <|> pure <$> funAltDef (Just lhsOperator) varId
 <|> valueDef
  where
    telescopeDataFields :: BodyParser ([SIName], [(Visibility, SExp)]) 
    telescopeDataFields = mkTelescope <$> commaSep ((,) Visible <$> ((,) <$> lowerCase <*> parseType Nothing))

    mkData x ts t cs
        = (Stmt (Data x ts t (second snd <$> cs)):) . concat <$> traverse mkProj (nub $ concat [fs | (_, (Just fs, _)) <- cs])
      where
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
    mkGuards <$> some (reservedOp "|" *> guard) <*> option [] (reserved "where" *> parseDefs)
  <|> do
    reservedOp tok
    rhs <- setR parseTermLam
    f <- option id $ mkLets <$ reserved "where" <*> parseDefs
    noGuards <$> trackSI (pure $ f rhs)
  where
    guard = do
        (nps, ps) <- mkTelescope' <$> commaSep1 guardPiece <* reservedOp tok
        e <- trackSI $ setR parseTermLam
        return (ps, deBruijnify nps e)

    guardPiece = getVars <$> option cTrue (try_ "pattern guard" $ setR parsePatOp <* reservedOp "<-") <*> setR parseTermOp
      where
        getVars p e = (reverse $ getPVars p, (p, e))

    mkGuards gs wh = mkLets_ lLet wh $ mconcat [foldr (uncurry guardNode') (noGuards e) ge | (ge, e) <- gs]

parseDefs = identation True parseDef >>= runCheck . compileStmt' . concat

funAltDef parseOpName parseName = do
    (n, (fee, tss)) <-
        case parseOpName of
          Nothing -> mzero
          Just opName -> try_ "operator definition" $ do
            (e', a1) <- longPattern
            n <- opName
            (e'', a2) <- longPattern
            lookAhead $ reservedOp "=" <|> reservedOp "|"
            let fee = e'' <> e'
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
        exps <- optional (parens $ commaSep parseExport)
        reserved "where"
        return (modn, exps)
    let mkIDef _ n i h _ = (n, f i h)
          where
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
        , definitions   = \ge -> runParse (parseDefs <* eof) (env { desugarInfo = ge }, st)
        }

parseLC :: FileInfo -> Either ParseError Module
parseLC fi
    = fmap fst $ runParse parseModule $ parseState fi ()

runDefParser :: (MonadFix m, MonadError LCParseError m) => DesugarInfo -> DefParser -> m ([Stmt], [ParseWarning], DesugarInfo)
runDefParser ds_ dp = do

    (defs, dns, ds) <- mfix $ \ ~(_, _, ds) -> do
        let x = dp (ds <> ds_)
        (defs, dns) <- either (throwError . ParseError) return x
        return (defs, dns, mkDesugarInfo defs)

    mapM_ throwError [x | Left (Just x) <- dns]

    let ism = Set.fromList [is | Right (Reachable is) <- dns]
        f (TrackedCode is) | is `Set.notMember` ism = Just $ Unreachable is
        f (Uncovered' si x) | not $ null $ filter (not . null . fst) x = Just $ Uncovered si x
        f _ = Nothing

    return (concatMap desugarMutual $ sortDefs defs, catMaybes [f w | Right w <- dns], ds)

