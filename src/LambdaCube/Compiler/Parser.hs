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
--import Debug.Trace

import LambdaCube.Compiler.Utils
import LambdaCube.Compiler.DeBruijn
import LambdaCube.Compiler.Pretty hiding (Doc, braces, parens)
import LambdaCube.Compiler.Lexer
import LambdaCube.Compiler.DesugaredSource
import LambdaCube.Compiler.Patterns
import LambdaCube.Compiler.Statements

-------------------------------------------------------------------------------- utils

try = try_

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
    | Uncovered SI [PatList]

instance NFData ParseWarning
 where
    rnf = \case
        Unreachable r -> rnf r
        Uncovered si r -> rnf si -- TODO --rnf r

instance Show LCParseError where
    show = \case
        MultiplePatternVars xs -> unlines $ "multiple pattern vars:":
            concat [(sName (head ns) ++ " is defined at"): map showSI ns | ns <- xs]
        OperatorMismatch op op' -> "Operator precedences don't match:\n" ++ show (getFixity op) ++ " at " ++ showSI op ++ "\n" ++ show (getFixity op') ++ " at " ++ showSI op'
        UndefinedConstructor n -> "Constructor " ++ show n ++ " is not defined at " ++ showSI n
        ParseError p -> show p

instance Show ParseWarning where
    show = \case
        Unreachable si -> "Source code is not reachable: " ++ show (showRange si)
        Uncovered si pss -> "Uncovered pattern(s) at " ++ showSI si ++ "\nMissing case(s):\n" ++
            unlines ["  " ++ unwords (map ppShow ps) ++
                     " | " +++ intercalate ", " [ppShow p ++ " <- " ++ ppShow e | (p, e) <- gs]
                    | (ps, gs) <- pss]
      where
        s +++ "" = ""
        s +++ s' = s ++ s'

trackSI p = do
    x <- p
    tell $ Right . TrackedCode <$> maybeToList (getRange $ sourceInfo x)
    return x

-- TODO: filter this in module imports
data DesugarInfo = DesugarInfo
    { fixityMap  :: Map.Map SName Fixity
    , consMap    :: Map.Map SName ConsInfo
    , definedSet :: DefinedSet
    }

instance Monoid DesugarInfo where
    mempty = DesugarInfo mempty mempty mempty
    DesugarInfo a b c `mappend` DesugarInfo a' b' c' = DesugarInfo (a <> a') (b <> b') (c <> c')

addFixity :: BodyParser SIName -> BodyParser SIName
addFixity p = f <$> asks (fixityMap . desugarInfo) <*> p
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

mkDesugarInfo :: [Stmt] -> DesugarInfo
mkDesugarInfo ss = DesugarInfo
    { fixityMap = Map.fromList $ ("'EqCTt", Fixity Infix (-1)): [(sName s, f) | PrecDef s f <- ss]
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

-------------------------------------------------------------------------------- precedences -- TODO: remove

data Prec
    = PrecAtom      --  ( _ )  ...                                          -- 20
    | PrecAtom'                                                             
    | PrecAt        --  _@_                 {assoc}  -- in patterns         -- 13
    | PrecProj      --  _ ._                {left}                          -- 12
    | PrecSwiz      --  _%_                 {left}                          -- 11
    | PrecApp       --  _ _                 {left}                          -- 10
    | PrecOp                                                                -- 0 - 9
    | PrecArr       --  _ -> _              {right}                         -- -1
    | PrecEq        --  _ ~ _                                               -- -2
    | PrecAnn       --  _ :: _              {right}                         -- -3
    | PrecLet       --  _ := _                                              -- -4
    | PrecLam       --  \ _ -> _            {right} {accum}                 -- -10
                    --  _ , _               {right}                         -- -20
    deriving (Eq, Ord)

-------------------------------------------------------------------------------- expression parsing

parseType mb = maybe id option mb (reservedOp "::" *> typeNS (parseTerm PrecLam))
typedIds f ds mb = (\ns t -> (,) <$> ns <*> pure t) <$> commaSep1 upperLower <*> (deBruijnify (ds :: [SIName]) <$> f (parseType mb))

hiddenTerm p q = (,) Hidden <$ reservedOp "@" <*> typeNS p  <|>  (,) Visible <$> q

telescope mb = fmap mkTelescope $ many $ hiddenTerm
    (typedId <|> maybe empty (tvar . pure) mb)
    (try "::" typedId <|> maybe ((,) (SIName mempty "") <$> typeNS (parseTerm PrecAtom)) (tvar . pure) mb)
  where
    tvar x = (,) <$> patVar <*> x
    typedId = parens $ tvar $ parseType mb

mkTelescope (unzip -> (vs, ns)) = second (zip vs) $ mkTelescope' $ first (:[]) <$> ns

mkTelescope' = go []
  where
    go ns [] = (ns, [])
    go ns ((n, e): ts) = second (deBruijnify ns e:) $ go (n ++ ns) ts

parseTerm p = appRange $ flip setSI <$> parseTerm_ p

parseTerm_ :: Prec -> BodyParser SExp
parseTerm_ = \case
    PrecLam ->
         do level PrecAnn $ \t -> mkPi <$> (Visible <$ reservedOp "->" <|> Hidden <$ reservedOp "=>") <*> pure t <*> parseTerm PrecLam
     <|> mkIf <$ reserved "if" <*> parseTerm PrecLam <* reserved "then" <*> parseTerm PrecLam <* reserved "else" <*> parseTerm PrecLam
     <|> do reserved "forall"
            (fe, ts) <- telescope $ Just $ Wildcard SType
            f <- SPi . const Hidden <$ reservedOp "." <|> SPi . const Visible <$ reservedOp "->"
            t' <- deBruijnify fe <$> parseTerm PrecLam
            return $ foldr (uncurry f) t' ts
     <|> do expNS $ do
                (fe, ts) <- reservedOp "\\" *> telescopePat <* reservedOp "->"
                foldr (\e m -> runCheck . uncurry (patLam id) e =<< m) (deBruijnify fe <$> parseTerm PrecLam) ts
     <|> do join $ (runCheck .) . compileCase <$ reserved "case" <*> parseTerm PrecLam <* reserved "of" <*> do
                identation False $ do
                    (fe, p) <- longPattern
                    (,) p . deBruijnify fe <$> parseRHS "->"
    PrecAnn -> level PrecOp $ \t -> SAnn t <$> parseType Nothing
    PrecOp -> (notOp False <|> notExp) >>= calculatePrecs where
        notExp = (++) <$> ope <*> notOp True
        notOp x = (++) <$> try "expression" ((++) <$> ex PrecApp <*> option [] ope) <*> notOp True
             <|> if x then option [] (try "lambda" $ ex PrecLam) else mzero
        ope = pure . Left <$> addFixity (rhsOperator <|> appRange (flip SIName "'EqCTt" <$ reservedOp "~"))
        ex pr = pure . Right <$> parseTerm pr
    PrecApp ->
        AppsS <$> try "record" (SGlobal <$> upperCase <* symbol "{")
              <*> commaSep ((,) Visible <$ lowerCase{-TODO-} <* reservedOp "=" <*> parseTerm PrecLam)
              <*  symbol "}"
     <|> AppsS <$> parseTerm PrecSwiz <*> many (hiddenTerm (parseTerm PrecSwiz) $ parseTerm PrecSwiz)
    PrecSwiz -> level PrecProj $ \t ->
        mkSwizzling t <$> lexeme (try "swizzling" $ char '%' *> count' 1 4 (satisfy (`elem` ("xyzwrgba" :: String))))
    PrecProj -> level PrecAtom $ \t ->
        try "projection" $ mkProjection t <$ char '.' <*> sepBy1 lowerCase (char '.')
    PrecAtom ->
         mkLit <$> try "literal" parseLit
     <|> Wildcard (Wildcard SType) <$ reserved "_"
     <|> mkLets <$ reserved "let" <*> parseDefs <* reserved "in" <*> parseTerm PrecLam
     <|> SGlobal <$> lowerCase
     <|> SGlobal <$> upperCase_
     <|> braces (mkRecord <$> commaSep ((,) <$> lowerCase <* symbol ":" <*> parseTerm PrecLam))
     <|> char '\'' *> ppa switchNamespace
     <|> ppa id
  where
    level pr f = parseTerm_ pr >>= \t -> option t $ f t

    ppa tick =
         brackets ( (parseTerm PrecLam >>= \e ->
                mkDotDot e <$ reservedOp ".." <*> parseTerm PrecLam
            <|> join (foldr (=<<) (pure $ BCons e BNil) <$ reservedOp "|" <*> commaSep (generator <|> letdecl <|> boolExpression))
            <|> mkList . tick <$> asks namespace <*> ((e:) <$> option [] (symbol "," *> commaSep1 (parseTerm PrecLam)))
            ) <|> mkList . tick <$> asks namespace <*> pure [])
     <|> parens (SGlobal <$> try "opname" (symbols <* lookAhead (symbol ")")) <|> mkTuple . tick <$> asks namespace <*> commaSep (parseTerm PrecLam))

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

    mkProjection = foldl $ \exp field -> SBuiltin "project" `SAppV` litString field `SAppV` exp

    -- Creates: RecordCons @[("x", _), ("y", _), ("z", _)] (1.0, 2.0, 3.0)))
    mkRecord (unzip -> (names, values))
        = SBuiltin "RecordCons" `SAppH` foldr BCons BNil (mkRecItem <$> names) `SAppV` foldr HCons HNil values

    mkRecItem l = SBuiltin "RecItem" `SAppV` litString l `SAppV` Wildcard SType

    litString (SIName si n) = SLit si $ LString n

    mkTuple _      [Section e] = e
    mkTuple ExpNS  [Parens e]  = HCons e HNil
    mkTuple TypeNS [Parens e]  = HList $ BCons e BNil
    mkTuple _      [x]         = Parens x
    mkTuple ExpNS  xs          = foldr HCons HNil xs
    mkTuple TypeNS xs          = HList $ foldr BCons BNil xs

    mkList TypeNS [x] = BList x
    mkList _      xs  = foldr BCons BNil xs

    mkLit n@LInt{} = SBuiltin "fromInt" `SAppV` sLit n
    mkLit l = sLit l

    mkIf b t f = SBuiltin "primIfThenElse" `SAppV` b `SAppV` t `SAppV` f

    mkDotDot e f = SBuiltin "fromTo" `SAppV` e `SAppV` f

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

        calcPrec' e = postponedCheck id . calcPrec (\op x y -> SGlobal op `SAppV` x `SAppV` y) getFixity e . reverse

    generator, letdecl, boolExpression :: BodyParser (SExp -> ErrorFinder SExp)
    generator = do
        (dbs, pat) <- try "generator" $ longPattern <* reservedOp "<-"
        checkPattern dbs
        exp <- parseTerm PrecLam
        return $ \e -> do
            cf <- runCheck $ compileGuardTree id id (Just $ sourceInfo pat) [(Visible, Wildcard SType)] $ compilePatts [pat] (noGuards $ deBruijnify dbs e) `mappend` noGuards BNil
            return $ SBuiltin "concatMap" `SAppV` cf `SAppV` exp

    letdecl = (return .) . mkLets <$ reserved "let" <*> (runCheck . compileStmt' =<< valueDef)

    boolExpression = (\pred e -> return $ SBuiltin "primIfThenElse" `SAppV` pred `SAppV` e `SAppV` BNil) <$> parseTerm PrecLam

    mkPi Hidden xs b = foldr (sNonDepPi Hidden) b $ getTTuple xs
    mkPi h a b = sNonDepPi h a b

    sNonDepPi h a b = SPi h a $ up1 b

-------------------------------------------------------------------------------- pattern parsing

parsePat p = appRange $ flip setSI <$> parsePat_ p

parsePat_ :: Prec -> BodyParser ParPat
parsePat_ = \case
    PrecAnn ->
        patType <$> parsePat PrecArr <*> parseType (Just $ Wildcard SType)
    PrecArr ->
        parsePat_ PrecOp
    PrecOp ->
        join $ calculatePatPrecs <$> parsePat PrecApp <*> option [] (oper >>= p)
      where
        oper = addConsInfo $ addFixity colonSymbols
        p op = do (exp, op') <- try "pattern" $ (,) <$> parsePat PrecApp <*> oper
                  ((op, exp):) <$> p op'
           <|> pure . (,) op <$> parsePat PrecAnn
    PrecApp ->
         PConSimp <$> addConsInfo upperCase_ <*> many (parsePat PrecAt)
     <|> parsePat_ PrecAt
    PrecAt -> concatParPats <$> sepBy1 (parsePat PrecAtom) (reservedOp "@")
    PrecAtom ->
         mkLit <$> asks namespace <*> try "literal" parseLit
     <|> flip PConSimp [] <$> addConsInfo upperCase_
     <|> mkPVar <$> patVar
     <|> char '\'' *> ppa switchNamespace
     <|> ppa id
  where
    ppa tick =
         brackets (mkListPat . tick <$> asks namespace <*> patlist)
     <|> parens   (parseViewPat <|> mkTupPat  . tick <$> asks namespace <*> patlist)

    parseViewPat = ViewPatSimp <$> try "view pattern" (parseTerm PrecOp <* reservedOp "->") <*> parsePat_ PrecAnn

    mkPVar (SIName si "") = PWildcard si
    mkPVar s = PVarSimp s

    concatParPats ps = ParPat $ concat [p | ParPat p <- ps]

    litP = flip ViewPatSimp cTrue . SAppV (SBuiltin "==")

    mkLit TypeNS (LInt n) = unfoldNat cZero cSucc n        -- todo: elim this alternative
    mkLit _ n@LInt{} = litP (SBuiltin "fromInt" `SAppV` sLit n)
    mkLit _ n = litP (sLit n)

    patlist = commaSep $ parsePat PrecAnn

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

    patType p (Wildcard SType) = p
    patType p t = PatTypeSimp p t

    calculatePatPrecs e xs = postponedCheck fst $ calcPrec (\op x y -> PConSimp op [x, y]) (getFixity . fst) e xs

longPattern = parsePat PrecAnn <&> (reverse . getPVars &&& id)

telescopePat = do
    (a, b) <- fmap (reverse . foldMap (getPVars . snd) &&& id) $ many $ uncurry f <$> hiddenTerm (parsePat PrecAtom) (parsePat PrecAtom)
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
                 (,) True . map (second $ (,) Nothing) . concat <$ reserved "where" <*> identation True (typedIds id npsd Nothing)
             <|> (,) False <$ reservedOp "=" <*>
                      sepBy1 ((,) <$> upperCase
                                  <*> (mkConTy True <$> braces telescopeDataFields <|> mkConTy False <$> telescope Nothing)
                             )
                             (reservedOp "|")
            mkData x ts t $ second (second $ if af then adf else id) <$> cs
 <|> do reserved "class" *> do
            x <- typeNS upperCase
            (nps, ts) <- telescope (Just SType)
            cs <- option [] $ concat <$ reserved "where" <*> identation True (typedIds id nps Nothing)
            return $ pure $ Class x (map snd ts) cs
 <|> do reserved "instance" *> do
          typeNS $ do
            constraints <- option [] $ try "constraint" $ getTTuple <$> parseTerm PrecOp <* reservedOp "=>"
            x <- upperCase
            (nps, args) <- telescopePat
            cs <- expNS $ option [] $ reserved "where" *> identation False (deBruijnify nps <$> funAltDef (Just lhsOperator) varId)
            pure . Instance x ({-todo-}map snd args) (deBruijnify (nps <> [x]) <$> constraints) <$> runCheck (compileStmt' cs)
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
                    rhs <- deBruijnify nps <$ reservedOp "=" <*> parseTerm PrecLam
                    runCheck $ fmap Stmt <$> compileStmt (compileGuardTrees id . const Nothing)
                        [{-TypeAnn x $ UncurryS ts $ SType-}{-todo-}]
                        [funAlt' x ts (map PVarSimp $ reverse nps) $ noGuards rhs]
 <|> do try "typed ident" $ map (uncurry TypeAnn) <$> typedIds addForalls' [] Nothing
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
    rhs <- parseTerm PrecLam
    f <- option id $ mkLets <$ reserved "where" <*> parseDefs
    noGuards <$> trackSI (pure $ f rhs)
  where
    guard = do
        (nps, ps) <- mkTelescope' <$> commaSep1 guardPiece <* reservedOp tok
        e <- trackSI $ parseTerm PrecLam
        return (ps, deBruijnify nps e)

    guardPiece = getVars <$> option cTrue (try "pattern guard" $ parsePat PrecOp <* reservedOp "<-") <*> parseTerm PrecOp
      where
        getVars p e = (reverse $ getPVars p, (p, e))

    mkGuards gs wh = mkLets_ lLet wh $ mconcat [foldr (uncurry guardNode') (noGuards e) ge | (ge, e) <- gs]

parseDefs = identation True parseDef >>= runCheck . compileStmt' . concat

funAltDef parseOpName parseName = do
    (n, (fee, tss)) <-
        case parseOpName of
          Nothing -> mzero
          Just opName -> try "operator definition" $ do
            (e', a1) <- longPattern
            n <- opName
            (e'', a2) <- longPattern
            lookAhead $ reservedOp "=" <|> reservedOp "|"
            let fee = e'' <> e'
            checkPattern fee
            return (n, (fee, (,) (Visible, Wildcard SType) <$> [a1, deBruijnify e' a2]))
      <|> do try "lhs" $ (,) <$> parseName <*> telescopePat <* lookAhead (reservedOp "=" <|> reservedOp "|")
    funAlt n tss . deBruijnify fee <$> parseRHS "="

valueDef :: BodyParser [PreStmt]
valueDef = do
    (dns, p) <- try "pattern" $ longPattern <* reservedOp "="
    checkPattern dns
    desugarValueDef p =<< parseTerm PrecLam
  where
    desugarValueDef p e = runCheck $ sequence
        $ pure (FunAlt n [] $ noGuards e)
        : [ FunAlt x [] . noGuards <$> compileCase (SGlobal n) [(p, noGuards $ SVar x i)]
          | (i, x) <- zip [0..] dns
          ]
      where
        dns = reverse $ getPVars p
        n = mangleNames dns

mangleNames xs = SIName (foldMap sourceInfo xs) $ "_" ++ intercalate "_" (sName <$> xs)

-------------------------------------------------------------------------------- modules

parseExport :: HeaderParser Export
parseExport =
        ExportModule <$ reserved "module" <*> moduleName
    <|> ExportId <$> varId

importlist = parens $ commaSep upperLower

parseExtensions :: HeaderParser [Extension]
parseExtensions
    = try "pragma" (symbol "{-#") *> symbol "LANGUAGE" *> commaSep (lexeme ext) <* symbolWithoutSpace "#-}" <* simpleSpace
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

    return (sortDefs defs, catMaybes [f w | Right w <- dns], ds)

