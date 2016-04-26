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
    ( SData(..)
    , NameDB, caseName, pattern MatchName
    , sourceInfo, SI(..), debugSI, FileInfo(..), ParseWarning(..)
    , Module(..), Visibility(..), Binder(..), SExp'(..), Extension(..), Extensions
    , pattern SVar, pattern SType, pattern Wildcard, pattern SAppV, pattern SLamV, pattern SAnn
    , pattern SBuiltin, pattern SPi, pattern Primitive, pattern SRHS, pattern SLam, pattern Parens
    , pattern TyType, pattern SLet, sVar
    , isPi, iterateN
    , parseLC, runDefParser
    , pattern UncurryS, pattern AppsS, downToS, addForalls
    , Up (..), up1, up
    , Doc, shLam, shApp, shLet, shLet_, shAtom, shAnn, shVar, epar, showDoc, showDoc_, sExpDoc, shCstr, shTuple
    , trSExp', usedS, deBruijnify, mapS
    , Stmt (..), Export (..), ImportItems (..)
    , DesugarInfo
    ) where

import Data.Monoid
import Data.Maybe
import Data.List
import Data.Char
import Data.String
import Data.Function
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMap as IM
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Arrow hiding ((<+>))
import Control.Applicative
import Control.DeepSeq
import Debug.Trace

import LambdaCube.Compiler.Utils

import qualified LambdaCube.Compiler.Pretty as Parser
import LambdaCube.Compiler.Pretty hiding (Doc, braces, parens)
import LambdaCube.Compiler.Lexer
import LambdaCube.Compiler.DesugaredSource

-------------------------------------------------------------------------------- utils

try = try_

-------------------------------------------------------------------------------- parser type

type BodyParser = Parse DesugarInfo PostponedCheck

type PostponedCheck = Either (Maybe LCParseError) ParseCheck

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

data ParseCheck
    = TrackedCode Range
    | Reachable Range
    | Uncovered' SI [PatList]

type PatList = ([ParPat_ ()], [(ParPat_ (), SExp)])

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

type DesugarInfo = (FixityMap, ConsMap)

type ConsMap = Map.Map SName{-constructor name-} ConsInfo

type ConsInfo = Either ((SName{-case eliminator name-}, Int{-num of indices-}), [(SIName, Int)]{-constructors with arities-})
                       Int{-arity-}

addFixity :: BodyParser SIName -> BodyParser SIName
addFixity p = f <$> asks (fst . desugarInfo) <*> p
  where
    f fm sn@(SIName_ si _ n) = SIName_ si (Map.lookup n fm) n

-------------------------------------------------------------------------------- expression parsing

parseType mb = maybe id option mb (reservedOp "::" *> typeNS (parseTerm PrecLam))
typedIds ds mb = (\ns t -> (,) <$> ns <*> pure t) <$> commaSep1 upperLower <*> (deBruijnify ds <$> parseType mb)

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
                foldr (\e m -> uncurry (patLam id) e =<< m) (deBruijnify fe <$> parseTerm PrecLam) ts
     <|> do join $ compileCase <$ reserved "case" <*> parseTerm PrecLam <* reserved "of" <*> do
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
            cf <- compileGuardTree id id (Just $ sourceInfo pat) [(Visible, Wildcard SType)] $ compilePatts [pat] (noGuards $ deBruijnify dbs e) `mappend` noGuards BNil
            return $ SBuiltin "concatMap" `SAppV` cf `SAppV` exp

    letdecl = (return .) . mkLets <$ reserved "let" <*> (compileStmt' =<< valueDef)

    boolExpression = (\pred e -> return $ SBuiltin "primIfThenElse" `SAppV` pred `SAppV` e `SAppV` BNil) <$> parseTerm PrecLam

    mkPi Hidden xs b = foldr (sNonDepPi Hidden) b $ getTTuple xs
    mkPi h a b = sNonDepPi h a b

    sNonDepPi h a b = SPi h a $ up1 b

patLam :: (SExp -> SExp) -> (Visibility, SExp) -> ParPat -> SExp -> ErrorFinder SExp
patLam f vt p e = compileGuardTree f f (Just $ sourceInfo p) [vt] (compilePatts [p] $ noGuards e)

-------------------------------------------------------------------------------- pattern representation

type Pat = Pat_ ConsInfo

data Pat_ c
    = PVar SIName -- Int
    | PCon_ SI (SIName, c) [ParPat_ c]
    | ViewPat_ SI SExp (ParPat_ c)
    | PatType_ SI (ParPat_ c) SExp
  deriving Show

type ParPat = ParPat_ ConsInfo

-- parallel patterns like  v@(f -> [])@(Just x)
data ParPat_ c = ParPat_ SI [Pat_ c]
  deriving Show

pattern ParPat ps <- ParPat_ _ ps
  where ParPat ps =  ParPat_ (foldMap sourceInfo ps) ps

instance PShow (Pat_ a) where
    pShowPrec _ = showDoc_ . patDoc
instance PShow (ParPat_ a) where
    pShowPrec _ = showDoc_ . parPatDoc


pattern PWildcard si = ParPat_ si []
pattern PCon n pp <- PCon_ _ n pp
  where PCon n pp =  PCon_ (sourceInfo (fst n) <> sourceInfo pp) n pp
pattern ViewPat e pp <- ViewPat_ _ e pp
  where ViewPat e pp =  ViewPat_ (sourceInfo e <> sourceInfo pp) e pp
pattern PatType pp e <- PatType_ _ pp e
  where PatType pp e =  PatType_ (sourceInfo e <> sourceInfo pp) pp e
--pattern SimpPats ps <- (traverse simpleParPat -> Just ps)
--  where SimpPats ps =  ParPat . (:[]) <$> ps

--simpleParPat (ParPat [p]) = Just p
--simpleParPat _ = Nothing

pattern PVarSimp    n    = ParPat [PVar    n]
pattern PConSimp    n ps = ParPat [PCon    n ps]
--pattern PConSimp    n ps = PCon    n (SimpPats ps)
pattern ViewPatSimp e p  = ParPat [ViewPat e p]
pattern PatTypeSimp p t  = ParPat [PatType p t]

pBuiltin n ci ps =  PConSimp (f n, left (second $ map $ first f) ci) ps
  where
    f n = SIName (debugSI $ "pattern_" ++ n) n

cTrue = pBuiltin "True" (Left ((CaseName "'Bool", 0), [("False", 0), ("True", 0)])) []
cZero = pBuiltin "Zero" (Left ((CaseName "'Nat", 0), [("Zero", 0), ("Succ", 1)])) []
cNil  = pBuiltin "Nil"  (Left ((CaseName "'List", 0), [("Nil", 0), ("Cons", 2)])) []
cHNil = pBuiltin "HNil" (Left (("hlistNilCase", -1), [("HNil", 0)])) []
cList  a = pBuiltin "'List" (Right 1) [a]
cHList a = pBuiltin "'HList" (Right 1) [a]
cSucc  a = pBuiltin "Succ" (Left ((CaseName "'Nat", 0), [("Zero", 0), ("Succ", 1)])) [a]
cCons  a b = pBuiltin "Cons" (Left ((CaseName "'List", 0), [("Nil", 0), ("Cons", 2)])) [a, b]
cHCons a b = pBuiltin "HCons" (Left (("hlistConsCase", -1), [("HCons", 2)])) [a, b]

pattern PParens p = ViewPatSimp (SBuiltin "parens") p

mapP :: (Int -> SExp -> SExp) -> Int -> Pat -> Pat
mapP f i = \case
    PVar n -> PVar n
    PCon_ si n ps -> PCon_ si n (upPats (mapPP f) i ps)
    ViewPat_ si e p -> ViewPat_ si (f i e) (mapPP f i p)
    PatType_ si p t -> PatType_ si (mapPP f i p) (f i t)

mapPP f i = \case
    ParPat_ si ps -> ParPat_ si $ upPats (mapP f) i ps

upPats g k [] = []
upPats g k (p: ps) = g k p: upPats g (k + patVars p) ps

instance Rearrange Pat where
    rearrange k f = mapP (`rearrange` f) k

instance Rearrange ParPat where
    rearrange k f = mapPP (`rearrange` f) k

instance DeBruijnify ParPat where
    deBruijnify_ l ns = mapPP (`deBruijnify_` ns) l

-- pattern variables
class PatVars a where getPVars :: a -> [SIName]

instance PatVars Pat
  where
    getPVars = \case
        PVar n -> [n]
        PCon _ ps -> foldMap getPVars ps
        ViewPat e p -> getPVars p
        PatType p t -> getPVars p

instance PatVars ParPat where getPVars (ParPat ps) = foldMap getPVars ps

instance PatVars a => PatVars [a] where getPVars = foldMap getPVars

-- number of pattern variables
patVars :: PatVars a => a -> Int
patVars = length . getPVars

instance SourceInfo (ParPat_ c) where
    sourceInfo (ParPat_ si _) = si

instance SetSourceInfo (ParPat_ c) where
    setSI si (ParPat_ _ ps) = ParPat_ si ps

instance SourceInfo (Pat_ c) where
    sourceInfo = \case
        PVar sn         -> sourceInfo sn
        PCon_ si _ _    -> si
        ViewPat_ si _ _ -> si
        PatType_ si _ _ -> si

instance SetSourceInfo (Pat_ c) where
    setSI si = \case
        PVar sn         -> PVar $ setSI si sn
        PCon_ _  a b    -> PCon_ si a b
        ViewPat_ _  a b -> ViewPat_ si a b
        PatType_ _  a b -> PatType_ si a b

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

-------------------------------------------------------------------------------- pattern match compilation

type ErrorFinder = BodyParser

-- pattern match compilation monad
type PMC = Writer ([CasePath], [Range])

type CasePath = [Maybe (SIName, Int, SExp)]

runPMC :: Maybe SI -> [(Visibility, SExp)] -> PMC a -> ErrorFinder a
runPMC si vt m = do
    tell $ Right . Reachable <$> rs
    case si of
        Nothing -> return ()
        Just si -> tell [Right $ Uncovered' si [mkPatt_ (zip [0 :: Int ..] $ reverse p) $ reverse [0.. length vt - 1] | Just p <- sequence <$> ps]]
    return a
  where
    (a, (ps, rs)) = runWriter m
    mkPatt_ ps_ i_ = (ps, mkGuards 0 ps_)
      where
        (mconcat -> qs, ps) = unzip $ map (mkPatt 0 ps_) i_

        mkGuards k [] = []
        mkGuards k ((q, (cn, n, e)): ps) = [(PConSimp (cn, ()) $ replicate n $ PWildcard mempty, e) | q `Set.notMember` qs] ++ mkGuards (k + n) ps

        mkPatt k ((q, (cn, n, SVar _ j)): ps) i | j == (i + k) = (Set.singleton q <>) . mconcat *** PConSimp (cn, ()) $ unzip [mkPatt (k + n) ps l | l <- [n-1, n-2..0]]
        mkPatt k ((q, (cn, n, _)): ps) i = mkPatt (k + n) ps i
        mkPatt k [] i = (mempty, PWildcard mempty)
        mkPatt k ps' i = error $ "mkPatt " ++ show i_ ++ ":  " ++ maybe "" showSI si ++ "\n" ++ show ps' ++ "\n" ++ show ps_

data Lets a
    = LLet SIName SExp (Lets a)
    | LTypeAnn SExp (Lets a)        -- TODO: eliminate if not used
    | In a
  deriving Show

lLet sn (SVar sn' i) l = rSubst 0 i l
lLet sn e l = LLet sn e l

foldLets f = \case
    In e -> f e
    LLet sn e x -> foldLets f x
    LTypeAnn e x -> foldLets f x

mapLets f h l = \case
    In e -> In $ h l e
    LLet sn e x -> LLet sn (f l e) $ mapLets f h (l+1) x
    LTypeAnn e x -> LTypeAnn (f l e) $ mapLets f h l x

instance Rearrange a => Rearrange (Lets a) where
    rearrange l f = mapLets (`rearrange` f) (`rearrange` f) l

instance DeBruijnify a => DeBruijnify (Lets a) where
    deBruijnify_ l ns = mapLets (`deBruijnify_` ns) (`deBruijnify_` ns) l

data GuardTree
    = GuardNode SExp (SIName, ConsInfo) [SIName] GuardTrees GuardTrees
    | GTSuccess SExp
    | GTFailure
  deriving Show

instance DeBruijnify GuardTree where
    deBruijnify_ l ns = mapGT (`deBruijnify_` ns) (`deBruijnify_` ns) l

type GuardTrees = Lets GuardTree

instance Monoid GuardTrees where
    mempty = In GTFailure
    LLet sn e x `mappend` y = LLet sn e $ x `mappend` rUp 1 0 y
    LTypeAnn t x `mappend` y = LTypeAnn t $ x `mappend` y
    In (GuardNode e n ps t ts) `mappend` y = In $ GuardNode e n ps t (ts `mappend` y)
    In GTFailure `mappend` y = y
    x@(In GTSuccess{}) `mappend` _ = x

mapGT :: (Int -> ParPat -> ParPat) -> (Int -> SExp -> SExp) -> Int -> GuardTree -> GuardTree
mapGT f h k = \case
    GuardNode e c pps gt el -> GuardNode (h k e) c pps (mapGTs f h (k + length pps) gt) (mapGTs f h k el)
    GTSuccess e -> GTSuccess $ h k e
    GTFailure -> GTFailure

mapGTs f h = mapLets h (mapGT f h)
{-
foldGT f = \case
    GuardNode e c pps gt el -> GuardNode (h k e) c pps (mapGTs f h (k + length pps) gt) (mapGTs f h k el)
    GTSuccess e -> f e
    GTFailure -> mempty
-}
instance Rearrange GuardTree where
    rearrange l f = mapGT (`rearrange` f) (`rearrange` f) l

pattern Otherwise = SBuiltin "otherwise"

guardNode :: Pat -> SExp -> GuardTrees -> GuardTrees
guardNode (PCon (sName -> "True", _) []) Otherwise gt = gt
guardNode (PCon (sName -> "False", _) []) Otherwise gt = In GTFailure
guardNode (PVar sn) e gt = lLet sn e gt
guardNode (ViewPat f p) e gt = guardNode' p (f `SAppV` e) gt
guardNode (PatType p t) e gt = guardNode' p (SAnn e t) gt
guardNode (PCon sn ps) e gt = In $ GuardNode e sn (replicate n $ dummyName "gn") (buildNode guardNode' n ps [n-1, n-2..0] gt) mempty
  where
    n = length ps

guardNode' (PParens p) e gt = guardNode' p e gt
guardNode' (ParPat_ si ps) e gt = case ps of
    []  -> gt
    [p] -> guardNode p e gt
    ps  -> lLet (SIName si "gtc") e $ buildNode guardNode 1 ps [0..] gt

buildNode guardNode n ps is gt
    = foldr f (rUp n (patVars ps) gt) $ zip3 ps is $ scanl (+) 0 $ map patVars ps
  where
    f (p, i, d) = guardNode (rUp n d p) (sVar "gn" $ i + d)

compilePatts :: [ParPat] -> GuardTrees -> GuardTrees
compilePatts ps = buildNode guardNode' n ps [n-1, n-2..0]
  where
    n = length ps

addConsInfo p = join $ f <$> asks (snd . desugarInfo) <*> p
  where
    f adts s = do
        tell [Left $ either (Just . UndefinedConstructor) (const Nothing) x]
        return $ either (const $ error "impossible @ Parser 826") id x
      where
        x = case Map.lookup (sName s) adts of
            Nothing -> throwError s
            Just i -> return (s, i)

compileGuardTree :: (SExp -> SExp) -> (SExp -> SExp) -> Maybe SI -> [(Visibility, SExp)] -> GuardTrees -> ErrorFinder SExp
compileGuardTree ulend lend si vt = fmap (\e -> foldr (uncurry SLam) e vt) . runPMC si vt . guardTreeToCases []
  where
    guardTreeToCases :: CasePath -> GuardTrees -> PMC SExp
    guardTreeToCases path = \case
        LLet sn e g -> SLet sn e <$> guardTreeToCases (Nothing: path){-TODO-} g
        LTypeAnn t g -> SAnn <$> guardTreeToCases (Nothing: path){-TODO-} g <*> pure t
        In GTFailure -> do
            tell ([path], mempty)
            return $ ulend $ SBuiltin "undefined"
        In (GTSuccess e) -> do
            tell $ (,) mempty $ maybeToList $ getRange $ sourceInfo e
            --trace (ppShow $ sourceInfo e) $ 
            return $ lend e
        ts@(In (GuardNode f (s, cn) _ _ _)) -> case cn of
--            Nothing -> throwError sn
            Left ((casename, inum), cns) -> do
                cf <- sequence [ iterateN n SLamV <$> guardTreeToCases (Just (cn, n, f): path) (filterGuardTree (up n f) cn 0 n $ rUp n 0 ts)
                               | (cn, n) <- cns ]
                return $
                    foldl SAppV
                        (SGlobal (SIName mempty casename) `SAppV` iterateN (1 + inum) SLamV (Wildcard (Wildcard SType)))
                        cf
                    `SAppV` f
            Right n -> do
                g1 <- guardTreeToCases (Nothing: path){-TODO-} $ filterGuardTree (up n f) s 0 n $ rUp n 0 ts
                g2 <- guardTreeToCases (Nothing: path){-TODO-} (filterGuardTree' f s ts)
                return $ SGlobal (SIName mempty $ MatchName $ sName s)
                 `SAppV` SLamV (Wildcard SType)
                 `SAppV` iterateN n SLamV g1
                 `SAppV` f
                 `SAppV` g2

    filterGuardTree' :: SExp -> SIName{-constr.-} -> GuardTrees -> GuardTrees
    filterGuardTree' f s = \case
        LLet sn e gt -> LLet sn e $ filterGuardTree' (up 1 f) s gt
        LTypeAnn e gt -> LTypeAnn e $ filterGuardTree' f s gt
        In (GuardNode f' s' ps gs (filterGuardTree' f s -> el))
            | f /= f' || s /= fst s' -> In $ GuardNode f' s' ps (filterGuardTree' (up (length ps) f) s gs) el
            | otherwise -> el
        In x -> In x

    filterGuardTree :: SExp -> SIName{-constr.-} -> Int -> Int{-number of constr. params-} -> GuardTrees -> GuardTrees
    filterGuardTree f s k ns = \case
        LLet sn e gt -> LLet sn e $ filterGuardTree (up 1 f) s (k + 1) ns gt
        LTypeAnn e gt -> LTypeAnn e $ filterGuardTree f s k ns gt
        In (GuardNode f' s' ps gs (filterGuardTree f s k ns -> el))
            | f /= f'   -> In $ GuardNode f' s' ps (filterGuardTree (up su f) s (su + k) ns gs) el
            | s == fst s' -> filterGuardTree f s k ns $ foldr (rSubst 0) gs (replicate su $ k+ns-1) <> el
            | otherwise -> el
          where
            su = length ps
        In x -> In x

compileGuardTrees ulend si vt = compileGuardTree ulend SRHS si vt . mconcat

compileGuardTrees' si vt = fmap (foldr1 $ SAppV2 $ SBuiltin "parEval" `SAppV` Wildcard SType) . mapM (compileGuardTrees id Nothing vt . (:[]))

compileCase x cs
    = (`SAppV` x) <$> compileGuardTree id id (Just $ sourceInfo x) [(Visible, Wildcard SType)] (mconcat [compilePatts [p] e | (p, e) <- cs])


-------------------------------------------------------------------------------- declaration representation

-- eliminated during parsing
data PreStmt
    = Stmt Stmt
    | TypeAnn SIName SExp
    | TypeFamily SIName SExp{-type-}   -- type family declaration
    | FunAlt SIName [(Visibility, SExp)]{-TODO: remove-} GuardTrees
    | Class SIName [SExp]{-parameters-} [(SIName, SExp)]{-method names and types-}
    | Instance SIName [ParPat]{-parameter patterns-} [SExp]{-constraints-} [Stmt]{-method definitions-}
    deriving (Show)

instance DeBruijnify PreStmt where
    deBruijnify_ k v = \case
        FunAlt n ts gue -> FunAlt n (map (second $ deBruijnify_ k v) ts) $ deBruijnify_ k v gue
        x -> error $ "deBruijnify @ " ++ show x

-------------------------------------------------------------------------------- declaration parsing

parseDef :: BodyParser [PreStmt]
parseDef =
     do reserved "data" *> do
            x <- typeNS upperCase
            (npsd, ts) <- telescope (Just SType)
            t <- deBruijnify npsd <$> parseType (Just SType)
            let mkConTy mk (nps', ts') =
                    ( if mk then Just $ reverse nps' else Nothing
                    , deBruijnify npsd $ foldr (uncurry SPi) (foldl SAppV (SGlobal x) $ SGlobal <$> reverse npsd) ts'
                    )
            (af, cs) <- option (True, []) $
                 (,) True . map (second $ (,) Nothing) . concat <$ reserved "where" <*> identation True (typedIds npsd Nothing)
             <|> (,) False <$ reservedOp "=" <*>
                      sepBy1 ((,) <$> upperCase
                                  <*> (mkConTy True <$> braces telescopeDataFields <|> mkConTy False <$> telescope Nothing)
                             )
                             (reservedOp "|")
            mkData x ts t af cs
 <|> do reserved "class" *> do
            x <- typeNS upperCase
            (nps, ts) <- telescope (Just SType)
            cs <- option [] $ concat <$ reserved "where" <*> identation True (typedIds nps Nothing)
            return $ pure $ Class x (map snd ts) cs
 <|> do reserved "instance" *> do
          typeNS $ do
            constraints <- option [] $ try "constraint" $ getTTuple <$> parseTerm PrecOp <* reservedOp "=>"
            x <- upperCase
            (nps, args) <- telescopePat
            cs <- expNS $ option [] $ reserved "where" *> identation False (deBruijnify nps <$> funAltDef (Just lhsOperator) varId)
            pure . Instance x ({-todo-}map snd args) (deBruijnify (nps <> [x]) <$> constraints) <$> compileStmt' cs
 <|> do reserved "type" *> do
            typeNS $ do
                reserved "family" *> do
                    x <- upperCase
                    (nps, ts) <- telescope (Just SType)
                    t <- deBruijnify nps <$> parseType (Just SType)
                    option {-open type family-}[TypeFamily x $ UncurryS ts t] $ do
                        cs <- (reserved "where" >>) $ identation True $ funAltDef Nothing $ mfilter (== x) upperCase
                        -- closed type family desugared here
                        fmap Stmt <$> compileStmt (compileGuardTrees id . const Nothing) [TypeAnn x $ UncurryS ts t] cs
             <|> pure <$ reserved "instance" <*> funAltDef Nothing upperCase
             <|> do x <- upperCase
                    (nps, ts) <- telescope $ Just (Wildcard SType)
                    rhs <- deBruijnify nps <$ reservedOp "=" <*> parseTerm PrecLam
                    fmap Stmt <$> compileStmt (compileGuardTrees id . const Nothing)
                        [{-TypeAnn x $ UncurryS ts $ SType-}{-todo-}]
                        [funAlt' x ts (map PVarSimp $ reverse nps) $ noGuards rhs]
 <|> do try "typed ident" $ map (uncurry TypeAnn) <$> typedIds [] Nothing
 <|> fmap . (Stmt .) . flip PrecDef <$> parseFixity <*> commaSep1 rhsOperator
 <|> pure <$> funAltDef (Just lhsOperator) varId
 <|> valueDef
  where
    telescopeDataFields :: BodyParser ([SIName], [(Visibility, SExp)]) 
    telescopeDataFields = mkTelescope <$> commaSep ((,) Visible <$> ((,) <$> lowerCase <*> parseType Nothing))

    mkData x ts t af cs
        = (Stmt (Data x ts t af (second snd <$> cs)):) . concat <$> traverse mkProj (nub $ concat [fs | (_, (Just fs, _)) <- cs])
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

noGuards = In . GTSuccess

parseDefs = identation True parseDef >>= compileStmt' . concat

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
    desugarValueDef p e = sequence
        $ pure (FunAlt n [] $ noGuards e)
        : [ FunAlt x [] . noGuards <$> compileCase (SGlobal n) [(p, noGuards $ SVar x i)]
          | (i, x) <- zip [0..] dns
          ]
      where
        dns = reverse $ getPVars p
        n = mangleNames dns

mangleNames xs = SIName (foldMap sourceInfo xs) $ "_" ++ intercalate "_" (sName <$> xs)

mkLets :: [Stmt]{-where block-} -> SExp{-main expression-} -> SExp{-big let with lambdas; replaces global names with de bruijn indices-}
mkLets = mkLets_ SLet

mkLets_ mkLet = mkLets' . sortDefs where
    mkLets' [] e = e
    mkLets' (Let n mt x: ds) e
        = mkLet n (maybe id (flip SAnn . addForalls {-todo-}[] []) mt x') (deBruijnify [n] $ mkLets' ds e)
      where
        x' = if usedS n x then SBuiltin "primFix" `SAppV` SLamV (deBruijnify [n] x) else x
    mkLets' (PrecDef{}: ds) e = mkLets' ds e
    mkLets' (x: ds) e = error $ "mkLets: " ++ show x

addForalls :: Extensions -> [SIName] -> SExp -> SExp
addForalls exs defined x = foldl f x [v | v@(sName -> vh:_) <- reverse $ names x, v `notElem'` defined, isLower vh]
  where
    f e v = SPi Hidden (Wildcard SType) $ deBruijnify [v] e

--    notElem' s@('\'':s') m = notElem s m && notElem s' m      -- TODO
    notElem' s m = s `notElem` m

    names :: SExp -> [SIName]
    names = nub . foldName pure

{-
defined defs = ("'Type":) $ flip foldMap defs $ \case
    TypeAnn (_, x) _ -> [x]
    Let (_, x) _ _ _ _  -> [x]
    Data (_, x) _ _ _ cs -> x: map (snd . fst) cs
    Class (_, x) _ cs    -> x: map (snd . fst) cs
    TypeFamily (_, x) _ _ -> [x]
    x -> error $ unwords ["defined: Impossible", show x, "cann't be here"]
-}


------------------------------------------------------------------------

compileStmt' ds = fmap concat . sequence $ map (compileStmt (compileGuardTrees SRHS . Just) ds) $ groupBy h ds where
    h (FunAlt n _ _) (FunAlt m _ _) = m == n
    h _ _ = False

compileStmt :: (SI -> [(Visibility, SExp)] -> [GuardTrees] -> ErrorFinder SExp) -> [PreStmt] -> [PreStmt] -> ErrorFinder [Stmt]
compileStmt compilegt ds = \case
    [Instance{}] -> return []
    [Class n ps ms] -> do
        cd <- compileStmt' $
            [ TypeAnn n $ foldr (SPi Visible) SType ps ]
         ++ [ funAlt n (map noTA ps) $ noGuards $ foldr (SAppV2 $ SBuiltin "'T2") (SBuiltin "'Unit") cstrs | Instance n' ps cstrs _ <- ds, n == n' ]
         ++ [ funAlt n (replicate (length ps) (noTA $ PVarSimp $ dummyName "cst0")) $ noGuards $ SBuiltin "'Empty" `SAppV` sLit (LString $ "no instance of " ++ sName n ++ " on ???")]
        cds <- sequence
            [ compileStmt'
            $ TypeAnn m (UncurryS (map ((,) Hidden) ps) $ SPi Hidden (foldl SAppV (SGlobal n) $ downToS "a2" 0 $ length ps) $ up1 t)
            : as
            | (m, t) <- ms
--            , let ts = fst $ getParamsS $ up1 t
            , let as = [ funAlt m p $ noGuards {- -$ SLam Hidden (Wildcard SType) $ up1 -} $ SLet m' e $ sVar "cst" 0
                      | Instance n' i cstrs alts <- ds, n' == n
                      , Let m' ~Nothing e <- alts, m' == m
                      , let p = zip ((,) Hidden <$> ps) i ++ [((Hidden, Wildcard SType), PVarSimp $ dummyName "cst2")]
        --              , let ic = patVars i
                      ]
            ]
        return $ cd ++ concat cds
    [TypeAnn n t] -> return [Primitive n t | n `notElem` [n' | FunAlt n' _ _ <- ds]]
    tf@[TypeFamily n t] -> case [d | d@(FunAlt n' _ _) <- ds, n' == n] of
        [] -> return [Primitive n t]
        alts -> compileStmt compileGuardTrees' [TypeAnn n t] alts
    fs@(FunAlt n vs _: _) -> case map head $ group [length vs | FunAlt _ vs _ <- fs] of
        [num]
          | num == 0 && length fs > 1 -> fail $ "redefined " ++ sName n ++ " at " ++ ppShow (sourceInfo n)
          | n `elem` [n' | TypeFamily n' _ <- ds] -> return []
          | otherwise -> do
            cf <- compilegt (mconcat [sourceInfo n | FunAlt n _ _ <- fs]) vs [gt | FunAlt _ _ gt <- fs]
            return [Let n (listToMaybe [t | TypeAnn n' t <- ds, n' == n]) cf]
        _ -> fail $ "different number of arguments of " ++ sName n ++ " at " ++ ppShow (sourceInfo n)
    [Stmt x] -> return [x]
  where
    noTA x = ((Visible, Wildcard SType), x)

funAlt :: SIName -> [((Visibility, SExp), ParPat)] -> GuardTrees -> PreStmt
funAlt n pats gt = FunAlt n (fst <$> pats) $ compilePatts (map snd pats) gt

funAlt' n ts x gt = FunAlt n ts $ compilePatts x gt



-------------------------------------------------------------------------------- desugar info

mkDesugarInfo :: [Stmt] -> DesugarInfo
mkDesugarInfo ss =
    ( Map.fromList $ ("'EqCTt", (Infix, -1)): [(sName s, f) | PrecDef s f <- ss]
    , Map.fromList $
        [(sName cn, Left ((caseName $ sName t, pars ty), second pars <$> cs)) | Data t ps ty _ cs <- ss, (cn, ct) <- cs]
     ++ [(sName t, Right $ pars $ UncurryS ps ty) | Data t ps ty _ _ <- ss]
--     ++ [(t, Right $ length xs) | Let (_, t) _ (Just ty) xs _ <- ss]
     ++ [("'Type", Right 0)]
    )
  where
    pars (UncurryS l _) = length $ filter ((== Visible) . fst) l -- todo

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

-------------------------------------------------------------------------------- pretty print

patDoc :: Pat_ a -> Doc
patDoc = \case
    PCon (n, _) _ -> pure $ shAtom $ sName n -- TODO

parPatDoc :: ParPat_ a -> Doc
parPatDoc = \case
    ParPat [] -> pure $ shAtom "_"
    ParPat [p] -> patDoc p
    -- TODO

