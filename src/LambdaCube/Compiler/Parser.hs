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
    , pattern TyType, pattern SLet
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
--import qualified Data.IntSet as IS
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
--import Control.Monad.Identity
import Control.Arrow hiding ((<+>))
import Control.Applicative
import Control.DeepSeq
import Debug.Trace

import LambdaCube.Compiler.Utils

import qualified LambdaCube.Compiler.Pretty as BodyParser
import LambdaCube.Compiler.Pretty hiding (Doc, braces, parens)
import LambdaCube.Compiler.Lexer

-------------------------------------------------------------------------------- utils

try = try_

-------------------------------------------------------------------------------- expression representation

data SExp' a
    = SLit    SI Lit
    | SGlobal SIName
    | SApp_   SI Visibility (SExp' a) (SExp' a)
    | SBind_  SI Binder (SData SIName){-parameter name-} (SExp' a) (SExp' a)
    | SVar_   (SData SIName) !Int
    | SLet_   SI (SData SIName) (SExp' a) (SExp' a)    -- let x = e in f   -->  SLet e f{-x is Var 0-}
    | STyped  a
  deriving (Eq, Show)

type SExp = SExp' Void

data Binder
    = BPi  Visibility
    | BLam Visibility
    | BMeta      -- a metavariable is like a floating hidden lambda
  deriving (Eq, Show)

data Visibility = Hidden | Visible
  deriving (Eq, Show)

dummyName s = (debugSI s, "v_" ++ s)
dummyName' = SData . dummyName
sVar = SVar . dummyName

pattern SBind v x a b <- SBind_ _ v x a b
  where SBind v x a b =  SBind_ (sourceInfo a <> sourceInfo b) v x a b
pattern SPi  h a b <- SBind (BPi  h) _ a b
  where SPi  h a b =  SBind (BPi  h) (dummyName' "SPi") a b
pattern SLam h a b <- SBind (BLam h) _ a b
  where SLam h a b =  SBind (BLam h) (dummyName' "SLam") a b
pattern Wildcard t <- SBind BMeta _ t (SVar _ 0)
  where Wildcard t =  SBind BMeta (dummyName' "Wildcard") t (sVar "Wildcard2" 0)
pattern SLet n a b <- SLet_ _ (SData n) a b
  where SLet n a b =  SLet_ (sourceInfo a <> sourceInfo b) (SData n) a b
pattern SLamV a  = SLam Visible (Wildcard SType) a
pattern SVar a b = SVar_ (SData a) b

pattern SApp h a b <- SApp_ _ h a b
  where SApp h a b =  SApp_ (sourceInfo a <> sourceInfo b) h a b
pattern SAppH a b    = SApp Hidden a b
pattern SAppV a b    = SApp Visible a b
pattern SAppV2 f a b = f `SAppV` a `SAppV` b

infixl 2 `SAppV`, `SAppH`

pattern SBuiltin s <- SGlobal (_, s)
  where SBuiltin s =  SGlobal (debugSI $ "builtin " ++ s, s)

pattern SRHS a      = SBuiltin "^rhs"     `SAppV` a
pattern Section e   = SBuiltin "^section" `SAppV` e
pattern SType       = SBuiltin "'Type"
pattern Parens e    = SBuiltin "parens"   `SAppV` e
pattern SAnn a t    = SBuiltin "typeAnn"  `SAppH` t `SAppV` a
pattern TyType a    = SAnn a SType

sLit = SLit mempty

isPi (BPi _) = True
isPi _ = False

pattern UncurryS :: [(Visibility, SExp' a)] -> SExp' a -> SExp' a
pattern UncurryS ps t <- (getParamsS -> (ps, t))
  where UncurryS ps t = foldr (uncurry SPi) t ps

getParamsS (SPi h t x) = first ((h, t):) $ getParamsS x
getParamsS x = ([], x)

pattern AppsS :: SExp' a -> [(Visibility, SExp' a)] -> SExp' a
pattern AppsS f args  <- (getApps -> (f, args))
  where AppsS = foldl $ \a (v, b) -> SApp v a b

getApps = second reverse . run where
  run (SApp h a b) = second ((h, b):) $ run a
  run x = (x, [])

-- todo: remove
downToS err n m = [sVar (err ++ "_" ++ show i) (n + i) | i <- [m-1, m-2..0]]

instance SourceInfo (SExp' a) where
    sourceInfo = \case
        SGlobal (si, _)        -> si
        SBind_ si _ _ _ _      -> si
        SApp_ si _ _ _         -> si
        SLet_ si _ _ _         -> si
        SVar (si, _) _         -> si
        SLit si _              -> si
        STyped _               -> mempty

instance SetSourceInfo SExp where
    setSI si = \case
        SBind_ _ a b c d -> SBind_ si a b c d
        SApp_ _ a b c    -> SApp_ si a b c
        SLet_ _ le a b  -> SLet_ si le a b
        SVar (_, n) i   -> SVar (si, n) i
        SGlobal (_, n)  -> SGlobal (si, n)
        SLit _ l        -> SLit si l
        STyped v        -> elimVoid v

-------------------------------------------------------------------------------- low-level toolbox

class Up a where
    up_ :: Int -> Int -> a -> a
    up_ n i = iterateN n $ up1_ i
    up1_ :: Int -> a -> a
    up1_ = up_ 1

    foldVar :: Monoid e => (Int{-level-} -> Int{-index-} -> e) -> Int -> a -> e

    usedVar :: Int -> a -> Bool
    usedVar = (getAny .) . foldVar ((Any .) . (==))

    closedExp :: a -> a
    closedExp a = a

instance (Up a, Up b) => Up (a, b) where
    up_ n i (a, b) = (up_ n i a, up_ n i b)
    usedVar i (a, b) = usedVar i a || usedVar i b
    foldVar f i (a, b) = foldVar f i a <> foldVar f i b
    closedExp (a, b) = (closedExp a, closedExp b)

instance Up a => Up [a] where
    up_ i k = map (up_ i k)

up n = up_ n 0
up1 = up1_ 0

foldS
    :: Monoid m
    => (Int -> t -> m)
    -> (SIName -> Int -> m)
    -> (SIName -> Int -> Int -> m)
    -> Int
    -> SExp' t
    -> m
foldS h g f = fs
  where
    fs i = \case
        SApp _ a b -> fs i a <> fs i b
        SLet _ a b -> fs i a <> fs (i+1) b
        SBind_ _ _ _ a b -> fs i a <> fs (i+1) b
        SVar sn j -> f sn j i
        SGlobal sn -> g sn i
        x@SLit{} -> mempty
        STyped x -> h i x

foldName f = foldS (\_ -> elimVoid) (\sn _ -> f sn) mempty 0

usedS :: SIName -> SExp -> Bool
usedS n = getAny . foldName (Any . (== n))

mapS
    :: (Int -> a -> SExp' a)
    -> (SIName -> Int -> SExp' a)
    -> (SIName -> Int -> Int{-level-} -> SExp' a)
    -> Int
    -> SExp' a
    -> SExp' a
mapS hh gg f2 = g where
    g i = \case
        SApp_ si v a b -> SApp_ si v (g i a) (g i b)
        SLet_ si x a b -> SLet_ si x (g i a) (g (i+1) b)
        SBind_ si k si' a b -> SBind_ si k si' (g i a) (g (i+1) b)
        SVar sn j -> f2 sn j i
        SGlobal sn -> gg sn i
        STyped x -> hh i x
        x@SLit{} -> x

instance Up Void where
    up_ _ _ = elimVoid
    foldVar _ _ = elimVoid

instance Up a => Up (SExp' a) where
    up_ n = mapS (\i x -> STyped $ up_ n i x) (const . SGlobal) (\sn j i -> SVar sn $ if j < i then j else j+n)
    foldVar f = foldS (foldVar f) mempty $ \sn j i -> f j i

-- rearrange free variables
-- up_ n k == rearrange k (+n)
class Rearrange a where
    rearrange :: Int -> (Int -> Int) -> a -> a

rSubst :: Rearrange a => Int -> Int -> a -> a
rSubst i j = rearrange 0 $ \k -> if k == i then j else if k > i then k - 1 else k

rUp :: Rearrange a => Int -> Int -> a -> a
rUp n l = rearrange l $ \k -> if k >= 0 then k + n else k

instance Rearrange a => Rearrange [a] where
    rearrange l f = map $ rearrange l f

instance (Rearrange a, Rearrange b) => Rearrange (Either a b) where
    rearrange l f = rearrange l f +++ rearrange l f

instance (Rearrange a, Rearrange b) => Rearrange (a, b) where
    rearrange l f = rearrange l f *** rearrange l f

instance Rearrange SExp where
    rearrange i f = mapS (\_ -> elimVoid) (const . SGlobal) (\sn j i -> SVar sn $ if j < i then j else i + f (j - i)) i

-- replace names with de bruijn indices
class DeBruijnify a where
    deBruijnify_ :: Int -> [SIName] -> a -> a

deBruijnify = deBruijnify_ 0

instance (DeBruijnify a, DeBruijnify b) => DeBruijnify (a, b) where
    deBruijnify_ k ns = deBruijnify_ k ns *** deBruijnify_ k ns

instance (DeBruijnify a, DeBruijnify b) => DeBruijnify (Either a b) where
    deBruijnify_ k ns = deBruijnify_ k ns +++ deBruijnify_ k ns

instance (DeBruijnify a) => DeBruijnify [a] where
    deBruijnify_ k ns = fmap (deBruijnify_ k ns)

instance DeBruijnify SExp where
    deBruijnify_ j xs
        = mapS (\_ -> elimVoid) (\sn x -> maybe (SGlobal sn) (\i -> SVar sn $ i + x) $ elemIndex sn xs)
                                (\sn j k -> SVar sn $ if j >= k then j + l else j) j
      where
        l = length xs

trSExp :: (a -> b) -> SExp' a -> SExp' b
trSExp f = g where
    g = \case
        SApp_ si v a b -> SApp_ si v (g a) (g b)
        SLet_ si x a b -> SLet_ si x (g a) (g b)
        SBind_ si k si' a b -> SBind_ si k si' (g a) (g b)
        SVar sn j -> SVar sn j
        SGlobal sn -> SGlobal sn
        SLit si l -> SLit si l
        STyped a -> STyped $ f a

trSExp' :: SExp -> SExp' a
trSExp' = trSExp elimVoid

-------------------------------------------------------------------------------- parser type

type BodyParser = Parse DesugarInfo PostponedCheck

type PostponedCheck = Either (Maybe LCParseError) ParseCheck

data LCParseError
    = MultiplePatternVars [[SIName]]
    | OperatorMismatch (SIName, Fixity) (SIName, Fixity)
    | UndefinedConstructor SIName
    | ParseError ParseError

data ParseWarning
    = Unreachable Range

instance NFData ParseWarning
 where
    rnf = \case Unreachable r -> rnf r

data ParseCheck
    = TrackedCode Range
    | Reachable Range

instance Show LCParseError where
    show = \case
        MultiplePatternVars xs -> "multiple pattern vars:\n" ++ unlines [n ++ " is defined at " ++ ppShow si | ns <- xs, (si, n) <- ns]
        OperatorMismatch (op, f) (op', f') -> "Operator precedences don't match:\n" ++ show f ++ " at " ++ showSI (fst op) ++ "\n" ++ show f' ++ " at " ++ showSI (fst op')
        UndefinedConstructor (si, c) -> "Constructor " ++ c ++ " is not defined at " ++ showSI si
        ParseError p -> show p

instance Show ParseWarning where
    show = \case
        Unreachable si -> "Source code is not reachable: " ++ show (showRange si)

trackSI p = do
    x <- p
    tell $ Right . TrackedCode <$> maybeToList (getRange $ sourceInfo x)
    return x

type DesugarInfo = (FixityMap, ConsMap)

type ConsMap = Map.Map SName{-constructor name-} ConsInfo

type ConsInfo = Either ((SName{-case eliminator name-}, Int{-num of indices-}), [(SName, Int)]{-constructors with arities-})
                       Int{-arity-}

addFixity :: (a -> SIName) -> BodyParser a -> BodyParser (a, Fixity)
addFixity pr p = f <$> asks (fst . desugarInfo) <*> p
  where
    f fm sn = (sn, fromMaybe (InfixL, 9) $ Map.lookup (snd $ pr sn) fm)

-------------------------------------------------------------------------------- builtin precedences

data Prec
    = PrecAtom      --  ( _ )  ...
    | PrecAtom'
    | PrecAt        --  _@_                 {assoc}  -- in patterns
    | PrecProj      --  _ ._                {left}
    | PrecSwiz      --  _%_                 {left}
    | PrecApp       --  _ _                 {left}
    | PrecOp
    | PrecArr       --  _ -> _              {right}
    | PrecEq        --  _ ~ _
    | PrecAnn       --  _ :: _              {right}
    | PrecLet       --  _ := _
    | PrecLam       --  \ _ -> _            {right} {accum}
    deriving (Eq, Ord)

-------------------------------------------------------------------------------- expression parsing

parseType mb = maybe id option mb (reservedOp "::" *> typeNS (parseTerm PrecLam))
typedIds ds mb = (\ns t -> (,) <$> ns <*> pure t) <$> commaSep1 upperLower <*> (deBruijnify ds <$> parseType mb)

hiddenTerm p q = (,) Hidden <$ reservedOp "@" <*> typeNS p  <|>  (,) Visible <$> q

telescope mb = fmap mkTelescope $ many $ hiddenTerm
    (typedId <|> maybe empty (tvar . pure) mb)
    (try "::" typedId <|> maybe ((,) (mempty, "") <$> typeNS (parseTerm PrecAtom)) (tvar . pure) mb)
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
        ope = pure . Left <$> addFixity id (rhsOperator <|> appRange (flip (,) "'EqCTt" <$ reservedOp "~"))
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

    litString = uncurry SLit . second LString

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

    calculatePrecs :: [Either (SIName, Fixity) SExp] -> BodyParser SExp
    calculatePrecs = go where

        go (Right e: xs)         = waitOp False e [] xs
        go xs@(Left ((_, "-"), _): _) = waitOp False (mkLit $ LInt 0) [] xs
        go (Left op: xs)         = Section . SLamV <$> waitExp True (sVar "leftSection" 0) [] op xs
        go _                     = error "impossible @ Parser 479"

        waitExp lsec e acc op (Right t: xs)  = waitOp lsec e ((op, if lsec then up 1 t else t): acc) xs
        waitExp lsec e acc op [] | lsec      = fail "two-sided section is not allowed"
                                 | otherwise = fmap (Section . SLamV) . calcPrec' e $ (op, sVar "rightSection" 0): map (second (up 1)) acc
        waitExp _ _ _ _ _                    = fail "two operator is not allowed next to each-other"

        waitOp lsec e acc (Left op: xs) = waitExp lsec e acc op xs
        waitOp lsec e acc []            = calcPrec' e acc
        waitOp lsec e acc _             = error "impossible @ Parser 488"

        calcPrec' e = postponedCheck id . calcPrec (\op x y -> SGlobal (fst op) `SAppV` x `SAppV` y) snd e . reverse

    generator, letdecl, boolExpression :: BodyParser (SExp -> ErrorFinder SExp)
    generator = do
        (dbs, pat) <- try "generator" $ longPattern <* reservedOp "<-"
        checkPattern dbs
        exp <- parseTerm PrecLam
        return $ \e -> do
            cf <- compileGuardTree id id $ compilePatts [pat] (noGuards $ deBruijnify dbs e) `mappend` noGuards BNil
            return $ SBuiltin "concatMap" `SAppV` SLamV cf `SAppV` exp

    letdecl = (return .) . mkLets <$ reserved "let" <*> (compileStmt' =<< valueDef)

    boolExpression = (\pred e -> return $ SBuiltin "primIfThenElse" `SAppV` pred `SAppV` e `SAppV` BNil) <$> parseTerm PrecLam

    mkPi Hidden xs b = foldr (sNonDepPi Hidden) b $ getTTuple xs
    mkPi h a b = sNonDepPi h a b

    sNonDepPi h a b = SPi h a $ up1 b

-- builtin heterogenous list
pattern HList a   = SBuiltin "'HList" `SAppV` a
pattern HCons a b = SBuiltin "HCons" `SAppV` a `SAppV` b
pattern HNil      = SBuiltin "HNil"

-- builtin list
pattern BList a   = SBuiltin "'List" `SAppV` a
pattern BCons a b = SBuiltin "Cons" `SAppV` a `SAppV` b
pattern BNil      = SBuiltin "Nil"

getTTuple (HList (getList -> Just xs)) = xs
getTTuple x = [x]

getList BNil = Just []
getList (BCons x (getList -> Just y)) = Just (x:y)
getList _ = Nothing

patLam :: (SExp -> SExp) -> (Visibility, SExp) -> ParPat -> SExp -> ErrorFinder SExp
patLam f (v, t) p e = SLam v t <$> compileGuardTree f f (compilePatts [p] $ noGuards e)

-------------------------------------------------------------------------------- pattern representation

data Pat
    = PVar SIName -- Int
    | PCon_ SI (SIName, ConsInfo) [ParPat]
    | ViewPat_ SI SExp ParPat
    | PatType_ SI ParPat SExp
  deriving Show

-- parallel patterns like  v@(f -> [])@(Just x)
data ParPat = ParPat_ SI [Pat]
  deriving Show

pattern ParPat ps <- ParPat_ _ ps
  where ParPat ps =  ParPat_ (foldMap sourceInfo ps) ps

pattern PWildcard si = ParPat_ si []
pattern PCon n pp <- PCon_ _ n pp
  where PCon n pp =  PCon_ (fst (fst n) <> sourceInfo pp) n pp
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

pBuiltin n ci ps =  PConSimp ((debugSI $ "pattern_" ++ n, n), ci) ps

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

instance SourceInfo ParPat where
    sourceInfo (ParPat_ si _) = si

instance SetSourceInfo ParPat where
    setSI si (ParPat_ _ ps) = ParPat_ si ps

instance SourceInfo Pat where
    sourceInfo = \case
        PVar (si,_)     -> si
        PCon_ si _ _    -> si
        ViewPat_ si _ _ -> si
        PatType_ si _ _ -> si

instance SetSourceInfo Pat where
    setSI si = \case
        PVar (_, n)     -> PVar (si, n)
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
        oper = addFixity fst $ addConsInfo colonSymbols
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

    mkPVar (si, "") = PWildcard si
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

    calculatePatPrecs e xs = postponedCheck (first fst) $ calcPrec (\op x y -> PConSimp (fst op) [x, y]) snd e xs

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
   case [ns' | ns' <- group . sort . filter (not . null . snd) $ ns
             , not . null . tail $ ns'] of
    [] -> Nothing
    xs -> Just $ MultiplePatternVars xs

postponedCheck pr x = do
    tell [Left $ either (\(a, b) -> Just $ OperatorMismatch (pr a) (pr b)) (const Nothing) x]
    return $ either (const $ error "impossible @ Parser 725") id x

-------------------------------------------------------------------------------- pattern match compilation

type ErrorFinder = BodyParser

-- pattern match compilation monad
type PMC = Writer [Range]

runPMC m = tell (map (Right . Reachable) w) >> return a
  where
    (a, w) = runWriter m

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

guardNode :: Pat -> SExp -> GuardTrees -> GuardTrees
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
    ps  -> lLet (si, "gtc") e $ buildNode guardNode 1 ps [0..] gt

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
        x = case Map.lookup (snd s) adts of
            Nothing -> throwError s
            Just i -> return (s, i)


compileGuardTree :: (SExp -> SExp) -> (SExp -> SExp) -> GuardTrees -> ErrorFinder SExp
compileGuardTree ulend lend = runPMC . guardTreeToCases
  where
    guardTreeToCases :: GuardTrees -> PMC SExp
    guardTreeToCases = \case
        LLet sn e g -> SLet sn e <$> guardTreeToCases g
        LTypeAnn t g -> SAnn <$> guardTreeToCases g <*> pure t
        In GTFailure -> return $ ulend $ SBuiltin "undefined"
        In (GTSuccess e) -> do
            tell $ maybeToList $ getRange $ sourceInfo e
            --trace (ppShow $ sourceInfo e) $ 
            return $ lend e
        ts@(In (GuardNode f ((si, s), cn) _ _ _)) -> case cn of
--            Nothing -> throwError sn
            Left ((casename, inum), cns) -> do
                cf <- sequence [ iterateN n SLamV <$> guardTreeToCases (filterGuardTree (up n f) cn 0 n $ rUp n 0 ts) | (cn, n) <- cns ]
                return $
                    foldl SAppV
                        (SGlobal (debugSI "compileGuardTree2", casename) `SAppV` iterateN (1 + inum) SLamV (Wildcard (Wildcard SType)))
                        cf
                    `SAppV` f
            Right n -> do
                g1 <- guardTreeToCases $ filterGuardTree (up n f) s 0 n $ rUp n 0 ts
                g2 <- guardTreeToCases (filterGuardTree' f s ts)
                return $ SGlobal (debugSI "compileGuardTree3", MatchName s)
                 `SAppV` SLamV (Wildcard SType)
                 `SAppV` iterateN n SLamV g1
                 `SAppV` f
                 `SAppV` g2

    filterGuardTree' :: SExp -> SName{-constr.-} -> GuardTrees -> GuardTrees
    filterGuardTree' f s = \case
        LLet sn e gt -> LLet sn e $ filterGuardTree' (up 1 f) s gt
        LTypeAnn e gt -> LTypeAnn e $ filterGuardTree' f s gt
        In (GuardNode f' s' ps gs (filterGuardTree' f s -> el))
            | f /= f' || s /= snd (fst s') -> In $ GuardNode f' s' ps (filterGuardTree' (up (length ps) f) s gs) el
            | otherwise -> el
        In x -> In x

    filterGuardTree :: SExp -> SName{-constr.-} -> Int -> Int{-number of constr. params-} -> GuardTrees -> GuardTrees
    filterGuardTree f s k ns = \case
        LLet sn e gt -> LLet sn e $ filterGuardTree (up 1 f) s (k + 1) ns gt
        LTypeAnn e gt -> LTypeAnn e $ filterGuardTree f s k ns gt
        In (GuardNode f' s' ps gs (filterGuardTree f s k ns -> el))
            | f /= f'   -> In $ GuardNode f' s' ps (filterGuardTree (up su f) s (su + k) ns gs) el
            | s == snd (fst s') -> filterGuardTree f s k ns $ foldr (rSubst 0) gs (replicate su $ k+ns-1) <> el
            | otherwise -> el
          where
            su = length ps
        In x -> In x

compileGuardTrees ulend = compileGuardTree ulend SRHS . mconcat

compileGuardTrees' = fmap (foldr1 $ SAppV2 $ SBuiltin "parEval" `SAppV` Wildcard SType) . mapM (compileGuardTrees id . (:[]))

compileCase x cs
    = (`SAppV` x) . SLamV <$> compileGuardTree id id (mconcat [compilePatts [p] e | (p, e) <- cs])


-------------------------------------------------------------------------------- declaration representation

data Stmt
    = Let SIName (Maybe SExp) SExp
    | Data SIName [(Visibility, SExp)]{-parameters-} SExp{-type-} Bool{-True:add foralls-} [(SIName, SExp)]{-constructor names and types-}
    | PrecDef SIName Fixity
    deriving (Show)

pattern Primitive n t <- Let n (Just t) (SBuiltin "undefined") where Primitive n t = Let n (Just t) $ SBuiltin "undefined"

data PreStmt
    = Stmt Stmt
    -- eliminated during parsing
    | TypeAnn SIName SExp
    | TypeFamily SIName SExp{-type-}   -- type family declaration
    | FunAlt SIName [(Visibility, SExp)]{-TODO: remove-} GuardTrees
    | Class SIName [SExp]{-parameters-} [(SIName, SExp)]{-method names and types-}
    | Instance SIName [ParPat]{-parameter patterns-} [SExp]{-constraints-} [Stmt]{-method definitions-}
    deriving (Show)

instance PShow Stmt where
    pShowPrec p = \case
        Let (_, n) ty e -> text n </> "=" <+> maybe (pShow e) (\ty -> pShow e </> "::" <+> pShow ty) ty 
        Data (_, n) ps ty fa cs -> "data" <+> text n
        PrecDef (_, n) i -> "precedence" <+> text n <+> text (show i)

instance DeBruijnify PreStmt where
    deBruijnify_ k v = \case
        FunAlt n ts gue -> FunAlt n (map (second $ deBruijnify_ k v) ts) $ deBruijnify_ k v gue
        x -> error $ "deBruijnify @ " ++ show x

instance DeBruijnify Stmt where
    deBruijnify_ k v = \case
        Let sn mt e -> Let sn (deBruijnify_ k v <$> mt) (deBruijnify_ k v e)
        x -> error $ "deBruijnify @ " ++ show x
-------------------------------------------------------------------------------- declaration parsing

parseDef :: BodyParser [PreStmt]
parseDef =
     do reserved "data" *> do
            x <- typeNS upperCase
            (npsd, ts) <- telescope (Just SType)
            t <- deBruijnify npsd <$> parseType (Just SType)
            let mkConTy mk (nps', ts') =
                    ( if mk then Just nps' else Nothing
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
                        fmap Stmt <$> compileStmt (compileGuardTrees id) [TypeAnn x $ UncurryS ts t] cs
             <|> pure <$ reserved "instance" <*> funAltDef Nothing upperCase
             <|> do x <- upperCase
                    (nps, ts) <- telescope $ Just (Wildcard SType)
                    rhs <- deBruijnify nps <$ reservedOp "=" <*> parseTerm PrecLam
                    fmap Stmt <$> compileStmt (compileGuardTrees id)
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
                return $ funAlt' fn [(Visible, Wildcard SType)] [PConSimp cn' $ replicate (length fs) $ PVarSimp (mempty, "generated_name1")]
                       $ noGuards $ sVar "proj" i
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
    e <- parseTerm PrecLam
    desugarValueDef p e
  where
    desugarValueDef p e = sequence
        $ pure (FunAlt n [] $ noGuards e)
        : [ FunAlt x [] . noGuards <$> compileCase (SGlobal n) [(p, noGuards $ SVar x i)]
          | (i, x) <- zip [0..] dns
          ]
      where
        dns = reverse $ getPVars p
        n = mangleNames dns

mangleNames xs = (foldMap fst xs, "_" ++ intercalate "_" (map snd xs))

mkLets :: [Stmt]{-where block-} -> SExp{-main expression-} -> SExp{-big let with lambdas; replaces global names with de bruijn indices-}
mkLets = mkLets_ SLet

mkLets_ mkLet = mkLets' . sortDefs where
    mkLets' [] e = e
    mkLets' (Let n mt x: ds) e
        = mkLet n (maybe id (flip SAnn . addForalls {-todo-}[] []) mt x') (deBruijnify [n] $ mkLets' ds e)
      where
        x' = if usedS n x then SBuiltin "primFix" `SAppV` SLamV (deBruijnify [n] x) else x
    mkLets' (x: ds) e = error $ "mkLets: " ++ show x

addForalls :: Extensions -> [SName] -> SExp -> SExp
addForalls exs defined x = foldl f x [v | v@(_, vh:_) <- reverse $ names x, snd v `notElem'` ("fromInt"{-todo: remove-}: defined), isLower vh]
  where
    f e v = SPi Hidden (Wildcard SType) $ deBruijnify [v] e

    notElem' s@('\'':s') m = notElem s m && notElem s' m
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

-------------------------------------------------------------------------------- declaration desugaring

data StmtNode = StmtNode
    { snId          :: !Int
    , snValue       :: Stmt
    , snChildren    :: [StmtNode]
    , snRevChildren :: [StmtNode]
    }

sortDefs :: [Stmt] -> [Stmt]
sortDefs xs = concatMap (desugarMutual . map snValue) $ scc snId snChildren snRevChildren nodes
  where
    nodes = zipWith mkNode [0..] xs
      where
        mkNode i s = StmtNode i s (nubBy ((==) `on` snId) $ catMaybes $ (`Map.lookup` defMap) <$> need)
                                  (fromMaybe [] $ IM.lookup i revMap)
          where
            need = Set.toList $ case s of
                PrecDef{} -> mempty
                Let _ mt e -> foldMap names mt <> names e
                Data _ ps t _ cs -> foldMap (names . snd) ps <> names t <> foldMap (names . snd) cs

            names = foldName Set.singleton

    revMap = IM.unionsWith (++) [IM.singleton (snId c) [n] | n <- nodes, c <- snChildren n]

    defMap = Map.fromList [(s, n) | n <- nodes, s <- def $ snValue n]
      where
        def = \case
            PrecDef{} -> mempty
            Let n _ _ -> [n]
            Data n _ _ _ cs -> n: map fst cs

desugarMutual [x] = [x]
desugarMutual xs = xs
{-
    = FunAlt n [] (Right e)
    : [ FunAlt x [] $ Right $ compileCase ds (SGlobal n) [(p, Right $ SVar x i)]
      | (i, x) <- zip [0..] dns
      ]
  where
    dns = reverse $ getPVars p
    n = mangleNames dns
    (ps, es) = unzip [(n, e) | Let n ~Nothing ~Nothing [] e <- xs]
    tup = "Tuple" ++ show (length xs)
    e = deBruijnify ps $ foldl SAppV (SBuiltin tup) es
    p = PCon (mempty, tup) $ map (ParPat . pure . PVar) ps
-}


------------------------------------------------------------------------

compileStmt' ds = fmap concat . sequence $ map (compileStmt (compileGuardTrees SRHS) ds) $ groupBy h ds where
    h (FunAlt n _ _) (FunAlt m _ _) = m == n
    h _ _ = False

compileStmt :: ([GuardTrees] -> ErrorFinder SExp) -> [PreStmt] -> [PreStmt] -> ErrorFinder [Stmt]
compileStmt compilegt ds = \case
    [Instance{}] -> return []
    [Class n ps ms] -> do
        cd <- compileStmt' $
            [ TypeAnn n $ foldr (SPi Visible) SType ps ]
         ++ [ funAlt n (map noTA ps) $ noGuards $ foldr (SAppV2 $ SBuiltin "'T2") (SBuiltin "'Unit") cstrs | Instance n' ps cstrs _ <- ds, n == n' ]
         ++ [ funAlt n (replicate (length ps) (noTA $ PVarSimp (debugSI "compileFunAlts1", "generated_name0"))) $ noGuards $ SBuiltin "'Empty" `SAppV` sLit (LString $ "no instance of " ++ snd n ++ " on ???")]
        cds <- sequence
            [ compileStmt'
            $ TypeAnn m (UncurryS (map ((,) Hidden) ps) $ SPi Hidden (foldl SAppV (SGlobal n) $ downToS "a2" 0 $ length ps) $ up1 t)
            : as
            | (m, t) <- ms
--            , let ts = fst $ getParamsS $ up1 t
            , let as = [ funAlt m p $ noGuards {- -$ SLam Hidden (Wildcard SType) $ up1 -} $ SLet m' e $ SVar mempty 0
                      | Instance n' i cstrs alts <- ds, n' == n
                      , Let m' ~Nothing e <- alts, m' == m
                      , let p = zip ((,) Hidden <$> ps) i ++ [((Hidden, Wildcard SType), PVarSimp (mempty, ""))]
        --              , let ic = patVars i
                      ]
            ]
        return $ cd ++ concat cds
    [TypeAnn n t] -> return [Primitive n t | snd n `notElem` [n' | FunAlt (_, n') _ _ <- ds]]
    tf@[TypeFamily n t] -> case [d | d@(FunAlt n' _ _) <- ds, n' == n] of
        [] -> return [Primitive n t]
        alts -> compileStmt compileGuardTrees' [TypeAnn n t] alts
    fs@(FunAlt n vs _: _) -> case map head $ group [length vs | FunAlt _ vs _ <- fs] of
        [num]
          | num == 0 && length fs > 1 -> fail $ "redefined " ++ snd n ++ " at " ++ ppShow (fst n)
          | n `elem` [n' | TypeFamily n' _ <- ds] -> return []
          | otherwise -> do
            cf <- compilegt [gt | FunAlt _ _ gt <- fs]
            return [Let n (listToMaybe [t | TypeAnn n' t <- ds, n' == n]) $ foldr (uncurry SLam) cf vs]
        _ -> fail $ "different number of arguments of " ++ snd n ++ " at " ++ ppShow (fst n)
    [Stmt x] -> return [x]
  where
    noTA x = ((Visible, Wildcard SType), x)

funAlt :: SIName -> [((Visibility, SExp), ParPat)] -> GuardTrees -> PreStmt
funAlt n pats gt = FunAlt n (fst <$> pats) $ compilePatts (map snd pats) gt

funAlt' n ts x gt = FunAlt n ts $ compilePatts x gt



-------------------------------------------------------------------------------- desugar info

mkDesugarInfo :: [Stmt] -> DesugarInfo
mkDesugarInfo ss =
    ( Map.fromList $ ("'EqCTt", (Infix, -1)): [(s, f) | PrecDef (_, s) f <- ss]
    , Map.fromList $
        [(cn, Left ((caseName t, pars ty), (snd *** pars) <$> cs)) | Data (_, t) ps ty _ cs <- ss, ((_, cn), ct) <- cs]
     ++ [(t, Right $ pars $ UncurryS ps ty) | Data (_, t) ps ty _ _ <- ss]
--     ++ [(t, Right $ length xs) | Let (_, t) _ (Just ty) xs _ <- ss]
     ++ [("'Type", Right 0)]
    )
  where
    pars (UncurryS l _) = length $ filter ((== Visible) . fst) l -- todo

-------------------------------------------------------------------------------- module exports

data Export = ExportModule SIName | ExportId SIName

parseExport :: HeaderParser Export
parseExport =
        ExportModule <$ reserved "module" <*> moduleName
    <|> ExportId <$> varId

-------------------------------------------------------------------------------- module imports

data ImportItems
    = ImportAllBut [SIName]
    | ImportJust [SIName]

importlist = parens $ commaSep upperLower

-------------------------------------------------------------------------------- language pragmas

type Extensions = [Extension]

data Extension
    = NoImplicitPrelude
    | TraceTypeCheck
    deriving (Enum, Eq, Ord, Show)

extensionMap :: Map.Map String Extension
extensionMap = Map.fromList $ map (show &&& id) [toEnum 0 .. ]

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

-------------------------------------------------------------------------------- modules

data Module = Module
    { extensions    :: Extensions
    , moduleImports :: [(SIName, ImportItems)]
    , moduleExports :: Maybe [Export]
    , definitions   :: DefParser
    }

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
        , moduleImports = [((mempty, "Prelude"), ImportAllBut []) | NoImplicitPrelude `notElem` exts] ++ idefs
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

    return (sortDefs defs, [Unreachable is | Right (TrackedCode is) <- dns, is `Set.notMember` ism], ds)

-------------------------------------------------------------------------------- pretty print

instance Up a => PShow (SExp' a) where
    pShowPrec _ = showDoc_ . sExpDoc

type Doc = NameDB PrecString

-- name De Bruijn indices
type NameDB a = StateT [String] (Reader [String]) a

showDoc :: Doc -> String
showDoc = str . flip runReader [] . flip evalStateT (flip (:) <$> iterate ('\'':) "" <*> ['a'..'z'])

showDoc_ :: Doc -> BodyParser.Doc
showDoc_ = text . str . flip runReader [] . flip evalStateT (flip (:) <$> iterate ('\'':) "" <*> ['a'..'z'])

sExpDoc :: Up a => SExp' a -> Doc
sExpDoc = \case
    SGlobal (_,s)   -> pure $ shAtom s
    SAnn a b        -> shAnn ":" False <$> sExpDoc a <*> sExpDoc b
    TyType a        -> shApp Visible (shAtom "tyType") <$> sExpDoc a
    SApp h a b    -> shApp h <$> sExpDoc a <*> sExpDoc b
    Wildcard t      -> shAnn ":" True (shAtom "_") <$> sExpDoc t
    SBind_ _ h _ a b -> join $ shLam (usedVar 0 b) h <$> sExpDoc a <*> pure (sExpDoc b)
    SLet _ a b      -> shLet_ (sExpDoc a) (sExpDoc b)
    STyped _{-(e,t)-}  -> pure $ shAtom "<<>>" -- todo: expDoc e
    SVar _ i        -> shAtom <$> shVar i
    SLit _ l        -> pure $ shAtom $ show l

shVar i = asks lookupVarName where
    lookupVarName xs | i < length xs && i >= 0 = xs !! i
    lookupVarName _ = "V" ++ show i

newName = gets head <* modify tail

shLet i a b = shAtom <$> shVar i >>= \i' -> local (dropNth i) $ shLam' <$> (cpar . shLet' (fmap inBlue i') <$> a) <*> b
shLet_ a b = newName >>= \i -> shLam' <$> (cpar . shLet' (shAtom i) <$> a) <*> local (i:) b
shLam usedVar h a b = newName >>= \i ->
    let lam = case h of
            BPi _ -> shArr
            _ -> shLam'
        p = case h of
            BMeta -> cpar . shAnn ":" True (shAtom $ inBlue i)
            BLam h -> vpar h
            BPi h -> vpar h
        vpar Hidden = brace . shAnn ":" True (shAtom $ inGreen i)
        vpar Visible = ann (shAtom $ inGreen i)
        ann | usedVar = shAnn ":" False
            | otherwise = const id
    in lam (p a) <$> local (i:) b

-----------------------------------------

data PS a = PS Prec a deriving (Functor)
type PrecString = PS String

getPrec (PS p _) = p
prec i s = PS i (s i)
str (PS _ s) = s

lpar, rpar :: PrecString -> Prec -> String
lpar (PS i s) j = par (i >. j) s  where
    PrecLam >. i = i > PrecAtom'
    i >. PrecLam = i >= PrecArr
    PrecApp >. PrecApp = False
    i >. j  = i >= j
rpar (PS i s) j = par (i >. j) s where
    PrecLam >. PrecLam = False
    PrecLam >. i = i > PrecAtom'
    PrecArr >. PrecArr = False
    PrecAnn >. PrecAnn = False
    i >. j  = i >= j

par True s = "(" ++ s ++ ")"
par False s = s

isAtom = (==PrecAtom) . getPrec
isAtom' = (<=PrecAtom') . getPrec

shAtom = PS PrecAtom
shAtom' = PS PrecAtom'
shTuple xs = prec PrecAtom $ \_ -> case xs of
    [x] -> "((" ++ str x ++ "))"
    xs -> "(" ++ intercalate ", " (map str xs) ++ ")"
shAnn _ True x y | str y `elem` ["Type", inGreen "Type"] = x
shAnn s simp x y | isAtom x && isAtom y = shAtom' $ str x <> s <> str y
shAnn s simp x y = prec PrecAnn $ lpar x <> " " <> const s <> " " <> rpar y
shApp Hidden x y = prec PrecApp $ lpar x <> " " <> const (str $ brace y)
shApp h x y = prec PrecApp $ lpar x <> " " <> rpar y
shArr x y | isAtom x && isAtom y = shAtom' $ str x <> "->" <> str y
shArr x y = prec PrecArr $ lpar x <> " -> " <> rpar y
shCstr x y | isAtom x && isAtom y = shAtom' $ str x <> "~" <> str y
shCstr x y = prec PrecEq $ lpar x <> " ~ " <> rpar y
shLet' x y | isAtom x && isAtom y = shAtom' $ str x <> ":=" <> str y
shLet' x y = prec PrecLet $ lpar x <> " := " <> rpar y
shLam' x y | PrecLam <- getPrec y = prec PrecLam $ "\\" <> lpar x <> " " <> pure (dropC $ str y)
  where
    dropC (ESC s (dropC -> x)) = ESC s x
    dropC (x: xs) = xs
shLam' x y | isAtom x && isAtom y = shAtom' $ "\\" <> str x <> "->" <> str y
shLam' x y = prec PrecLam $ "\\" <> lpar x <> " -> " <> rpar y
brace s = shAtom $ "{" <> str s <> "}"
cpar s | isAtom' s = s      -- TODO: replace with lpar, rpar
cpar s = shAtom $ par True $ str s
epar = fmap underlined

instance IsString (Prec -> String) where fromString = const

