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
    , sourceInfo, SI(..), debugSI
    , Module(..), Visibility(..), Binder(..), SExp'(..), Extension(..), Extensions
    , pattern SVar, pattern SType, pattern Wildcard, pattern SAppV, pattern SLamV, pattern SAnn
    , pattern SBuiltin, pattern SPi, pattern Primitive, pattern SRHS, pattern SLam, pattern Parens
    , pattern TyType, pattern SLet
    , debug, isPi, iterateN, traceD
    , parseLC, runDefParser
    , pattern UncurryS, pattern AppsS, downToS, addForalls
    , Up (..), up1, up
    , Doc, shLam, shApp, shLet, shLet_, shAtom, shAnn, shVar, epar, showDoc, showDoc_, sExpDoc, shCstr, shTuple
    , mtrace
    , trSExp', usedS, substSG0, mapS
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
import qualified Data.IntSet as IS
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Arrow hiding ((<+>))
import Control.Applicative
--import Debug.Trace

import qualified LambdaCube.Compiler.Pretty as BodyParser
import LambdaCube.Compiler.Pretty hiding (Doc, braces, parens)
import LambdaCube.Compiler.Lexer

-------------------------------------------------------------------------------- utils

(<&>) = flip (<$>)

dropNth i xs = take i xs ++ drop (i+1) xs
iterateN n f e = iterate f e !! n
mtrace s = trace_ s $ return ()

data Void

instance Show Void where show = elimVoid
instance Eq Void where x == y = elimVoid x

elimVoid :: Void -> a
elimVoid _ = error "impossible"

-- supplementary data: data with no semantic relevance
newtype SData a = SData a

instance Show (SData a) where show _ = "SData"
instance Eq (SData a) where _ == _ = True
instance Ord (SData a) where _ `compare` _ = EQ

traceD x = if debug then trace_ x else id

debug = False--True--tr

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

rearrangeS :: (Int -> Int) -> SExp -> SExp
rearrangeS f = mapS (\_ -> elimVoid) (const . SGlobal) (\sn j i -> SVar sn $ if j < i then j else i + f (j - i)) 0

dbf_ :: Int -> DBNames -> SExp -> SExp
dbf_ j xs
    = mapS (\_ -> elimVoid) (\sn x -> maybe (SGlobal sn) (\i -> SVar sn $ i + x) $ elemIndex sn xs)
                            (\sn j k -> SVar sn $ if j >= k then j + l else j) j
  where
    l = length xs

dbf = dbf_ 0

substSG0 :: SIName -> SExp -> SExp
substSG0 n = dbf [n]

instance Up Void where
    up_ _ _ = elimVoid
    foldVar _ _ = elimVoid

instance Up a => Up (SExp' a) where
    up_ n = mapS (\i x -> STyped $ up_ n i x) (const . SGlobal) (\sn j i -> SVar sn $ if j < i then j else j+n)
    foldVar f = foldS (foldVar f) mempty $ \sn j i -> f j i

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

type PostponedCheck = Maybe LCParseError

data LCParseError
    = MultiplePatternVars [[SIName]]
    | OperatorMismatch (SIName, Fixity) (SIName, Fixity)
    | ParseError ParseError

instance Show LCParseError where
    show = \case
        MultiplePatternVars xs -> "multiple pattern vars:\n" ++ unlines [n ++ " is defined at " ++ ppShow si | ns <- xs, (si, n) <- ns]
        OperatorMismatch (op, f) (op', f') -> "Operator precedences don't match:\n" ++ show f ++ " at " ++ showSI (fst op) ++ "\n" ++ show f' ++ " at " ++ showSI (fst op')
        ParseError p -> show p

type DesugarInfo = (FixityMap, ConsMap)

type ConsMap = Map.Map SName{-constructor name-}
                (Either ((SName{-case eliminator name-}, Int{-num of indices-}), [(SName, Int)]{-constructors with arities-})
                        Int{-arity-})

getFixity :: DesugarInfo -> SName -> Fixity
getFixity (fm, _) n = fromMaybe (InfixL, 9) $ Map.lookup n fm

dsInfo :: BodyParser DesugarInfo
dsInfo = asks desugarInfo

-------------------------------------------------------------------------------- builtin precedences

data Prec
    = PrecAtom      --  ( _ )  ...
    | PrecAtom'
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
typedIds mb = (,) <$> commaSep1 upperLower <*> parseType mb

hiddenTerm p q = (,) Hidden <$ reservedOp "@" <*> typeNS p  <|>  (,) Visible <$> q

telescope mb = fmap dbfi $ many $ hiddenTerm
    (typedId <|> maybe empty (tvar . pure) mb)
    (try "::" typedId <|> maybe ((,) (mempty, "") <$> typeNS (parseTerm PrecAtom)) (tvar . pure) mb)
  where
    tvar x = (,) <$> patVar <*> x
    typedId = parens $ tvar $ parseType mb

dbfi = first reverse . unzip . go []
  where
    go _ [] = []
    go vs ((v, (n, e)): ts) = (n, (v, dbf vs e)): go (n: vs) ts

indentation p q = p >> q

parseTerm p = appRange $ flip setSI <$> (dsInfo >>= flip parseTerm_ p)

parseTerm_ :: DesugarInfo -> Prec -> BodyParser SExp
parseTerm_ ge = \case
    PrecLam ->
         do level PrecAnn $ \t -> mkPi <$> (Visible <$ reservedOp "->" <|> Hidden <$ reservedOp "=>") <*> pure t <*> parseTerm PrecLam
     <|> mkIf <$ reserved "if" <*> parseTerm PrecLam <* reserved "then" <*> parseTerm PrecLam <* reserved "else" <*> parseTerm PrecLam
     <|> do reserved "forall"
            (fe, ts) <- telescope $ Just $ Wildcard SType
            f <- SPi . const Hidden <$ reservedOp "." <|> SPi . const Visible <$ reservedOp "->"
            t' <- dbf fe <$> parseTerm PrecLam
            return $ foldr (uncurry f) t' ts
     <|> do expNS $ do
                (fe, ts) <- reservedOp "\\" *> telescopePat <* reservedOp "->"
                t' <- dbf fe <$> parseTerm PrecLam
                return $ foldr (uncurry (patLam id ge)) t' ts
     <|> compileCase ge <$ reserved "case" <*> parseTerm PrecLam <* reserved "of" <*> do
            identation False $ do
                (fe, p) <- longPattern
                (,) p <$> parseRHS (dbf fe) "->"
    PrecAnn -> level PrecOp $ \t -> SAnn t <$> parseType Nothing
    PrecOp -> (notOp False <|> notExp) >>= calculatePrecs ge where
        notExp = (++) <$> ope <*> notOp True
        notOp x = (++) <$> try "expression" ((++) <$> ex PrecApp <*> option [] ope) <*> notOp True
             <|> if x then option [] (try "lambda" $ ex PrecLam) else mzero
        ope = pure . Left <$> (rhsOperator <|> appRange (flip (,) "'EqCTt" <$ reservedOp "~"))
        ex pr = pure . Right <$> parseTerm pr
    PrecApp ->
        AppsS <$> try "record" (SGlobal <$> upperCase <* symbol "{")
              <*> commaSep ((,) Visible <$ lowerCase{-TODO-} <* reservedOp "=" <*> parseTerm PrecLam)
              <*  symbol "}"
     <|> AppsS <$> parseTerm PrecSwiz <*> many (hiddenTerm (parseTerm PrecSwiz) $ parseTerm PrecSwiz)
    PrecSwiz -> level PrecProj $ \t ->
        mkSwizzling t <$> lexeme (try "swizzling" $ char '%' *> manyNM 1 4 (satisfy (`elem` ("xyzwrgba" :: String))))
    PrecProj -> level PrecAtom $ \t ->
        try "projection" $ mkProjection t <$ char '.' <*> sepBy1 lowerCase (char '.')
    PrecAtom ->
         mkLit <$> try "literal" parseLit
     <|> Wildcard (Wildcard SType) <$ reserved "_"
     <|> mkLets ge <$ reserved "let" <*> parseDefs <* reserved "in" <*> parseTerm PrecLam
     <|> SGlobal <$> lowerCase
     <|> SGlobal <$> upperCase_  -- todo: move under ppa?
     <|> braces (mkRecord <$> commaSep ((,) <$> lowerCase <* symbol ":" <*> parseTerm PrecLam))
     <|> char '\'' *> ppa switchNamespace
     <|> ppa id
  where
    level pr f = parseTerm_ ge pr >>= \t -> option t $ f t

    ppa tick =
         brackets ( (parseTerm PrecLam >>= \e ->
                mkDotDot e <$ reservedOp ".." <*> parseTerm PrecLam
            <|> foldr ($) (BCons e BNil) <$ reservedOp "|" <*> commaSep (generator <|> letdecl <|> boolExpression)
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

    calculatePrecs :: DesugarInfo -> [Either SIName SExp] -> BodyParser SExp
    calculatePrecs dcls = go where

        go (Right e: xs)         = waitOp False e [] xs
        go xs@(Left (_, "-"): _) = waitOp False (mkLit $ LInt 0) [] xs
        go (Left op: xs)         = Section . SLamV <$> waitExp True (sVar "leftSection" 0) [] op xs
        go _                     = error "impossible"

        waitExp lsec e acc op (Right t: xs)  = waitOp lsec e ((op, if lsec then up 1 t else t): acc) xs
        waitExp lsec e acc op [] | lsec      = fail "two-sided section is not allowed"
                                 | otherwise = fmap (Section . SLamV) . calcPrec' e $ (op, sVar "rightSection" 0): map (second (up 1)) acc
        waitExp _ _ _ _ _                    = fail "two operator is not allowed next to each-other"

        waitOp lsec e acc (Left op: xs) = waitExp lsec e acc op xs
        waitOp lsec e acc []            = calcPrec' e acc
        waitOp lsec e acc _             = error "impossible"

        calcPrec' e = postponedCheck dcls . calcPrec (\op x y -> SGlobal op `SAppV` x `SAppV` y) (getFixity dcls . snd) e . reverse

    generator, letdecl, boolExpression :: BodyParser (SExp -> SExp)
    generator = do
        (dbs, pat) <- try "generator" $ longPattern <* reservedOp "<-"
        checkPattern dbs
        exp <- parseTerm PrecLam
        return $ \e ->
                 SBuiltin "concatMap"
         `SAppV` SLamV (compileGuardTree id id ge $ Alts
                    [ compilePatts [(pat, 0)] $ Right $ dbf dbs e
                    , GuardLeaf $ BNil
                    ])
         `SAppV` exp

    letdecl = mkLets ge <$ reserved "let" <*> (compileFunAlts' =<< valueDef)

    boolExpression = (\pred e -> SBuiltin "primIfThenElse" `SAppV` pred `SAppV` e `SAppV` BNil) <$> parseTerm PrecLam

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

patLam :: (SExp -> SExp) -> DesugarInfo -> (Visibility, SExp) -> Pat -> SExp -> SExp
patLam f ge (v, t) p e = SLam v t $ compileGuardTree f f ge $ compilePatts [(p, 0)] $ Right e

-------------------------------------------------------------------------------- pattern representation

data Pat
    = PVar SIName -- Int
    | PCon SIName [ParPat]
    | ViewPat SExp ParPat
    | PatType ParPat SExp
  deriving Show

pattern PParens p = ViewPat (SBuiltin "parens") (ParPat [p])

-- parallel patterns like  v@(f -> [])@(Just x)
newtype ParPat = ParPat [Pat]
  deriving Show

mapPP f = \case
    ParPat ps -> ParPat (mapP f <$> ps)

mapP :: (SExp -> SExp) -> Pat -> Pat
mapP f = \case
    PVar n -> PVar n
    PCon n pp -> PCon n (mapPP f <$> pp)
    PParens p -> PParens (mapP f p)
    ViewPat e pp -> ViewPat (f e) (mapPP f pp)
    PatType pp e -> PatType (mapPP f pp) (f e)

--upP i j = mapP (up_ j i)

varPP = length . getPPVars_
varP = length . getPVars_

type DBNames = [SIName]  -- De Bruijn variable names

getPVars :: Pat -> DBNames
getPVars = reverse . getPVars_

getPPVars = reverse . getPPVars_

getPVars_ = \case
    PVar n -> [n]
    PCon _ pp -> foldMap getPPVars_ pp
    PParens p -> getPVars_ p
    ViewPat e pp -> getPPVars_ pp
    PatType pp e -> getPPVars_ pp

getPPVars_ = \case
    ParPat pp -> foldMap getPVars_ pp

instance SourceInfo ParPat where
    sourceInfo (ParPat ps) = sourceInfo ps

instance SourceInfo Pat where
    sourceInfo = \case
        PVar (si,_)     -> si
        PCon (si,_) ps  -> si <> sourceInfo ps
        ViewPat e ps    -> sourceInfo e  <> sourceInfo ps
        PatType ps e    -> sourceInfo ps <> sourceInfo e

-------------------------------------------------------------------------------- pattern parsing

parsePat :: Prec -> BodyParser Pat
parsePat = \case
  PrecAnn ->
        patType <$> parsePat PrecOp <*> parseType (Just $ Wildcard SType)
  PrecOp ->
        join $ calculatePatPrecs <$> dsInfo <*> p_
    where
        p_ = (,) <$> parsePat PrecApp <*> option [] (colonSymbols >>= p)
        p op = do (exp, op') <- try "pattern" ((,) <$> parsePat PrecApp <*> colonSymbols)
                  ((op, exp):) <$> p op'
           <|> pure . (,) op <$> parsePat PrecAnn
  PrecApp ->
         PCon <$> upperCase_ <*> many (ParPat . pure <$> parsePat PrecAtom)
     <|> parsePat PrecAtom
  PrecAtom ->
         mkLit <$> asks namespace <*> try "literal" parseLit
     <|> flip PCon [] <$> upperCase_
     <|> char '\'' *> switchNS (parsePat PrecAtom)
     <|> PVar <$> patVar
     <|> (\ns -> pConSI . mkListPat ns) <$> asks namespace <*> brackets patlist
     <|> (\ns -> pConSI . mkTupPat ns) <$> asks namespace <*> parens patlist
 where
    litP = flip ViewPat (ParPat [PCon (mempty, "True") []]) . SAppV (SBuiltin "==")

    mkLit TypeNS (LInt n) = toNatP n        -- todo: elim this alternative
    mkLit _ n@LInt{} = litP (SBuiltin "fromInt" `SAppV` sLit n)
    mkLit _ n = litP (sLit n)

    toNatP = run where
      run 0         = PCon (mempty, "Zero") []
      run n | n > 0 = PCon (mempty, "Succ") [ParPat [run $ n-1]]

    pConSI (PCon (_, n) ps) = PCon (sourceInfo ps, n) ps
    pConSI p = p

    patlist = commaSep $ parsePat PrecAnn

    mkListPat TypeNS [p] = PCon (debugSI "mkListPat4", "'List") [ParPat [p]]
    mkListPat ns (p: ps) = PCon (debugSI "mkListPat2", "Cons") $ map (ParPat . (:[])) [p, mkListPat ns ps]
    mkListPat _ []       = PCon (debugSI "mkListPat3", "Nil") []

    --mkTupPat :: [Pat] -> Pat
    mkTupPat ns [PParens x] = ff [x]
    mkTupPat ns [x] = PParens x
    mkTupPat ns ps = ff ps

    ff ps = foldr (\a b -> PCon (mempty, "HCons") (ParPat . (:[]) <$> [a, b])) (PCon (mempty, "HNil") []) ps

    patType p (Wildcard SType) = p
    patType p t = PatType (ParPat [p]) t

    calculatePatPrecs dcls (e, xs) = postponedCheck dcls $ calcPrec (\op x y -> PCon op $ ParPat . (:[]) <$> [x, y]) (getFixity dcls . snd) e xs

longPattern = parsePat PrecAnn <&> (getPVars &&& id)
--patternAtom = parsePat PrecAtom <&> (getPVars &&& id)

telescopePat = do
    (a, b) <- fmap (getPPVars . ParPat . map snd &&& id) $ many $ uncurry f <$> hiddenTerm (parsePat PrecAtom) (parsePat PrecAtom)
    checkPattern a
    return (a, b)
  where
    f h (PParens p) = second PParens $ f h p
    f h (PatType (ParPat [p]) t) = ((h, t), p)
    f h p = ((h, Wildcard SType), p)

checkPattern :: DBNames -> BodyParser ()
checkPattern ns = lift $ tell $ pure $ 
   case [ns' | ns' <- group . sort . filter (not . null . snd) $ ns
             , not . null . tail $ ns'] of
    [] -> Nothing
    xs -> Just $ MultiplePatternVars xs

postponedCheck dcls x = do
    lift $ tell [either (\(op, op') -> Just $ OperatorMismatch (op, getFixity dcls $ snd op) (op', getFixity dcls $ snd op')) (const Nothing) x]
    return $ either (const $ error "impossible") id x

-------------------------------------------------------------------------------- pattern match compilation

data GuardTree
    = GuardNode SExp SName [ParPat] GuardTree -- _ <- _
    | Alts [GuardTree]          --      _ | _
    | GuardLeaf SExp            --     _ -> e
  deriving Show

alts (Alts xs) = concatMap alts xs
alts x = [x]

mapGT k i = \case
    GuardNode e c pps gt -> GuardNode (i k e) c {-todo: up-}pps $ mapGT (k + sum (map varPP pps)) i gt
    Alts gts -> Alts $ map (mapGT k i) gts
    GuardLeaf e -> GuardLeaf $ i k e

upGT k i = mapGT k $ \k -> up_ i k

substGT i j = mapGT 0 $ \k -> rearrangeS $ \r -> if r == k + i then k + j else if r > k + i then r - 1 else r
{-
dbfGT :: DBNames -> GuardTree -> GuardTree
dbfGT v = mapGT 0 $ \k -> dbf_ k v
-}
-- todo: clenup
compilePatts :: [(Pat, Int)] -> Either [(SExp, SExp)] SExp -> GuardTree
compilePatts ps gu = cp [] ps
  where
    cp ps' [] = case gu of
        Right e -> GuardLeaf $ rearrangeS (f $ reverse ps') e
        Left gs -> Alts
            [ GuardNode (rearrangeS (f $ reverse ps') ge) "True" [] $ GuardLeaf $ rearrangeS (f $ reverse ps') e
            | (ge, e) <- gs
            ]
    cp ps' ((p@PVar{}, i): xs) = cp (p: ps') xs
    cp ps' ((p@(PCon (si, n) ps), i): xs) = GuardNode (SVar (si, n) $ i + sum (map (fromMaybe 0 . ff) ps')) n ps $ cp (p: ps') xs
    cp ps' ((PParens p, i): xs) = cp ps' ((p, i): xs)
    cp ps' ((p@(ViewPat f (ParPat [PCon (si, n) ps])), i): xs)
        = GuardNode (SAppV f $ SVar (si, n) $ i + sum (map (fromMaybe 0 . ff) ps')) n ps $ cp (p: ps') xs
    cp _ p = error $ "cp: " ++ show p

    m = length ps

    ff PVar{} = Nothing
    ff p = Just $ varP p

    f ps i
        | i >= s = i - s + m + sum vs'
        | i < s = case vs_ !! n of
        Nothing -> m + sum vs' - 1 - n
        Just _ -> m + sum vs' - 1 - (m + sum (take n vs') + j)
      where
        i' = s - 1 - i
        (n, j) = concat (zipWith (\k j -> zip (repeat j) [0..k-1]) vs [0..]) !! i'

        vs_ = map ff ps
        vs = map (fromMaybe 1) vs_
        vs' = map (fromMaybe 0) vs_
        s = sum vs

compileGuardTrees ulend ge alts = compileGuardTree ulend SRHS ge $ Alts alts
compileGuardTrees' ge alts = foldr1 (SAppV2 $ SBuiltin "parEval" `SAppV` Wildcard SType) $ compileGuardTree id SRHS ge <$> alts

compileGuardTree :: (SExp -> SExp) -> (SExp -> SExp) -> DesugarInfo -> GuardTree -> SExp
compileGuardTree ulend lend adts t = (\x -> traceD ("  !  :" ++ ppShow x) x) $ guardTreeToCases t
  where
    guardTreeToCases :: GuardTree -> SExp
    guardTreeToCases t = case alts t of
        [] -> ulend $ SBuiltin "undefined"
        GuardLeaf e: _ -> lend e
        ts@(GuardNode f s _ _: _) -> case Map.lookup s (snd adts) of
            Nothing -> error $ "Constructor is not defined: " ++ s
            Just (Left ((casename, inum), cns)) ->
                foldl SAppV (SGlobal (debugSI "compileGuardTree2", casename) `SAppV` iterateN (1 + inum) SLamV (Wildcard (Wildcard SType)))
                    [ iterateN n SLamV $ guardTreeToCases $ Alts $ map (filterGuardTree (up n f) cn 0 n . upGT 0 n) ts
                    | (cn, n) <- cns
                    ]
                `SAppV` f
            Just (Right n) -> SGlobal (debugSI "compileGuardTree3", MatchName s)
                `SAppV` SLamV (Wildcard SType)
                `SAppV` iterateN n SLamV (guardTreeToCases $ Alts $ map (filterGuardTree (up n f) s 0 n . upGT 0 n) ts)
                `SAppV` f
                `SAppV` guardTreeToCases (Alts $ map (filterGuardTree' f s) ts)

    filterGuardTree :: SExp -> SName{-constr.-} -> Int -> Int{-number of constr. params-} -> GuardTree -> GuardTree
    filterGuardTree f s k ns = \case
        GuardLeaf e -> GuardLeaf e
        Alts ts -> Alts $ map (filterGuardTree f s k ns) ts
        GuardNode f' s' ps gs
            | f /= f'  -> GuardNode f' s' ps $ filterGuardTree (up su f) s (su + k) ns gs
            | s == s'  -> filterGuardTree f s k ns $ guardNodes (zips [k+ns-1, k+ns-2..] ps) gs
            | otherwise -> Alts []
          where
            zips is ps = zip (map (sVar "30") $ zipWith (+) is $ sums $ map varPP ps) ps
            su = sum $ map varPP ps
            sums = scanl (+) 0

    filterGuardTree' :: SExp -> SName{-constr.-} -> GuardTree -> GuardTree
    filterGuardTree' f s = \case
        GuardLeaf e -> GuardLeaf e
        Alts ts -> Alts $ map (filterGuardTree' f s) ts
        GuardNode f' s' ps gs
            | f /= f' || s /= s' -> GuardNode f' s' ps $ filterGuardTree' (up su f) s gs
            | otherwise -> Alts []
          where
            su = sum $ map varPP ps

    guardNodes :: [(SExp, ParPat)] -> GuardTree -> GuardTree
    guardNodes [] l = l
    guardNodes ((v, ParPat ws): vs) e = guardNode v ws $ guardNodes vs e

    guardNode :: SExp -> [Pat] -> GuardTree -> GuardTree
    guardNode v [] e = e
    guardNode v [w] e = case w of
        PVar _ -> {-todo guardNode v (subst x v ws) $ -} varGuardNode 0 v e
        PParens p -> guardNode v [p] e
        ViewPat f (ParPat p) -> guardNode (f `SAppV` v) p {- -$ guardNode v ws -} e
        PCon (_, s) ps' -> GuardNode v s ps' {- -$ guardNode v ws -} e

    varGuardNode v (SVar _ e) = substGT v e

compileCase ge x cs
    = SLamV (compileGuardTree id id ge $ Alts [compilePatts [(p, 0)] e | (p, e) <- cs]) `SAppV` x


-------------------------------------------------------------------------------- declaration representation

data Stmt
    = Let SIName (Maybe SExp) SExp
    | Data SIName [(Visibility, SExp)]{-parameters-} SExp{-type-} Bool{-True:add foralls-} [(SIName, SExp)]{-constructor names and types-}
    | PrecDef SIName Fixity

    -- eliminated during parsing
    | TypeFamily SIName [(Visibility, SExp)]{-parameters-} SExp{-type-}
    | Class SIName [SExp]{-parameters-} [(SIName, SExp)]{-method names and types-}
    | Instance SIName [Pat]{-parameter patterns-} [SExp]{-constraints-} [Stmt]{-method definitions-}
    | TypeAnn SIName SExp            -- intermediate
    | FunAlt SIName [((Visibility, SExp), Pat)] (Either [(SExp, SExp)]{-guards-} SExp{-no guards-})
    deriving (Show)

pattern Primitive n t <- Let n (Just t) (SBuiltin "undefined") where Primitive n t = Let n (Just t) $ SBuiltin "undefined"

instance PShow Stmt where
    pShowPrec p = \case
        Let (_, n) ty e -> text n </> "=" <+> maybe (pShow e) (\ty -> pShow e </> "::" <+> pShow ty) ty 
        Data (_, n) ps ty fa cs -> "data" <+> text n
        PrecDef (_, n) i -> "precedence" <+> text n <+> text (show i)

-------------------------------------------------------------------------------- declaration parsing

parseDef :: BodyParser [Stmt]
parseDef =
     do reserved "data" *> do
            x <- typeNS upperCase
            (npsd, ts) <- telescope (Just SType)
            t <- dbf npsd <$> parseType (Just SType)
            let mkConTy mk (nps', ts') =
                    ( if mk then Just nps' else Nothing
                    , foldr (uncurry SPi) (foldl SAppV (SGlobal x) $ downToS "a1" (length ts') $ length ts) ts')
            (af, cs) <- option (True, []) $
                 do fmap ((,) True) $ (reserved "where" >>) $ identation True $ second ((,) Nothing . dbf npsd) <$> typedIds Nothing
             <|> (,) False <$ reservedOp "=" <*>
                      sepBy1 ((,) <$> (pure <$> upperCase)
                                  <*> do  do braces $ mkConTy True . second (zipWith (\i (v, e) -> (v, dbf_ i npsd e)) [0..])
                                                <$> telescopeDataFields
                                           <|> mkConTy False . second (zipWith (\i (v, e) -> (v, dbf_ i npsd e)) [0..])
                                                <$> telescope Nothing
                             )
                             (reservedOp "|")
            mkData <$> dsInfo <*> pure x <*> pure ts <*> pure t <*> pure af <*> pure (concatMap (\(vs, t) -> (,) <$> vs <*> pure t) cs)
 <|> do reserved "class" *> do
            x <- typeNS upperCase
            (nps, ts) <- telescope (Just SType)
            cs <- option [] $ (reserved "where" >>) $ identation True $ typedIds Nothing
            return $ pure $ Class x (map snd ts) (concatMap (\(vs, t) -> (,) <$> vs <*> pure (dbf nps t)) cs)
 <|> do indentation (reserved "instance") $ typeNS $ do
            constraints <- option [] $ try "constraint" $ getTTuple <$> parseTerm PrecOp <* reservedOp "=>"
            x <- upperCase
            (nps, args) <- telescopePat
            cs <- expNS $ option [] $ reserved "where" *> identation False (dbFunAlt nps <$> funAltDef (Just lhsOperator) varId)
            pure . Instance x ({-todo-}map snd args) (dbf (nps <> [x]) <$> constraints) <$> compileFunAlts' cs
 <|> do indentation (reserved "type") $ typeNS $
            reserved "family" *> do
                x <- upperCase
                (nps, ts) <- telescope (Just SType)
                t <- dbf nps <$> parseType (Just SType)
                option {-open type family-}[TypeFamily x ts t] $ do
                    cs <- (reserved "where" >>) $ identation True $ funAltDef Nothing $ mfilter (== x) upperCase
                    -- closed type family desugared here
                    compileFunAlts (compileGuardTrees id) [TypeAnn x $ UncurryS ts t] cs
         <|> pure <$ reserved "instance" <*> funAltDef Nothing upperCase
         <|> do x <- upperCase
                (nps, ts) <- telescope $ Just (Wildcard SType)
                rhs <- dbf nps <$ reservedOp "=" <*> parseTerm PrecLam
                compileFunAlts (compileGuardTrees id)
                    [{-TypeAnn x $ UncurryS ts $ SType-}{-todo-}]
                    [FunAlt x (zip ts $ map PVar $ reverse nps) $ Right rhs]
 <|> do try "typed ident" $ (\(vs, t) -> TypeAnn <$> vs <*> pure t) <$> typedIds Nothing
 <|> fmap . flip PrecDef <$> parseFixity <*> commaSep1 rhsOperator
 <|> pure <$> funAltDef (Just lhsOperator) varId
 <|> valueDef
  where
    telescopeDataFields :: BodyParser ([SIName], [(Visibility, SExp)]) 
    telescopeDataFields = dbfi <$> commaSep ((,) Visible <$> ((,) <$> lowerCase <*> parseType Nothing))

    mkData ge x ts t af cs = Data x ts t af (second snd <$> cs): concatMap mkProj (nub $ concat [fs | (_, (Just fs, _)) <- cs])
      where
        mkProj fn
          = [ FunAlt fn [((Visible, Wildcard SType), PCon cn $ replicate (length fs) $ ParPat [PVar (mempty, "generated_name1")])] $ Right $ sVar "proj" i
            | (cn, (Just fs, _)) <- cs, (i, fn') <- zip [0..] fs, fn' == fn
            ]


parseRHS fe tok = fmap (fmap (fe *** fe) +++ fe) $ do
    fmap Left . some $ (,) <$ reservedOp "|" <*> parseTerm PrecOp <* reservedOp tok <*> parseTerm PrecLam
  <|> do
    reservedOp tok
    rhs <- parseTerm PrecLam
    f <- option id $ mkLets <$ reserved "where" <*> dsInfo <*> parseDefs
    return $ Right $ f rhs

parseDefs = identation True parseDef >>= compileFunAlts' . concat

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
            return (n, (fee, (,) (Visible, Wildcard SType) <$> [a1, mapP (dbf e') a2]))
      <|> do try "lhs" $ (,) <$> parseName <*> telescopePat <* lookAhead (reservedOp "=" <|> reservedOp "|")
    FunAlt n tss <$> parseRHS (dbf fee) "="

valueDef :: BodyParser [Stmt]
valueDef = do
    (dns, p) <- try "pattern" $ longPattern <* reservedOp "="
    checkPattern dns
    e <- parseTerm PrecLam
    ds <- dsInfo
    return $ desugarValueDef ds p e

desugarValueDef ds p e
    = FunAlt n [] (Right e)
    : [ FunAlt x [] $ Right $ compileCase ds (SGlobal n) [(p, Right $ SVar x i)]
      | (i, x) <- zip [0..] dns
      ]
  where
    dns = getPVars p
    n = mangleNames dns

mangleNames xs = (foldMap fst xs, "_" ++ intercalate "_" (map snd xs))

mkLets :: DesugarInfo -> [Stmt]{-where block-} -> SExp{-main expression-} -> SExp{-big let with lambdas; replaces global names with de bruijn indices-}
mkLets ds = mkLets' . sortDefs ds where
    mkLets' [] e = e
    mkLets' (Let n mt x: ds) e
        = SLet n (maybe id (flip SAnn . addForalls {-todo-}[] []) mt x') (substSG0 n $ mkLets' ds e)
      where
        x' = if usedS n x then SBuiltin "primFix" `SAppV` SLamV (substSG0 n x) else x
    mkLets' (x: ds) e = error $ "mkLets: " ++ show x

addForalls :: Extensions -> [SName] -> SExp -> SExp
addForalls exs defined x = foldl f x [v | v@(_, vh:_) <- reverse $ names x, snd v `notElem'` ("fromInt"{-todo: remove-}: defined), isLower vh]
  where
    f e v = SPi Hidden (Wildcard SType) $ substSG0 v e

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

sortDefs :: DesugarInfo -> [Stmt] -> [Stmt]
sortDefs ds xs = concatMap (desugarMutual ds . map snValue) $ scc snId snChildren snRevChildren nodes
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

desugarMutual _ [x] = [x]
desugarMutual ds xs = xs
{-
    = FunAlt n [] (Right e)
    : [ FunAlt x [] $ Right $ compileCase ds (SGlobal n) [(p, Right $ SVar x i)]
      | (i, x) <- zip [0..] dns
      ]
  where
    dns = getPVars p
    n = mangleNames dns
    (ps, es) = unzip [(n, e) | Let n ~Nothing ~Nothing [] e <- xs]
    tup = "Tuple" ++ show (length xs)
    e = dbf ps $ foldl SAppV (SBuiltin tup) es
    p = PCon (mempty, tup) $ map (ParPat . pure . PVar) ps
-}


------------------------------------------------------------------------ strongly connected component calculation

type Children k = k -> [k]

data Task a = Return a | Visit a

scc :: forall k . (k -> Int) -> Children k -> Children k -> [k]{-roots-} -> [[k]]
scc key children revChildren
    = filter (not . null) . uncurry (revMapWalk revChildren) . revPostOrderWalk children
  where
    revPostOrderWalk :: Children k -> [k] -> (IS.IntSet, [k])
    revPostOrderWalk children = collect IS.empty [] . map Visit where

        collect s acc [] = (s, acc)
        collect s acc (Return h: t) = collect s (h: acc) t
        collect s acc (Visit h: t)
            | key h `IS.member` s = collect s acc t
            | otherwise = collect (IS.insert (key h) s) acc $ map Visit (children h) ++ Return h: t

    revMapWalk :: Children k -> IS.IntSet -> [k] -> [[k]]
    revMapWalk children = f []
     where
        f acc s [] = acc
        f acc s (h:t) = f (c: acc) s' t
            where (s', c) = collect s [] [h]

        collect s acc [] = (s, acc)
        collect s acc (h:t)
            | not (key h `IS.member` s) = collect s acc t
            | otherwise = collect (IS.delete (key h) s) (h: acc) (children h ++ t)


------------------------------------------------------------------------

compileFunAlts' ds = fmap concat . sequence $ map (compileFunAlts (compileGuardTrees SRHS) ds) $ groupBy h ds where
    h (FunAlt n _ _) (FunAlt m _ _) = m == n
    h _ _ = False

--compileFunAlts :: forall m . Monad m => Bool -> (SExp -> SExp) -> (SExp -> SExp) -> DesugarInfo -> [Stmt] -> [Stmt] -> m [Stmt]
compileFunAlts compilegt ds xs = dsInfo >>= \ge -> case xs of
    [Instance{}] -> return []
    [Class n ps ms] -> do
        cd <- compileFunAlts' $
            [ TypeAnn n $ foldr (SPi Visible) SType ps ]
         ++ [ FunAlt n (map noTA ps) $ Right $ foldr (SAppV2 $ SBuiltin "'T2") (SBuiltin "'Unit") cstrs | Instance n' ps cstrs _ <- ds, n == n' ]
         ++ [ FunAlt n (replicate (length ps) (noTA $ PVar (debugSI "compileFunAlts1", "generated_name0"))) $ Right $ SBuiltin "'Empty" `SAppV` sLit (LString $ "no instance of " ++ snd n ++ " on ???")]
        cds <- sequence
            [ compileFunAlts'
            $ TypeAnn m (UncurryS (map ((,) Hidden) ps) $ SPi Hidden (foldl SAppV (SGlobal n) $ downToS "a2" 0 $ length ps) $ up1 t)
            : as
            | (m, t) <- ms
--            , let ts = fst $ getParamsS $ up1 t
            , let as = [ FunAlt m p $ Right {- -$ SLam Hidden (Wildcard SType) $ up1 -} $ SLet m' e $ SVar mempty 0
                      | Instance n' i cstrs alts <- ds, n' == n
                      , Let m' ~Nothing e <- alts, m' == m
                      , let p = zip ((,) Hidden <$> ps) i ++ [((Hidden, Wildcard SType), PVar (mempty, ""))]
        --              , let ic = sum $ map varP i
                      ]
            ]
        return $ cd ++ concat cds
    [TypeAnn n t] -> return [Primitive n t | snd n `notElem` [n' | FunAlt (_, n') _ _ <- ds]]
    tf@[TypeFamily n ps t] -> case [d | d@(FunAlt n' _ _) <- ds, n' == n] of
        [] -> return [Primitive n $ UncurryS ps t]
        alts -> compileFunAlts compileGuardTrees' [TypeAnn n $ UncurryS ps t] alts
    [p@PrecDef{}] -> return [p]
    fs@(FunAlt n vs _: _) -> case map head $ group [length vs | FunAlt _ vs _ <- fs] of
        [num]
          | num == 0 && length fs > 1 -> fail $ "redefined " ++ snd n ++ " at " ++ ppShow (fst n)
          | n `elem` [n' | TypeFamily n' _ _ <- ds] -> return []
          | otherwise -> return
            [ Let n
                (listToMaybe [t | TypeAnn n' t <- ds, n' == n])
                $ foldr (uncurry SLam . fst) (compilegt ge
                    [ compilePatts (zip (map snd vs) $ reverse [0.. num - 1]) gsx
                    | FunAlt _ vs gsx <- fs
                    ]) vs
            ]
        _ -> fail $ "different number of arguments of " ++ snd n ++ " at " ++ ppShow (fst n)
    x -> return x
  where
    noTA x = ((Visible, Wildcard SType), x)

dbFunAlt v (FunAlt n ts gue) = FunAlt n (map (second $ mapP (dbf v)) ts) $ fmap (dbf v *** dbf v) +++ dbf v $ gue


-------------------------------------------------------------------------------- desugar info

mkDesugarInfo :: [Stmt] -> DesugarInfo
mkDesugarInfo ss =
    ( Map.fromList $ ("'EqCTt", (Infix, -1)): [(s, f) | PrecDef (_, s) f <- ss]
    , Map.fromList $
        [hackHList (cn, Left ((caseName t, pars ty), (snd *** pars) <$> cs)) | Data (_, t) ps ty _ cs <- ss, ((_, cn), ct) <- cs]
     ++ [(t, Right $ pars $ UncurryS ps ty) | Data (_, t) ps ty _ _ <- ss]
--     ++ [(t, Right $ length xs) | Let (_, t) _ (Just ty) xs _ <- ss]
     ++ [("'Type", Right 0)]
    )
  where
    pars (UncurryS l _) = length $ filter ((== Visible) . fst) l -- todo

    hackHList ("HCons", _) = ("HCons", Left (("hlistConsCase", -1), [("HCons", 2)]))
    hackHList ("HNil", _) = ("HNil", Left (("hlistNilCase", -1), [("HNil", 0)]))
    hackHList x = x

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

type DefParser = DesugarInfo -> (Either ParseError [Stmt], [PostponedCheck])

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

parseLC :: Int -> FilePath -> String -> Either ParseError Module
parseLC fid f str
    = fst $ runParse parseModule $ parseState (FileInfo fid f str) ()

--type DefParser = DesugarInfo -> (Either ParseError [Stmt], [PostponedCheck])
runDefParser :: (MonadFix m, MonadError LCParseError m) => DesugarInfo -> DefParser -> m ([Stmt], DesugarInfo)
runDefParser ds_ dp = do

    (defs, dns, ds) <- mfix $ \ ~(_, _, ds) -> do
        let (x, dns) = dp (ds <> ds_)
        defs <- either (throwError . ParseError) return x
        return (defs, dns, mkDesugarInfo defs)

    mapM_ (maybe (return ()) throwError) dns

    return (sortDefs ds defs, ds)

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

