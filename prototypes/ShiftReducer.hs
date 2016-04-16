{-# language ScopedTypeVariables #-}
{-# language LambdaCase #-}
{-# language TypeOperators #-}
{-# language TypeFamilies #-}
{-# language ViewPatterns #-}
{-# language PatternGuards #-}
{-# language PatternSynonyms #-}
{-# language RankNTypes #-}
{-# language DataKinds #-}
{-# language KindSignatures #-}
{-# language GADTs #-}
{-# language DeriveFunctor #-}
{-# language DeriveGeneric #-}
{-# language DefaultSignatures #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language TemplateHaskell #-}  -- for testing
{-# language NoMonomorphismRestriction #-}
module ShiftReducer where

import Data.Monoid
import Data.Maybe
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad
import Control.Arrow hiding (app)
import Test.QuickCheck
import Test.QuickCheck.Function
import GHC.Generics
import Debug.Trace

import Stream

------------------------------------------------------------ de bruijn index shifting layer

-- transformation on De-Bruijn indices
--      Shift s i   ~   (fromJust . indexTrans s) <$> i
data Shift a = Shift DBUsed a
  deriving (Eq, Functor)

instance Show a => Show (Shift a) where
    showsPrec p (Shift s a) rest = parens (p > 0) (foldStream (:) (:":") ((\b -> if b then 'x' else '_') <$> s) ++ show a) ++ rest

parens True s = "(" ++ s ++ ")"
parens False s = s

strip (Shift _ x) = x

-----------------------------

class GetDBUsed a where
    getDBUsed :: a -> DBUsed

instance GetDBUsed ExpDB where
    getDBUsed = getExpDB

instance GetDBUsed (Shift a) where
    getDBUsed (Shift u _) = u

mkShift :: GetDBUsed a => a -> Shift a
mkShift e = Shift (getDBUsed e) e

instance (Arbitrary a, GetDBUsed a) => Arbitrary (Shift a) where
    arbitrary = upToShift <$> arbitrary


----------------

-- for testing
-- generate a DBUsed with a given number of used indicies
data Up a = Up DBUsed a
    deriving (Show)

upToShift :: GetDBUsed a => Up a -> Shift a
upToShift (Up u x) = Shift (sComp u $ getDBUsed x) x

instance (Arbitrary a, GetDBUsed a) => Arbitrary (Up a) where
    arbitrary = do
        f <- arbitrary
        u <- flip sFromList True . concatMap ((++ [True]) . (`replicate` False) . getNonNegative)
                <$> replicateM (limesIndex $ getDBUsed f) arbitrary
        return $ Up u f

class GetDBUsed a => ShiftLike a where
    setDBUsed :: DBUsed -> a -> a

modDBUsed :: ShiftLike a => (DBUsed -> DBUsed) -> a -> a
modDBUsed f e = setDBUsed (f $ getDBUsed e) e

up :: ShiftLike a => DBUsed -> a -> a
up x = modDBUsed (sComp x)

down :: ShiftLike a => DBUsed -> a -> Maybe a
down a e = case filterDBUsed (not <$> a) (getDBUsed e) of
    Repeat False -> Just $ modDBUsed (filterDBUsed a) e
    _ -> Nothing

up_ :: ShiftLike a => Int -> Int -> a -> a
up_ i j = up (iterateN i (cons True) $ iterateN j (cons False) (Repeat True))

down_ :: ShiftLike a => Int -> a -> Maybe a
down_ i = down (iterateN i (cons True) $ cons False (Repeat True))

instance ShiftLike (Shift a) where
    setDBUsed x (Shift _ a) = Shift x a

prop_upDown (Up u ((`Shift` ()) . getExpDB -> e))
    = down u (up u e) == Just e
prop_downNothing ((`Shift` ()) . getExpDB -> e) (getNonNegative -> i)
    = if i `elem` trueIndices (getDBUsed e) then down_ i e == Nothing else isJust (down_ i e)

------------------------------------------------------------ substitutions

type Substs a = Map Int a

substsKeys :: Substs a -> Stream Bool
substsKeys = invTrueIndices . Map.keys

substsStream :: Eq a => Substs a -> Stream (Maybe a)
substsStream = elemsUps . Map.toList

elemsUps :: Eq a => [(Int, a)] -> Stream (Maybe a)
elemsUps = f 0 where
    f i [] = Repeat Nothing
    f i ((k, a): ks) = iterateN (k - i) (cons Nothing) $ cons (Just a) $ f (k + 1) ks

streamSubsts :: Stream (Maybe a) -> Substs a
streamSubsts = Map.fromDistinctAscList . upsElems

upsElems :: Stream (Maybe a) -> [(Int, a)]
upsElems = f 0 where
    f _ (Repeat Nothing) = []
    f i (Cons Nothing u) = f (i+1) u
    f i (Cons (Just a) u) = (i, a): f (i+1) u

-- TODO: remove Eq constraint
expandSubsts :: (Eq a, ShiftLike a) => Stream Bool -> Substs a -> Substs a
expandSubsts u m = streamSubsts $ (\x -> mergeStreams u x $ Repeat Nothing) $ substsStream $ up u <$> m

-- TODO: remove Eq constraint
filterSubsts :: (Eq a, ShiftLike a) => Stream Bool -> Substs a -> Substs a
filterSubsts u m = streamSubsts $ filterStream (Repeat Nothing) u $ substsStream $ modDBUsed (filterDBUsed u) <$> m

------------------------------------------------------------ let expressions (substitutions + expression)

{-
In let expressions, de bruijn indices of variables can be arbitrary, because
they cannot be seen from outside:

let V 3 = 'c' in (V 4) (V 3)    ===    let V 4 = 'c' in (V 3) (V 4)    ===    let (V 0) = 'c' in (V 4) (V 0)

So all let de bruinj indices could be numbered 0, 1, ..., n.

Question: is it a good idea to store lets in this normal form?
-}

data Let e a = Let (Substs e) a
  deriving (Eq, Show, Functor)

instance (GetDBUsed e, GetDBUsed a) => GetDBUsed (Let e a) where
    getDBUsed (Let m e) = getDBUsed $ ShiftLet (getDBUsed e <> mconcat (Map.elems $ getDBUsed <$> m)) m e

-- let with outer shifts
-- handles let keys removal / addition
pattern ShiftLet :: DBUsed -> Substs a -> b -> Shift (Let a b)
pattern ShiftLet u m e <- (getShiftLet -> (u, m, e)) where ShiftLet u m e = Shift (filterDBUsed (not <$> substsKeys m) u) (Let m e)

getShiftLet (Shift u (Let m e)) = (mergeStreams (substsKeys m) (Repeat True) u, m, e)

-- push shift into let
-- TODO: remove Eq a
pattern PushedShiftLet :: () => (Eq a, ShiftLike a, ShiftLike b) => Substs a -> b -> Shift (Let a b)
pattern PushedShiftLet m e <- (pushShiftLet -> Let m e) where
    PushedShiftLet m e = ShiftLet u (filterSubsts u m) $ modDBUsed (filterDBUsed u) e
      where
        u = getDBUsed e <> mconcat (Map.elems $ getDBUsed <$> m)

pushShiftLet (ShiftLet u m e) = Let (expandSubsts u m) (up u e)

mkLet :: (Eq a, ShiftLike a, ShiftLike b) => Substs a -> b -> Shift (Let a b)
mkLet m e = PushedShiftLet (Map.filterWithKey (\k _ -> streamToFun (transitiveClosure (getDBUsed <$> m) $ getDBUsed e) k) m) e

-- determine which let expressions are used (kinf of garbage collection)
-- TODO: speed this up somehow
transitiveClosure m e = limes $ sIterate f e
  where
    f x = dbAnd ks $ x <> mconcat (sCatMaybes $ filterStream (Repeat Nothing) x us)
    ks = substsKeys m
    us = substsStream m

{- TODO
prop_mkLet_idempotent = l == f l
  where
    l = mkLet m e
    f (Let m e) = mkLet m e
-}

mkLet_test1 = mkLet m e == Shift s (Let m' e')
  where
    e = f [0]
    m = Map.fromList
        [ (0,  f [10])
        , (2,  f [])
        , (3,  f [])
        , (10, f [0, 2])
        ]

    s = invTrueIndices [7]
    e' = f [0]
    m' = Map.fromList
        [ (0,  f [2])
        , (1,  f [])
        , (2,  f [0, 1])
        ]

    f x = Shift (invTrueIndices x) ()

transportIntoLet (Let m _) e = up (not <$> substsKeys m) e

----------------------------------------------------------------- MaybeLet

data MaybeLet a b
    = HasLet (Let (Shift a) (Shift b))
    | NoLet b
    deriving (Show, Eq, Functor)

--pattern MLet :: Let -> MaybeLet a b
--pattern MLet 

maybeLet :: Shift (Let (Shift a) (Shift b)) -> Shift (MaybeLet a b)
maybeLet l@(Shift u (Let m e))
    | Map.null m = up u $ NoLet <$> e
    | otherwise  = HasLet <$> l

joinLets :: (Eq a) => MaybeLet a (MaybeLet a b) -> MaybeLet a b
joinLets (NoLet e) = e
joinLets (HasLet (Let m (Shift s' (NoLet e)))) = HasLet $ Let m $ Shift s' e
joinLets (HasLet (Let m (Shift s' (HasLet (Let m' e)))))
    = HasLet $ Let (expandSubsts (not <$> substsKeys sm) m <> sm) se
      where
        (PushedShiftLet sm se) = Shift s' (Let m' e)

-- TODO: test joinLets

instance (GetDBUsed b) => GetDBUsed (MaybeLet a b) where
    getDBUsed = \case
        NoLet a  -> getDBUsed a
        HasLet x -> getDBUsed x

-- used in testing
fromLet (Shift u (NoLet e)) = Shift u e

------------------------------------------------------------ literals

data Lit
    = LInt Int
    | LChar Char
    -- ...
    deriving (Eq)

instance Show Lit where
    show = \case
        LInt i -> show i
        LChar c -> show c

------------------------------------------------------------ expressions

data Exp e
    = ELit  Lit
    | EVar
    | ELam  (WithLet (Exp e))   -- lambda with used argument
--    | ELamD (Exp e)             -- lambda with unused argument (optimization?)
    | EApp  (Shift (Exp e)) (Shift (Exp e)) -- application
    | Delta String [SLExp{-?-}]
    | RHS   e    -- marks the beginning of right hand side (parts right to the equal sign) in fuction definitions
                 -- e  is either RHSExp or Void; Void  means that this constructor cannot be used
  deriving (Eq, Show)

-- right-hand-side expression (no RHS constructor)
type RHSExp = Exp Void
-- left-hand-side expression (allows RHS constructor)
type LHSExp = Exp RHSExp

rhs :: LHSExp -> RHSExp
rhs (RHS x) = x

lhs :: RHSExp -> LHSExp
lhs = RHS
{-\case
    ELit l -> ELit l
    EVar -> EVar
--    ELamD e -> ELamD $ lhs e
    ELam l -> ELam $ lhs <$> l
    EApp a b -> EApp (lhs <$> a) (lhs <$> b)
    RHS _   -> error "lhs: impossible"
-}
type WithLet a = MaybeLet LHSExp a

--------------------------------------------------------

type SExp  = Shift RHSExp
type LExp  = WithLet RHSExp
type SLExp = Shift (WithLet RHSExp) -- SLExp is *the* expression type in the user API

-- TODO
instance Arbitrary LExp where
    arbitrary = NoLet <$> arbitrary

instance GetDBUsed RHSExp where
    getDBUsed = \case
        EApp (Shift ua a) (Shift ub b) -> ua <> ub
        ELit{} -> mempty
        EVar{} -> cons True mempty
--        ELamD e -> sTail $ getDBUsed e
        ELam e  -> sTail $ getDBUsed e
        Delta _ xs -> mconcat $ getDBUsed <$> xs

instance Arbitrary RHSExp where
    arbitrary = (\(Shift _ (NoLet e)) -> e) . getSimpleExp <$> arbitrary
--    shrink = genericShrink

-- SLExp without let and shifting; for testing
newtype SimpleExp = SimpleExp { getSimpleExp :: SLExp }
    deriving (Eq, Show)

instance Arbitrary SimpleExp where
    arbitrary = fmap SimpleExp $ oneof
        [ Var . getNonNegative <$> arbitrary
        , Int <$> arbitrary
        , app <$> (getSimpleExp <$> arbitrary) <*> (getSimpleExp <$> arbitrary)
        , lam <$> (getSimpleExp <$> arbitrary)
        ]

-- does no reduction
pattern SLLit :: Lit -> SLExp
pattern SLLit l <- (getLit -> Just l) where SLLit = Shift mempty . NoLet . ELit

getLit :: SLExp -> Maybe Lit
getLit (Shift (Repeat False) (NoLet (ELit l))) = Just l
getLit (Shift _ (HasLet (Let _ (Shift _ (ELit l))))) = error "getLit: impossible: literals does not depend on variables"
getLit _ = Nothing

pattern Int i = SLLit (LInt i)

-- TODO: should it reduce on pattern match?
pattern Var :: Int -> SLExp
pattern Var i <- (getVar -> Just i) where Var i = fmap NoLet $ up_ 0 i $ mkShift EVar

getVar (Shift u (NoLet EVar)) = Just $ fromMaybe (error "getVar: impossible") $ listToMaybe $ trueIndices u
getVar (Shift _ (HasLet (Let _ (Shift _ _)))) = error "getVar: TODO"
getVar _ = Nothing

prop_Var (getNonNegative -> i) = case (Var i) of Var j -> i == j

prop_upVar (getNonNegative -> k) (getNonNegative -> n) (getNonNegative -> i) = up_ k n (Var i) == Var (if k <= i then n + i else i)
prop_downVar (getNonNegative -> k) (getNonNegative -> i) = down_ k (Var i) == case compare k i of LT -> Just (Var $ i-1); EQ -> Nothing; GT -> Just (Var i)

lam :: SLExp -> SLExp
lam (Shift u e) = Shift (sTail u) $ eLam e -- TODO: if sHead u then eLam e else eLamD e
  where
    -- TODO: improve this by let-floating
    eLam = NoLet . ELam
{-
    eLam (NoLet e) = NoLet $ ELam $ NoLet e
    eLam (HasLet (Let m e)) = NoLet $ ELam (HasLet (Let m{-(filterSubsts (not <$> c) m)-} e))
      where
        c = transitiveClosure (getDBUsed <$> m) $ Cons True $ Repeat False
-}

{-
    eLamD (NoLet e) = NoLet $ ELamD e
    -- TODO: review
    eLamD (HasLet (Let m (Shift u e))) = HasLet $ {-gc?-}Let (filterSubsts ul m) $ Shift (filterDBUsed ul u) $ ELamD e
      where
        ul = Cons False $ Repeat True
-}
-- test without let floating, modify it after let floating is implemented
lam_test_let = lam (lets_ m e) == Shift s (NoLet $ ELam $ HasLet $ Let m' $ Shift u e')
  where
    e = Var 0 `app` Var 1 `app` Var 10
    m = Map.fromList
        [ (0,  Var 13)
        , (2,  Var 1)
        , (3,  Var 1)       -- garbage
        , (10, Var 0 `app` Var 2)
        ]

    s = invTrueIndices [6, 9]
    (Shift u (NoLet e')) = Var 0 `app` Var 1 `app` Var 3
    m' = Map.fromList
        [ (0,  f $ Var 4)
        , (2,  f $ Var 1)
        , (3,  f $ Var 0 `app` Var 2)
        ]

    f (Shift u (NoLet e)) = Shift u $ lhs e

app :: SLExp -> SLExp -> SLExp
app (Shift ua (NoLet a)) (Shift ub (NoLet b))
    = Shift u $ NoLet $ EApp (Shift (filterDBUsed u ua) a) (Shift (filterDBUsed u ub) b)
  where u = ua <> ub
app x y = f x y
  where
    f :: SLExp -> SLExp -> SLExp
    f (Shift ula la) (Shift ulb (HasLet lb)) = g app ula la ulb lb
    f (Shift ulb (HasLet lb)) (Shift ula la) = g (flip app) ula la ulb lb

    g :: (SLExp -> SLExp -> SLExp) -> DBUsed -> LExp -> DBUsed -> Let (Shift LHSExp) (Shift RHSExp) -> SLExp
    g app ula la ulb lb
        = up u $ lets {-Shift u $-}
    --      app (Shift ula' la) (Shift ulb' lb)
    --      app (Shift ula' la) (Let mb eb)
            mb {-HasLet $ Let mb $-} $
                app xa (fmap NoLet eb)
      where
        (u, [ula', ulb']) = diffDBs [ula, ulb]
        lb'@(Let mb eb) = pushShiftLet $ Shift ulb' lb
        xa = transportIntoLet lb' $ Shift ula' la

lets :: Substs (Shift LHSExp) -> SLExp -> SLExp
lets m e = fmap joinLets $ maybeLet $ mkLet m e

-- TODO: handle lets inside
lets_ :: Substs SLExp -> SLExp -> SLExp
lets_ m e = lets (f <$> m) e
  where
    f :: SLExp -> Shift LHSExp
    f (Shift u (NoLet e)) = Shift u $ lhs e

let1 :: Int -> SLExp -> SLExp -> SLExp
let1 i (Shift u (NoLet x)) = lets $ Map.singleton i $ Shift u $ RHS x
let1 i (Shift u (HasLet l)) = lets $ m <> Map.singleton i' (RHS <$> e)
  where
    (Let m e) = pushShiftLet $ Shift u l
    (Just i') = indexTrans (not <$> substsKeys m) i

---------------------------------------------------------
{-
newtype ExpS = ExpS (Exp Int ExpS (MaybeLet SExp ExpS RHSExp) SExp)
  deriving (Eq, Show)

pushShift :: SExp -> ExpS
pushShift (Shift u e) = ExpS $ case e of
    EApp a b -> EApp (up u a) (up u b)
    ELit i -> ELit i
    EVar{} -> EVar $ fromJust $ indexTrans u 0
    ELamD e -> ELamD $ pushShift $ Shift (cons False u) e
    ELam (NoLet e) -> ELam $ NoLet $ pushShift $ Shift (cons True u) e
    LHS a b -> LHS_ a (up u <$> b) -- ??? $ SData (pushShift $ Shift u c)
--    Delta x -> Delta_ $ SData x

prop_Var (getNonNegative -> i) = case pushShift (fromLet $ Var i) of
    ExpS (EVar i') -> i == i'
    _ -> False

prop_app (getSimpleExp -> a) (getSimpleExp -> b) = case pushShift $ fromLet $ app a b of
    ExpS (EApp a' b') -> (a', b') == (fromLet a, fromLet b)
    _ -> False

--prop_lam (getNonNegative -> i) = elimShift undefined undefined undefined (==i) (Var i)

--prop_pushShift (Shift u e) =

---------------------------------------------------------

newtype ExpL = ExpL (Exp Int SLExp SLExp SLExp)
  deriving (Eq, Show)
{-
pushLet :: LExp -> ExpL
pushLet (NoLet e) = ExpL $ case e of
    EInt i -> EInt_ i
    EApp a b -> EApp (NoLet <$> a) (NoLet <$> b)
    EVar{} -> EVar 0
--    ELam a -> ELam $ mkShift a
    ELamD a -> ELamD $ NoLet <$> mkShift a
pushLet (HasLet (Let m e)) = ExpL $ case pushShift e of
    ExpS e' -> case e' of
        EApp a b -> EApp (fmap HasLet (mkLet m a)) (fmap HasLet (mkLet m b))
        EInt_ i -> EInt_ i
        EVar i -> EVar i
-}
pushLet' :: SLExp -> ExpL
pushLet' (Shift u l) = case l of
    NoLet e -> {-case pushShift (Shift u e) of
      ExpS e -> -} ExpL $ case e of
        ELit i -> ELit i
        EApp a b -> EApp (NoLet <$> up u a) (NoLet <$> up u b)
        EVar () -> EVar $ fromJust $ indexTrans u 0
        ELam a -> ELam $ Shift (cons True u) a
    --    ELamD a -> ELamD $ NoLet a
        LHS a b -> LHS_ a ((fmap NoLet . up u) <$> b)
    HasLet l -> case Shift u l of
      PushedShiftLet m e -> case pushShift e of
        ExpS e' -> case e' of
            EApp a b -> ExpL $ EApp (fmap HasLet (mkLet m a)) (fmap HasLet (mkLet m b))
            ELit i -> ExpL $ ELit i
            EVar i -> case Map.lookup i m of
                Nothing -> ExpL $ EVar i
                Just x -> pushLet' $ lets m $ NoLet <$> x
            LHS_ a b -> error "efun"
--            Delta_ f -> ExpL $ Delta_ f

---------------------------------------------------------
-}
{-
  TODO: add work only for normal form literals on expressions without lets
  NEXT: this should work: add (add 1 1) (add 2 2)
-}
hnf :: SLExp -> SLExp
hnf exp@(Shift u (NoLet e)) = case e of
    EApp f x -> up u $ apl (NoLet <$> f) (NoLet <$> x)
    Delta "add" [Int i, Int j] -> Int $ j + i
    Delta "whenLE" [Int x, f, Int y] -> if y < x then hnf $ f `app` Int y else Int y
    Delta{} -> exp
    ELam{} -> exp
    ELit{} -> exp
    x -> error $ "hnf: " ++ show x
hnf exp@(Shift u (HasLet (Let m e'@(Shift u' e)))) = case NoLet <$> e' of
    Var i -> case Map.lookup i m of
        Just x -> hnf $ up u $ maybeLet $ mkLet m $ rhs <$> x 
    Shift u' (NoLet (EApp a b)) -> apl (maybeLet $ mkLet m $ up u' a) (maybeLet $ mkLet m $ up u' b)
    x -> error $ "hnf2: " ++ show x

apl f x = case hnf f of
    Shift u' (NoLet a_) -> case a_ of
        ELam a -> hnf $ let1 0 x $ Shift (Cons (sHead $ getDBUsed a) u') a     -- beta reduction
        Delta s xs | length xs < arity s  -> hnf $ Shift u' $ NoLet $ Delta s (hnf x: xs)
        x -> error $ "apl: " ++ show x
  where
    arity "add" = 2
    arity "whenLE" = 3


{-
hnf e = case pushLet' e of
    (ExpL (LHS_ "add" [_, _])) -> error "ok"
    x@(ExpL (EApp a b)) -> case hnf a of
        ExpL (ELam a) -> hnf $ let1 0 b a       -- beta reduction
--        ExpL (LHS_ n acc) -> hnf $ LHS n (_ b: acc)
        _ -> x
    x -> x
-}
{- pattern synonyms

-   BReduce e : at least one step of beta reduction, e is the result
-   Lit: a literal, after all kind of possible reductions
-   App
    -   after reduction
    -   before reduction

-}

-----------------------------------------------------------------------------------

idE :: SLExp
idE = lam $ Var 0

add :: SLExp
add = NoLet <$> mkShift (Delta "add" [])

whenLE = NoLet <$> mkShift (Delta "whenLE" [])

suc :: SLExp
suc = lam $ add `app` Int 1 `app` Var 0

double :: SLExp
double = lam $ add `app` Var 0 `app` Var 0

--------

id_test = hnf (idE `app` Int 10) == Int 10

add_test = hnf (add `app` Int 10 `app` Int 20) == Int 30

succ_test = hnf (suc `app` Int 10) == Int 11

double_test = hnf (iterateN 5 (double `app`) $ Int 1) == Int 32

mutual_test = hnf $ lets_ (Map.fromList [ (0, lam $ Var 2 `app` Var 0)
                                        , (1, lam $ whenLE `app` Int 100 `app` Var 1 `app` Var 0)
                                        ])
                        $ Var 0 `app` Int 0

----------------------------------------------------------------- run all tests

return []
runTests | mkLet_test1 && id_test && add_test && succ_test && double_test = $quickCheckAll

{-
TODO

-   primes example running ~ 3 days
-   speed up eliminators with caching ~ 3 days
-   write performance tests (primes + ?)
-   speed up Boolean streams with compression ~ 3 days
-   gc speedup ~ 2 days
-   check that all operations is available and efficient ~ 1 day
    -   up, down
    -   subst
    -   constructions
        -   lam, pi, app, Var, lit, ...
    -   eliminations

-   intergrate into the compiler
-}

