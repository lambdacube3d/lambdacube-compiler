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

------------------------------------------------------------ utils

iterateN i f x = iterate f x !! i

(<&>) = flip (<$>)

data Void

instance Eq Void where (==) = error "(==) @Void"
instance Show Void where show = error "show @Void"

{- used later?
-- supplementary data: data with no semantic relevance
newtype SData a = SData a
instance Show (SData a) where show _ = "SData"
instance Eq (SData a) where _ == _ = True
instance Ord (SData a) where _ `compare` _ = EQ
-}

------------------------------------------------------------ streams

-- streams with constant tails
-- invariant property: Repeat is used when possible (see cons)
data Stream a
    = Cons a (Stream a)  
    | Repeat a
    deriving (Eq, Show, Functor)    -- Functor is not proper, may break invariant

-- smart constructor to construct normal form of streams
cons b (Repeat b') | b == b' = Repeat b'
cons b x = Cons b x

-- stream head
sHead (Cons a _) = a
sHead (Repeat a) = a

-- stream tail
sTail (Cons _ a) = a
sTail (Repeat a) = Repeat a

instance Applicative Stream where
    pure a = Repeat a
    -- (<*>) is not proper, may break invariant
    Repeat f <*> Repeat a = Repeat $ f a
    x <*> y = Cons{-should be cons-} (sHead x $ sHead y) (sTail x <*> sTail y)

foldStream :: (b -> a -> a) -> (b -> a) -> Stream b -> a
foldStream f g (Cons b u) = f b (foldStream f g u)
foldStream f g (Repeat b) = g b

-- final value in the stream
limes :: Stream a -> a
limes = foldStream const id

-- replace limes by given stream
sCont :: Eq a => Stream a -> (a -> Stream a) -> Stream a
sCont as f = foldStream cons f as

-- semantics of Stream
streamToList :: Stream a -> [a]
streamToList = foldStream (:) repeat

streamToFun :: Stream a -> Int -> a
streamToFun u i = streamToList u !! i

sFromList :: Eq a => [a] -> a -> Stream a
sFromList xs b = foldr cons (Repeat b) xs

instance (Arbitrary a, Eq a) => Arbitrary (Stream a) where
    arbitrary = sFromList <$> arbitrary <*> arbitrary

-- iterate on stream
sIterate :: Eq a => (a -> a) -> a -> Stream a
sIterate f x
    | y == x = Repeat x
    | otherwise = Cons x $ sIterate f y
  where
    y = f x

sCatMaybes :: Stream (Maybe a) -> [a]
sCatMaybes = foldStream (\m s -> maybe s (:s) m) (maybe [] repeat)

---------------------------------------------------------- operations involving Boolean streams

mergeStreams :: Eq a => Stream Bool -> Stream a -> Stream a -> Stream a
mergeStreams (Cons True u)  as bs = cons (sHead as) $ mergeStreams u (sTail as) bs
mergeStreams (Cons False u) as bs = cons (sHead bs) $ mergeStreams u as (sTail bs)
mergeStreams (Repeat True)  as bs = as
mergeStreams (Repeat False) as bs = bs

sFilter :: Stream Bool -> [a] -> [a]
sFilter (Cons True  u) is = take 1 is ++ sFilter u (drop 1 is)
sFilter (Cons False u) is =              sFilter u (drop 1 is)
sFilter (Repeat True)  is = is
sFilter (Repeat False) is = []

-- sFilter for streams
-- the first stream is used when no more element can pass the filter
filterStream :: Eq a => Stream a -> Stream Bool -> Stream a -> Stream a
filterStream d (Cons True s)  as = cons (sHead as) $ filterStream d s $ sTail as
filterStream d (Cons False s) as =                   filterStream d s $ sTail as
filterStream d (Repeat True)  as = as
filterStream d (Repeat False) as = d

sOr :: Stream Bool -> Stream Bool -> Stream Bool
sOr (Cons b u) (Cons b' u') = cons (b || b') $ sOr u u'
sOr (Repeat False) u = u
sOr (Repeat True)  u = Repeat True
sOr u (Repeat False) = u
sOr u (Repeat True)  = Repeat True

prop_sOr_idemp a = sOr a a == a
prop_sOr_comm a b = sOr a b == sOr b a

dbAnd a b = not <$> sOr (not <$> a) (not <$> b)

instance Monoid (Stream Bool) where
    mempty = Repeat False
    mappend = sOr

prop_StreamBool_monoid_left  (a :: Stream Bool)     = mempty <> a == a
prop_StreamBool_monoid_right (a :: Stream Bool)     = a <> mempty == a
prop_StreamBool_monoid_assoc (a :: Stream Bool) b c = (a <> b) <> c == a <> (b <> c)

-- composition of (Stream Bool) values (by sFilter semantics)
sComp :: Stream Bool -> Stream Bool -> Stream Bool
sComp bs as = mergeStreams bs as $ Repeat False

prop_sComp a b xs = sFilter (sComp a b) xs == (sFilter b . sFilter a) xs
prop_sComp_trans a b (getNonNegative -> i) = indexTrans (sComp a b) i == (indexTrans a =<< indexTrans b i)

filterDBUsed :: Stream Bool -> Stream Bool -> Stream Bool
filterDBUsed = filterStream $ Repeat False

--prop_filterDBUsed bs = mergeStreams bs xs ys sOr b a `sComp` filterDBUsed (sOr b a) a  == a

prop_filterDBUsed a b = sOr b a `sComp` filterDBUsed (sOr b a) a  == a

compress s = filterDBUsed s s


--takeUps :: Int -> Stream Bool -> Stream Bool
--takeUps i = (`sComp` sFromList (replicate i True) False)

--prop_takeUps (getNonNegative -> n) u = streamToList (takeUps n u) == normSem (take n $ streamToList u)

--takeUps' :: Int -> Stream Bool -> Stream Bool
--takeUps' i = sComp $ sFromList (replicate i True) False

--prop_takeUps' u (getNonNegative -> n) = streamToList (takeUps' n u) == head (dropWhile ((< n) . length . filter id) (inits $ streamToList u) ++ [streamToList u])

--------------------------------------------------------------- indices

-- index of the first appearance of the limes
limesIndex :: Stream a -> Int
limesIndex = foldStream (const (+1)) (const 0)

-- indices at which the stream value is True
trueIndices :: Stream Bool -> [Int]
trueIndices s = sFilter s [0..]

prop_trueIndices (getExpDB -> u) = all (streamToFun u) $ trueIndices u

invTrueIndices :: [Int] -> Stream Bool
invTrueIndices = f 0 where
    f i [] = Repeat False
    f i (k: ks) = iterateN (k - i) (cons False) $ cons True $ f (k + 1) ks

prop_invTrueIndices (map getNonNegative . Set.toList -> ks) = trueIndices (invTrueIndices ks) == ks
prop_invTrueIndices' (getExpDB -> u) = u == invTrueIndices (trueIndices u)

-- a Boolean stream can be seen as an index transformation function for indices 0..n
indexTrans :: Stream Bool -> Int -> Maybe Int
indexTrans s i = ((Just <$> sFilter s [0..]) ++ repeat Nothing) !! i

-- inverse of indexTrans
invIndexTrans :: Stream Bool -> Int -> Maybe Int
invIndexTrans s i = case dropWhile ((< i) . snd) $ zip [0..] $ sFilter s [0..] of
    ((x, i'): _) | i' == i -> Just x
    _ -> Nothing

prop_invIndexTrans u (getNonNegative -> i) = maybe True (==i) (indexTrans u i >>= invIndexTrans u)

diffDBs as = (u, filterDBUsed u <$> as) where u = mconcat as


------------------------------------------------------------ used/unused de bruijn indices

-- which de bruijn indicies are used?
-- semantics of DBUsed is given by trueIndices
-- True: use index; False: skip index
type DBUsed = Stream Bool

-- invariant property: limes is False
-- finite indicies are used; lambda expressions are decorated with this
newtype ExpDB = ExpDB { getExpDB :: DBUsed }
    deriving (Eq, Show)

instance Arbitrary ExpDB where
    arbitrary = ExpDB . flip sFromList False <$> arbitrary

-- invariant property: limes is True
-- finite indicies are not used; good for index shifting transformations
newtype ShiftDB = ShiftDB { getShiftDB :: DBUsed }
    deriving (Eq, Show)

instance Arbitrary ShiftDB where
    arbitrary = ShiftDB . flip sFromList True <$> arbitrary

------------------------------------------------------------ de bruijn index shifting layer

-- transformation on De-Bruijn indices
--      Shift s i   ~   (fromJust . indexTrans s) <$> i
data Shift a = Shift DBUsed a
  deriving (Eq, Functor)

instance Show a => Show (Shift a) where
    show (Shift s a) = foldStream (:) (:":") ((\b -> if b then 'x' else '_') <$> s) ++ show a

strip (Shift _ x) = x

{-
instance Applicative Shift where
    pure = Shift (Repeat False)
    Shift uf f <*> Shift ua a = Shift (uf <> ua) (f a)

instance Monad Shift where
    return = pure
    Shift ux x >>= f = up ux $ f x

--prop_UExpmonadAssoc (x :: Shift ()) (apply -> f) (apply -> g) = ((x >>= f) >>= g) == (x >>= (\x' -> f x' >>= g))
-}

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

expandSubsts :: (Eq a, ShiftLike a) => Stream Bool -> Substs a -> Substs a
expandSubsts u m = streamSubsts $ (\x -> mergeStreams u x $ Repeat Nothing) $ substsStream $ up u <$> m

filterSubsts :: (Eq a, ShiftLike a) => Stream Bool -> Substs a -> Substs a
filterSubsts u m = streamSubsts $ filterStream (Repeat Nothing) u $ substsStream $ modDBUsed (filterDBUsed u) <$> m

------------------------------------------------------------ let expressions (substitutions + expression)

data Let e a = Let (Substs e) a
  deriving (Eq, Show, Functor)

instance (GetDBUsed e, GetDBUsed a) => GetDBUsed (Let e a) where
    getDBUsed (Let m e) = getDBUsed $ ShiftLet (getDBUsed e <> mconcat (Map.elems $ getDBUsed <$> m)) m e

pattern ShiftLet :: DBUsed -> Substs a -> b -> Shift (Let a b)
pattern ShiftLet u m e <- (getShiftLet -> (u, m, e)) where ShiftLet u m e = Shift (filterDBUsed (not <$> substsKeys m) u) (Let m e)

getShiftLet (Shift u (Let m e)) = (mergeStreams (substsKeys m) (Repeat True) u, m, e)

-- TODO: remove Eq a
pattern PShiftLet :: () => (Eq a, ShiftLike a, ShiftLike b) => Substs a -> b -> Shift (Let a b)
pattern PShiftLet m e <- (pushShiftLet -> Let m e) where
    PShiftLet m e = ShiftLet u (filterSubsts u m) $ modDBUsed (filterDBUsed u) e
      where
        u = getDBUsed e <> mconcat (Map.elems $ getDBUsed <$> m)

pushShiftLet (ShiftLet u m e) = Let (expandSubsts u m) (up u e)

mkLet :: (Eq a, ShiftLike a, ShiftLike b) => Substs a -> b -> Shift (Let a b)
mkLet m e = PShiftLet (Map.filterWithKey (\k _ -> streamToFun c k) m) e
  where
    -- determine which let expressions are used (garbage collection)
    -- TODO: speed this up somehow
    c = limes $ sIterate f $ getDBUsed e
      where
        f x = dbAnd ks $ x <> mconcat (sCatMaybes $ filterStream (Repeat Nothing) x us)
        ks = substsKeys m
        us = substsStream $ getDBUsed <$> m

transportIntoLet (Let m _) e = up (not <$> substsKeys m) e

----------------------------------------------------------------- MaybeLet

data MaybeLet a b c
    = HasLet (Let a (Shift c))
    | NoLet b
    deriving (Show, Eq)

type MaybeLet' a b = MaybeLet a b b

maybeLet :: (Eq a, ShiftLike a) => Shift (Let a (Shift b)) -> Shift (MaybeLet' a b)
maybeLet l@(Shift u (Let m e))
    | Map.null m = up u $ NoLet <$> e
    | otherwise  = HasLet <$> l

joinLets :: (Eq a, ShiftLike a) => MaybeLet' a (MaybeLet' a b) -> MaybeLet' a b
joinLets (NoLet e) = e
joinLets (HasLet (Let m (Shift s' (NoLet e)))) = HasLet $ Let m $ Shift s' e
joinLets (HasLet (Let m (Shift s' (HasLet (Let m' e)))))
    = HasLet $ Let (expandSubsts (not <$> substsKeys sm) m <> sm) se
      where
        (PShiftLet sm se) = Shift s' (Let m' e)

instance (GetDBUsed a, GetDBUsed b, GetDBUsed c) => GetDBUsed (MaybeLet a b c) where
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
    | ELamD (Exp e)             -- lambda with unused argument
    | ELam  (WithLet (Exp e))   -- lambda with used argument
    | EApp  (Shift (Exp e)) (Shift (Exp e)) -- application
    | RHS   e    -- marks the beginning of right hand side (parts right to the equal sign) in fuction definitions
                 -- e  is either RHSExp or Void; Void  means that this constructor cannot be used
  deriving (Eq, Show)

-- right-hand-side expression (no RHS constructor)
type RHSExp = Exp Void
-- left-hand-side expression (allows RHS constructor)
type LHSExp = Exp RHSExp

type WithLet a = MaybeLet (Shift LHSExp) a a

--------------------------------------------------------

type SExp  = Shift RHSExp
type LExp  = WithLet RHSExp
type SLExp = Shift (WithLet RHSExp) -- SLExp is *the* expression type in the user API

instance GetDBUsed RHSExp where
    getDBUsed = \case
        EApp (Shift ua a) (Shift ub b) -> ua <> ub
        ELit{} -> mempty
        EVar{} -> cons True mempty
        ELamD e -> sTail $ getDBUsed e
        ELam e  -> sTail $ getDBUsed e

instance Arbitrary RHSExp where
    arbitrary = (\(Shift _ (NoLet e)) -> e) . getSimpleExp <$> arbitrary
--    shrink = genericShrink

-- SLExp without let and shifting; for testing
newtype SimpleExp = SimpleExp { getSimpleExp :: SLExp }
    deriving (Eq, Show)

instance Arbitrary SimpleExp where
    arbitrary = fmap SimpleExp $ oneof
        [ var . getNonNegative <$> arbitrary
        , Int <$> arbitrary
        , app <$> (getSimpleExp <$> arbitrary) <*> (getSimpleExp <$> arbitrary)
        , lam <$> (getSimpleExp <$> arbitrary)
        ]

pattern SLLit l <- (getLit -> Just l) where SLLit = Shift mempty . NoLet . ELit

getLit :: SLExp -> Maybe Lit
getLit (Shift _ (NoLet (ELit l))) = Just l
getLit (Shift _ (HasLet (Let _ (Shift _ (ELit l))))) = Just l
getLit _ = Nothing

pattern Int i = SLLit (LInt i)

var :: Int -> SLExp
var i = fmap NoLet $ up_ 0 i $ mkShift EVar

prop_upVar (getNonNegative -> k) (getNonNegative -> n) (getNonNegative -> i) = up_ k n (var i) == var (if k <= i then n + i else i)
prop_downVar (getNonNegative -> k) (getNonNegative -> i) = down_ k (var i) == case compare k i of LT -> Just (var $ i-1); EQ -> Nothing; GT -> Just (var i)

lam :: SLExp -> SLExp
lam (Shift u e) = Shift (sTail u) $ if sHead u then eLam e else eLamD e
  where
    eLam (NoLet e) = NoLet $ ELam $ NoLet e
    -- TODO: improve this by let-floating
    eLam (HasLet (Let m (Shift u x))) = NoLet $ ELam (HasLet (Let m (Shift u x)))

    eLamD (NoLet e) = NoLet $ ELamD e
    -- TODO: review
    eLamD (HasLet (Let m (Shift u e))) = HasLet $ {-gc?-}Let (filterSubsts ul m) $ Shift (filterDBUsed ul u) $ ELamD e
      where
        ul = Cons False $ Repeat True

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

-- TODO
instance Arbitrary LExp where
    arbitrary = NoLet <$> arbitrary

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

prop_var (getNonNegative -> i) = case pushShift (fromLet $ var i) of
    ExpS (EVar i') -> i == i'
    _ -> False

prop_app (getSimpleExp -> a) (getSimpleExp -> b) = case pushShift $ fromLet $ app a b of
    ExpS (EApp a' b') -> (a', b') == (fromLet a, fromLet b)
    _ -> False

--prop_lam (getNonNegative -> i) = elimShift undefined undefined undefined (==i) (var i)

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
      PShiftLet m e -> case pushShift e of
        ExpS e' -> case e' of
            EApp a b -> ExpL $ EApp (fmap HasLet (mkLet m a)) (fmap HasLet (mkLet m b))
            ELit i -> ExpL $ ELit i
            EVar i -> case Map.lookup i m of
                Nothing -> ExpL $ EVar i
                Just x -> pushLet' $ lets m $ NoLet <$> x
            LHS_ a b -> error "efun"
--            Delta_ f -> ExpL $ Delta_ f

---------------------------------------------------------

hnf :: SLExp -> ExpL
hnf e = case pushLet' e of
    (ExpL (LHS_ "add" [_, _])) -> error "ok"
    x@(ExpL (EApp a b)) -> case hnf a of
        ExpL (ELam a) -> hnf $ let1 0 b a
        ExpL (LHS_ n acc) -> hnf $ LHS n (_ b: acc)
        _ -> x
    x -> x

{- pattern synonyms

-   BReduce e : at least one step of beta reduction, e is the result
-   Lit: a literal, after all kind of possible reductions
-   App
    -   after reduction
    -   before reduction

-}

-----------------------------------------------------------------------------------
-}
idE :: SLExp
idE = lam $ var 0
{-
add :: SLExp
add = NoLet <$> mkShift (LHS "add" []) -- $ ELam $ NoLet $ ELam $ NoLet $ Delta f)
  where
    f [Int i, Int j] = Int $ i + j

example1 = app (idE) (Int 10)

example2 = app (app add (Int 10)) (Int 5)


--     = fun name args  $ \x -> \y -> rhs e


----------------------------------------------------------------- run all tests
-}
return []
runTests = $quickCheckAll

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
        -   lam, pi, app, var, lit, ...
    -   eliminations

-   intergrate into the compiler
-}

