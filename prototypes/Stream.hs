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
module Stream where

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
limes = foldStream (flip const) id

prop_limes (getNonNegative -> n) = limes (sFromList [0..n-1] n) == n

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

------------------------------------------------------------------

return []
main = $quickCheckAll

