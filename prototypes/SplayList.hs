{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module SplayList
    ( SplayList (..)
    , pattern Cons, pattern Snoc
    , Measured (..)
    , split
    ) where

import Prelude hiding (null)
import Control.Applicative hiding (empty)
import Control.Monad
import Control.Arrow

import Data.Function
import Data.Data
import Data.Maybe
import Data.Monoid

import FreeVars

------------------------------------------------------------------------

data SplayList a
    = Nil
    | Singleton a
    | Append_ !(Measure a) !FV (SplayList a) (SplayList a)
    deriving (Typeable)

deriving instance (Show a, Show (Measure a)) => Show (SplayList a)

toList = go []
  where
    go i    Nil = i
    go i   (Singleton a) = a: i
    go acc (Append l r) = go (go acc r) l

instance (Measured a, Eq a)  => Eq (SplayList a)  where (==)    = (==)    `on` toList
instance (Measured a, Ord a) => Ord (SplayList a) where compare = compare `on` toList

--------------------------------------------

class (HasFV a, Measure a ~ Nat) => Measured a where
    type Measure a :: *
    measure :: a -> Measure a

instance Measured a => Monoid (SplayList a) where
    mempty  = Nil
    Nil `mappend` ys  = ys
    xs  `mappend` Nil = xs
    xs  `mappend` ys  = Append xs ys

instance (Measured a, HasFV a) => HasFV (SplayList a) where
    fvLens = \case
        Nil -> lConst Nil
        Singleton (fvLens -> (s, f)) -> (s, Singleton . f)
        Append_ n s l r -> (s, \s -> Append_ n s l r)

instance (Measured a) => Measured (SplayList a) where
    type Measure (SplayList a) = Measure a
    measure Nil = mempty
    measure (Singleton a) = measure a
    measure (Append_ n _ _ _) = n

--------------------------------------------

getAppend (Append_ _ s x@(fvLens -> ~(ux, x')) z@(fvLens -> ~(uz, z')))
    = Just (x' $ fv 0 (measure z) s `expand` ux, z' $ s `expand` uz)
getAppend _ = Nothing

pattern Append :: () => Measured a => SplayList a -> SplayList a -> SplayList a
pattern Append l r <- (getAppend -> Just (l, r))
  where Append x@(fvLens -> (ux, x')) z@(fvLens -> (uz, z')) = Append_ us s (x' ux') (z' uz')
          where
            SFV us s = SFV (measure x) ux <> SFV mz uz

            mz = measure z

            ux' = fv 0 mz s `primContract` ux
            uz' = s `primContract` uz

pattern Cons a as <- (viewl -> Just (a, ascendL -> as))
  where Cons a as = Singleton a <> as

viewl Nil = Nothing
viewl xs = Just $ go [] xs
  where
    go xs (Singleton a) = (a, xs)
    go xs (Append l r)  = go (r: xs) l

ascendL [] = Nil
ascendL (x: xs) = go x xs
  where
    go !a = \case
        [] -> a
        b: [] -> a `app` b
        b: c: xs -> go (a `app` Append b c) xs

    Append a b `app` c = Append a (Append b c)
    a `app` b = Append a b

pattern Snoc as a <- (viewr -> Just (a, ascendR -> as))
  where Snoc as a = as <> Singleton a

viewr Nil = Nothing
viewr xs = Just $ go [] xs
  where
    go xs (Singleton a) = (a, xs)
    go xs (Append l r) = go (l: xs) r

ascendR [] = Nil
ascendR (x: xs) = go x xs
  where
    go !c = \case
        [] -> c
        a: [] -> a `app` c
        b: a: xs -> go (Append a b `app` c) xs

    a `app` Append b c = Append (Append a b) c
    a `app` b = Append a b

-- | Split a list at the point where the predicate on the measure changes from False to True.
split :: Measured a => (Nat -> Bool) -> SplayList a -> (SplayList a, SplayList a)
split _ Nil = (Nil, Nil)
split p xs
    | p mempty       = (Nil, xs)
    | p (measure xs) = go mempty [] [] xs
    | otherwise      = (xs, Nil)
  where
    go m ls rs = \case
        Append l r
            | p n       -> go m ls (r: rs) l
            | otherwise -> go n (l: ls) rs r
          where
            n = m <> measure l

        xs  | p (m <> measure xs) -> (ascendR ls, ascendL $ xs: rs)
            | otherwise           -> (ascendR $ xs: ls, ascendL rs)

