{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
module IndexList where

import Prelude hiding (length, (!!))
import Control.Arrow

data List a
    = Nil
    | Z !(List (a, a))
    | S a !(List (a, a))
    deriving Show

z Nil = Nil
z v = Z v

length :: List a -> Int
length Nil = 0
length (Z v) = 2 * length v
length (S _ v) = 1 + 2 * length v

(!!) :: List a -> Int -> a
S x v !! 0 = x
S x v !! i = Z v !! (i-1)
Z v   !! i
    | even i    = fst $ v !! (i `div` 2)
    | otherwise = snd $ v !! (i `div` 2)
Nil   !! i = error $ "index out of bounds: " ++ show i

update :: List a -> Int -> (a -> a) -> List a
update (S x v) 0 f = S (f x) v
update (S x v) i f
    | even (i-1) = S x $ update v ((i-1) `div` 2) (first f)
    | otherwise  = S x $ update v ((i-1) `div` 2) (second f)
update (Z v) i f
    | even i    = Z $ update v (i `div` 2) (first f)
    | otherwise = Z $ update v (i `div` 2) (second f)
update Nil i _ = error $ "update index out of bounds: " ++ show i

pattern Cons :: a -> List a -> List a
pattern Cons a v <- (getCons -> Just (a, v))
  where Cons x Nil = S x Nil
        Cons x (Z v) = S x v
        Cons x (S y v) = Z (Cons (x, y) v)

getCons :: List a -> Maybe (a, List a)
getCons Nil = Nothing
getCons (S x v) = Just (x, z v)
getCons (Z v) = (\((x, y), v) -> (x, S y v)) <$> getCons v

pattern List :: [a] -> List a
pattern List a <- (fromList -> a)
  where List = foldr Cons Nil

fromList :: List a -> [a]
fromList (Cons x xs) = x: fromList xs
fromList Nil = []


