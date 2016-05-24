{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE BangPatterns #-}

module FreeVars where

import Data.List
import Data.Word
import Data.Int
import Data.Monoid
import Data.Maybe
import Data.Bits
import Control.Arrow
import Control.Category hiding ((.), id)
--import Debug.Trace

import LambdaCube.Compiler.Pretty

newtype Nat = Nat_ Int --Word32
  deriving (Eq, Ord, Enum)

pattern Nat i <- (fromEnum -> i)
  where Nat i =  toEnum i

instance Num Nat where
    fromInteger n = Nat $ fromInteger n
    Nat a + Nat b = Nat (a + b)
    Nat a - Nat b = Nat (a - b)
    negate (Nat b) = Nat $ negate b  -- error "negate @Nat"
    _ * _ = error "(*) @Nat"
    abs _ = error "abs @Nat"
    signum _ = error "signum @Nat"

instance PShow Nat where
    pShow (Nat i) = pShow i

data FV
--    = FV !Nat !Nat !FV
    = FV_ !Int !FV
    | FE
    deriving (Eq)

pattern FV :: Nat -> Nat -> FV -> FV
pattern FV i j x <- FV_ (splitInt -> (i, j)) x
  where FV (Nat i) (Nat j) x = FV_ (i `shiftL` 32 .|. j) x

splitInt x = (Nat $ x `shiftR` 32, Nat $ x .&. 0xffffffff)

instance PShow FV where
    pShow FE = "0"
    pShow (FV i j x) = pShow i <> "|" <> pShow j <> "|" <> pShow x

{-
newtype FV = FV_ Integer

pattern FV :: Nat -> Nat -> FV -> FV
pattern FV i j x <- FV_ (ff -> Just (x, i, j))
  where FV i j (FV_ x) = FV_ (x `shiftL` 32 .|. fromIntegral (i `shiftL` 16 .|. j))

ff 0 = Nothing
ff x = Just (FV_ (x `shiftR` 32), (fromIntegral x `shiftR` 16) .&. 0xffff, fromIntegral x .&. 0xffff)

pattern FE :: FV
pattern FE =  FV_ 0
-}

fv :: Nat -> Nat -> FV -> FV
fv 0 0 xs = xs
fv a 0 FE = FE
fv a 0 (FV b c xs) = FV (a+b) c xs
fv a b (FV 0 c xs) = FV a (b+c) xs
fv a b xs = FV a b xs

pattern VarFV i <- FV i _ _
  where VarFV i =  FV i 1 FE

del1 :: FV -> FV
del1 FE = FE
del1 (FV 0 n us) = fv 0 (n-1) us
del1 (FV n i us) = FV (n-1) i us

compact :: FV -> FV
compact xs@(FV 0 _ _) = delUnused xs
compact xs = fv 1 0 $ delUnused xs

usedFVs :: FV -> [Nat]
usedFVs = f 0
  where
    f _ FE = []
    f s (FV i a xs) = [s+i..(s+i+a)-1] ++ f (s+i+a) xs

usedFV :: Nat -> FV -> Bool
usedFV i FE = False
usedFV i (FV n l us) = i >= n && (i < l || usedFV (i - l - n) us)

downFV :: Nat -> FV -> Maybe FV
downFV i FE = Just FE
downFV i (FV n j us)
    | i < n     = Just $ FV (n - 1) j us
    | i - n < j = Nothing
    | otherwise = fv n j <$> downFV (i - n - j) us

instance Monoid FV where
    mempty = FE

    mappend x FE = x
    mappend FE x = x
    mappend (FV a b us) (FV a' b' us')
        | a + b <= a'      = fv a b             $ mappend us (FV (a' - (a + b)) b'       us')
        | a + b - a' <= b' = fv c (a + b - c)   $ mappend us (FV 0 (b' - (a + b - a'))   us')
        | a' + b' <= a     = fv a' b'           $ mappend (FV (a - (a' + b')) b       us) us'
        | otherwise        = fv c (a' + b' - c) $ mappend (FV 0 ((a + b) - (a' + b')) us) us'
      where
        c = min a a'

delFV :: FV -> FV -> FV
delFV FE x = FE
delFV (FV a b us) (FV a' b' us')
    | a' + b' <= a = fv b'       0 $ delFV (FV (a - (a' + b')) b us) us'
    | otherwise    = fv (a - a') b $ delFV us (FV 0 ((a' + b') - (a + b)) us')

-- delUnused x = delFV x x
delUnused :: FV -> FV
delUnused xs = fv 0 (altersum xs) FE
  where
    altersum FE = 0
    altersum (FV _ a cs) = a + altersum cs

compFV :: FV -> FV -> FV
compFV _ FE = FE
compFV FE x = x
compFV (FV a b xs) (FV c d ys)
    | c + d <= b  = fv (a + c) d       $ compFV (FV 0 (b - (c + d)) xs) ys
    | c <= b      = fv (a + c) (b - c) $ compFV xs (FV 0 (d - (b - c)) ys)
    | otherwise   = fv (a + b) 0       $ compFV xs (FV (c - b) d ys)

incFV :: FV -> FV
incFV = FV{-ok-} 0 1

--upFV l n = compFV (fv 0 l $ fv n 0{-buggy-} FE)
upFV :: Nat -> Nat -> FV -> FV
upFV l n FE = FE
upFV l n (FV n' l' us)
    | l  <= n'     = FV (n' + n) l' us
    | l' <= l - n' = FV n' l' $ upFV (l - n' - l') n us
    | otherwise    = FV n' (l - n') $ FV n (l' - (l - n')) us



