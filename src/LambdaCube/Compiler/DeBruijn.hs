{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module LambdaCube.Compiler.DeBruijn where

import Data.Monoid
import Data.Bits
import Control.Arrow hiding ((<+>))

import LambdaCube.Compiler.Utils

-------------------------------------------------------------------------------- rearrange De Bruijn indices

class Rearrange a where
    rearrange :: Int{-level-} -> RearrangeFun -> a -> a

data RearrangeFun
    = RFSubst Int Int
    | RFMove Int
    | RFUp Int
    deriving Show

rearrangeFun = \case
    RFSubst i j -> \k -> if k == i then j else if k > i then k - 1 else k
    RFMove i -> \k -> if k == i then 0 else k + 1
    RFUp n -> \k -> if k >= 0 then k + n else k

rSubst :: Rearrange a => Int -> Int -> a -> a
rSubst i j = rearrange 0 $ RFSubst i j

-- move index to 0
rMove :: Rearrange a => Int -> Int -> a -> a
rMove i l = rearrange l $ RFMove i

rUp :: Rearrange a => Int -> Int -> a -> a
rUp n l = rearrange l $ RFUp n

up1_ :: Rearrange a => Int -> a -> a
up1_ = rUp 1

up n = rUp n 0
up1 = up1_ 0

instance Rearrange a => Rearrange [a] where
    rearrange l f = map $ rearrange l f

instance (Rearrange a, Rearrange b) => Rearrange (Either a b) where
    rearrange l f = rearrange l f +++ rearrange l f

instance (Rearrange a, Rearrange b) => Rearrange (a, b) where
    rearrange l f = rearrange l f *** rearrange l f

instance Rearrange Void where
    rearrange _ _ = elimVoid

------------------------------------------------------- set of free variables (implemented with bit vectors)

newtype FreeVars = FreeVars Integer

instance Monoid FreeVars where
    mempty = FreeVars 0
    FreeVars a `mappend` FreeVars b = FreeVars $ a .|. b

freeVar :: Int -> FreeVars
freeVar i = FreeVars $ 1 `shiftL` i

shiftFreeVars :: Int -> FreeVars -> FreeVars
shiftFreeVars i (FreeVars x) = FreeVars $ x `shift` i

isFreeVar :: FreeVars -> Int -> Bool
isFreeVar (FreeVars x) i = testBit x i

freeVars :: FreeVars -> [Int]
freeVars (FreeVars x) = take (popCount x) [i | i <- [0..], testBit x i]

isClosed :: FreeVars -> Bool
isClosed (FreeVars x) = x == 0

lowerFreeVars = shiftFreeVars (-1)

rearrangeFreeVars g l fv = case g of
    RFUp n -> appFreeVars l (`shiftL` n) fv
    RFMove n -> appFreeVars l (\x -> (if testBit x n then (`setBit` 0) else id) (clearBit x n `shiftL` 1)) fv
    _ -> error $ "rearrangeFreeVars: " ++ show g
  where
    appFreeVars l f (FreeVars i) = FreeVars $ (f (i `shiftR` l) `shiftL` l) .|. (i .&. (2^l-1))

-- TODO: rename
dbGE i (getFreeVars -> FreeVars x) = 2^i > x

class HasFreeVars a where
    getFreeVars :: a -> FreeVars

-------------------------------------------------------------------------------- fold De Bruijn indices

class Up{-TODO: rename-} a where

    foldVar :: Monoid e => (Int{-level-} -> Int{-index-} -> e) -> Int -> a -> e

    usedVar :: Int -> a -> Bool
    usedVar = (getAny .) . foldVar ((Any .) . (==))

instance Up Void where
    foldVar _ _ = elimVoid

-------------------------------------------------------------------------------- substitute names with De Bruijn indices

class DeBruijnify n a where
    deBruijnify_ :: Int -> [n] -> a -> a

deBruijnify = deBruijnify_ 0

instance (DeBruijnify n a, DeBruijnify n b) => DeBruijnify n (a, b) where
    deBruijnify_ k ns = deBruijnify_ k ns *** deBruijnify_ k ns

instance (DeBruijnify n a, DeBruijnify n b) => DeBruijnify n (Either a b) where
    deBruijnify_ k ns = deBruijnify_ k ns +++ deBruijnify_ k ns

instance (DeBruijnify n a) => DeBruijnify n [a] where
    deBruijnify_ k ns = fmap (deBruijnify_ k ns)


