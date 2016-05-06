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
import Control.Arrow hiding ((<+>))

import LambdaCube.Compiler.Utils

-------------------------------------------------------------------------------- rearrange De Bruijn indices

class Rearrange a where
    rearrange :: Int{-level-} -> (Int -> Int) -> a -> a

rSubst :: Rearrange a => Int -> Int -> a -> a
rSubst i j = rearrange 0 $ \k -> if k == i then j else if k > i then k - 1 else k

-- move index to 0
rMove :: Rearrange a => Int -> Int -> a -> a
rMove i l = rearrange l $ \k -> if k == i then 0 else k + 1

rUp :: Rearrange a => Int -> Int -> a -> a
rUp n l = rearrange l $ \k -> if k >= 0 then k + n else k

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


