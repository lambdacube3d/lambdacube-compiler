{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# language TemplateHaskell #-}  -- for testing
{-# LANGUAGE NoMonomorphismRestriction #-}

module FreeVars
    ( SFV(..), FV, Nat(..), pattern Nat
    , HasFV (..), Lens
    , up, down, usedVar, appLens, lComp, lConst
    , FVCache(..), LamFV(..), VarFV(..)
    , pattern CacheFV

    , expand, fv, primContract
    )
    where

import Data.List
import Data.Word
import Data.Int
import Data.Monoid
import Data.Maybe
import Data.Bits
import Data.Foldable
import Control.Arrow
import Control.Monad.State
import Control.Monad.Identity
import Control.Category hiding ((.), id)
import Test.QuickCheck hiding ((.&.))
import Test.QuickCheck.Property.Monoid hiding ((.&&.), (.||.))
import Test.QuickCheck.Property.Common.Internal (Equal(..))
--import Debug.Trace

import LambdaCube.Compiler.Pretty hiding (expand)

instance (Eq a, Show a) => Testable (Equal a) where
    property (Equal a b) = a === b
    property (AndE a b) = a .&&. b
    property (OrE a b) = a .||. b
    property (NotE a) = expectFailure a

----------------------------------------------------------------------------------

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

instance Monoid Nat where
    mempty = 0
    Nat a `mappend` Nat b = Nat (a + b)

instance PShow Nat where pShow (Nat i) = pShow i
instance Show Nat where show = ppShow

----------------------------------------------------------------------------------

-- Expand monoid
newtype Expand = Expand {getExpand :: FV}
    deriving (Eq, Show, Arbitrary)

instance Monoid Expand where
    mempty = Expand $ fO 0
    Expand a `mappend` Expand b = Expand (a `expand` b)

{-
diffTest u = u == uncurry expandT (diffT u)

assocTestL (D3 a b c) = (abc, D3 a'' b'' c'') == diffT (D3 a b c)
  where
    (ab, D2 a' b') = diffT $ D2 a b
    (abc, D2 ab' c'') = diffT $ D2 ab c
    D2 a'' b'' = expandT ab' $ D2 a' b'

assocTestR (D3 a b c) = (abc, D3 a'' b'' c'') == diffT (D3 a b c)
  where
    (bc, D2 b' c') = diffT $ D2 b c
    (abc, D2 a'' bc') = diffT $ D2 a bc
    D2 b'' c'' = expandT bc' $ D2 b' c'
-}

----------------------------------------------------------------------------------

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
    pShow = text . f where 
        f FE = "|"
        f (FV (Nat i) (Nat j) x) = replicate i '_' ++ replicate j '.' ++ f x

instance Show FV where show = ppShow

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

testNormalFV = f where
    f FE = True
    f (FV _ a xs) = a > 0 && g xs
    g FE = True
    g (FV a b xs) = a > 0 && b > 0 && g xs

instance Arbitrary FV where
    arbitrary = fromBools <$> arbitrary

fromBools [] = FE
fromBools (True: bs) = fv 0 1 $ fromBools bs
fromBools (False: bs) = fv 1 0 $ fromBools bs

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

prop_monoid_FV = prop_Monoid (T :: T FV)
prop_mappend_normal_FV (a :: FV) b = testNormalFV (a <> b)

expand :: FV -> FV -> FV
expand _ FE = FE
expand FE _ = FE
expand (FV a b xs) (FV c d ys)
    | c + d <= b  = fv (a + c) d       $ expand (FV 0 (b - (c + d)) xs) ys
    | c <= b      = fv (a + c) (b - c) $ expand xs (FV 0 (d - (b - c)) ys)
    | otherwise   = fv (a + b) 0       $ expand xs (FV (c - b) d ys)

primContract :: FV -> FV -> FV
primContract x FE = FE
primContract (FV a' b' us') (FV a b us)
    | a' + b' <= a = fv b'       0 $ primContract us' (FV (a - (a' + b')) b us)
    | otherwise    = fv (a - a') b $ primContract (FV 0 ((a' + b') - (a + b)) us') us

contract :: FV -> FV -> FV
contract a b = primContract (a <> b) a

--    selfContract a = primContract a a
selfContract :: FV -> FV
selfContract xs = fv 0 (altersum xs) FE
  where
    altersum FE = 0
    altersum (FV _ a cs) = a + altersum cs

prop_expand_normal_FV (a :: FV) b = testNormalFV (expand a b)
prop_contract_normal_FV (a :: FV) b = testNormalFV (contract a b)

prop_monoid_Expand_FV = prop_Monoid (T :: T Expand)
{-
--prop_diffTestFV1 = diffTest :: D1 FV -> Bool
--prop_diffTestFV2 = diffTest :: D2 FV -> Bool
--prop_diffTestFV3 = diffTest :: D3 FV -> Bool

--prop_assocTestL_FV = assocTestL :: D3 FV -> Bool
--prop_assocTestR_FV = assocTestR :: D3 FV -> Bool
-}

sIndex :: FV -> Nat -> Bool
sIndex FE i = False
sIndex (FV n l us) i = i >= n && (i < l || sIndex us (i - l - n))

sDrop :: Nat -> FV -> FV
sDrop _ FE = FE
sDrop n (FV i j us)
    | i + j <= n   = sDrop (n - (i + j)) us
    | n <= i       = FV (i - n) j us
    | otherwise    = FV 0 (j - (n - i)) us

------------------------------------------------

onTail :: (FV -> FV) -> Nat -> FV -> FV
onTail f 0 u = f u
onTail f n FE = fv n 0 $ f FE
onTail f n (FV i j us)
    | i + j <= n   = fv i j $ onTail f (n - (i + j)) us
    | n <= i       = fv n 0 $ f $ FV (i - n) j us
    | otherwise    = fv i (n - i) $ f $ FV 0 (j - (n - i)) us

-- downFV i u = if sIndex u i then Just $ fv 0 i (FO 1) `contract` u else Nothing
downFV :: Nat -> FV -> Maybe FV
downFV i FE = Just FE
downFV i (FV n j us)
    | i < n     = Just $ FV (n - 1) j us
    | i - n < j = Nothing
    | otherwise = fv n j <$> downFV (i - n - j) us

-- TODO
fO i = FV i 10000 FE

mkUp l n = fv 0 l $ fO n

--upFV l n = expand (mkUp l n)
upFV :: Nat -> Nat -> FV -> FV
upFV l n FE = FE
upFV l n (FV n' l' us)
    | l  <= n'     = FV (n' + n) l' us
    | l' <= l - n' = FV n' l' $ upFV (l - n' - l') n us
    | otherwise    = FV n' (l - n') $ FV n (l' - (l - n')) us

--------------------------------------------

type Lens a b = a -> (b, b -> a)

(l1 `lComp` l2) (l1 -> (l2 -> (y, fy), fx)) = (y, fx . fy)

lConst e = (mempty, const e)

lId x = (x, id)

lApp' f (a, b) = b (f a)

------------

class HasFV a where
    fvLens :: Lens a FV

appLens fx (fvLens -> (y, fy)) = (y, fx . fy)

up l n = lApp' (upFV l n) . fvLens

down i (fvLens -> (ux, fx)) = fx <$> downFV i ux

usedVar :: HasFV x => Nat -> x -> Bool
usedVar i x = sIndex (fst $ fvLens x :: FV) i

instance HasFV FV where
    fvLens = lId

instance (HasFV a, HasFV b) => HasFV (a, b) where
    fvLens (fvLens -> (ux, x'), fvLens -> (uy, y')) = (s, \s' -> (x' $ s' `expand` primContract s ux, y' $ s' `expand` primContract s uy)) where
        s = ux <> uy

--prop_HasFV_D2 (a :: FV) b = contractFV (D2 a b) == diffT (D2 a b)
--prop_HasFV_D2' (s :: FV) a b = expandFV s (D2 a b) == expandT s (D2 a b)

newtype LamFV u = LamFV {getLamFV :: u}
    deriving (Eq, Show)

instance HasFV a => HasFV (LamFV a) where
    fvLens (LamFV (fvLens -> x@(ux, fx))) = (sDrop 1 ux, \s -> LamFV $ lApp' (onTail (const s) 1) x)

--prop_LamFV (u :: FV) = contractFV (LamFV u) == (sDrop 1 u, LamFV $ onTail selfContract 1 u)
--prop_LamFV' s (u :: FV) = expandFV s (LamFV u) == LamFV (fv 0 1 s `expand` u)

data FVCache a b = FVCache !a !b
    deriving (Eq, Show)

instance Functor (FVCache a) where
    fmap f (FVCache a b) = FVCache a (f b)

instance HasFV (FVCache FV x) where
    fvLens (FVCache u x) = (u, \u -> FVCache u x)

pattern CacheFV a <- FVCache u (lApp' (expand u) . fvLens -> a)
  where CacheFV (fvLens -> x@(ua, fa)) = FVCache ua $ lApp' selfContract x

instance HasFV a => HasFV [a] where
    fvLens [] = lConst []
    fvLens [fvLens -> (u, fx)] = (u, \s -> [fx s])
    fvLens [fvLens -> (u, fx), fvLens -> (u', fy)] = (s, \s' -> [fx $ s' `expand` primContract s u, fy $ s' `expand` primContract s u' ])
      where
        s = u <> u'
    fvLens (unzip . map fvLens -> (us, fs)) = let
        s = mconcat us in (s, \s -> zipWith (\f u -> f $ s `expand` primContract s u) fs us)

newtype VarFV = VarFV Nat
    deriving (Eq, Show)

instance HasFV VarFV where
    fvLens (VarFV i) = (FV i 1 FE, \(FV i _ _) -> VarFV i)

---------------------------------------------------------------------------------- skewed free vars set

-- skewed FV
data SFV = SFV !Nat !FV
    deriving (Eq, Show)

instance PShow SFV where pShow (SFV n x) = pShow n <> pShow x

instance Arbitrary SFV where
    arbitrary = SFV <$> (Nat . getNonNegative <$> arbitrary) <*> arbitrary

instance Monoid SFV where
    mempty = SFV 0 mempty

    SFV m b `mappend` SFV n a = SFV (n + m) $ sDrop n b <> a

prop_monoid_SFV = prop_Monoid (T :: T SFV)

instance HasFV SFV where
    fvLens (SFV n u) = (u, SFV n)
{-
--prop_diffTest1_SFV = diffTest :: D1 SFV -> Bool
--prop_diffTest2_SFV = diffTest :: D2 SFV -> Bool
--prop_diffTest3_SFV = diffTest :: D3 SFV -> Bool

--prop_assocTestL_SFV = assocTestL :: D3 SFV -> Bool
--prop_assocTestR_SFV = assocTestR :: D3 SFV -> Bool
-}

-----------------------------------------------------

return []
main = $quickCheckAll

