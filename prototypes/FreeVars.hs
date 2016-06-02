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
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# language TemplateHaskell #-}  -- for testing

module FreeVars where

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

instance PShow Nat where pShow (Nat i) = pShow i
instance Show Nat where show = ppShow

----------------------------------------------------------------------------------

data D1 a = D1 a
    deriving (Functor, Foldable, Traversable, Eq, Ord, Show)

data D2 a = D2 a a
    deriving (Functor, Foldable, Traversable, Eq, Ord, Show)

data D3 a = D3 a a a
    deriving (Functor, Foldable, Traversable, Eq, Ord, Show)

instance Arbitrary a => Arbitrary (D1 a) where arbitrary = D1 <$> arbitrary
instance Arbitrary a => Arbitrary (D2 a) where arbitrary = D2 <$> arbitrary <*> arbitrary
instance Arbitrary a => Arbitrary (D3 a) where arbitrary = D3 <$> arbitrary <*> arbitrary <*> arbitrary

----------------------------------------------------------------------------------

class Monoid a => Expandable a where

    expandT :: Traversable t => a -> t a -> t a
    expandT = fmap . expand

    expand :: a -> a -> a
    expand u = runIdentity . expandT u . Identity

    primContractT :: Traversable t => a -> t a -> t a
    primContractT = fmap . primContract

    primContract :: a -> a -> a
    primContract u = runIdentity . primContractT u . Identity

    contract :: a -> a -> a
    contract a b = primContract (a <> b) a

    selfContract :: a -> a
    selfContract a = primContract a a

diffT :: (Traversable t, Expandable a) => t a -> (a, t a)
diffT u = (s, primContractT s u)
  where
    s = fold u

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

class StreamLike a where
    type StreamElem a

    sDrop :: Nat -> a -> a

    sIndex :: a -> Nat -> StreamElem a

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

instance Expandable FV where
    expand _ FE = FE
    expand FE _ = FE
    expand (FV a b xs) (FV c d ys)
        | c + d <= b  = fv (a + c) d       $ expand (FV 0 (b - (c + d)) xs) ys
        | c <= b      = fv (a + c) (b - c) $ expand xs (FV 0 (d - (b - c)) ys)
        | otherwise   = fv (a + b) 0       $ expand xs (FV (c - b) d ys)

    primContract x FE = FE
    primContract (FV a' b' us') (FV a b us)
        | a' + b' <= a = fv b'       0 $ primContract us' (FV (a - (a' + b')) b us)
        | otherwise    = fv (a - a') b $ primContract (FV 0 ((a' + b') - (a + b)) us') us

    selfContract xs = fv 0 (altersum xs) FE
      where
        altersum FE = 0
        altersum (FV _ a cs) = a + altersum cs

prop_expand_normal_FV (a :: FV) b = testNormalFV (expand a b)
prop_contract_normal_FV (a :: FV) b = testNormalFV (contract a b)

prop_diffTestFV1 = diffTest :: D1 FV -> Bool
prop_diffTestFV2 = diffTest :: D2 FV -> Bool
prop_diffTestFV3 = diffTest :: D3 FV -> Bool

prop_assocTestL_FV = assocTestL :: D3 FV -> Bool
prop_assocTestR_FV = assocTestR :: D3 FV -> Bool

instance StreamLike FV where
    type StreamElem FV = Bool

    sIndex FE i = False
    sIndex (FV n l us) i = i >= n && (i < l || sIndex us (i - l - n))

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

-- usedFVs s = filter (sIndex s) [0..]
-- TODO: remove
usedFVs :: FV -> [Nat]
usedFVs = f 0
  where
    f _ FE = []
    f s (FV i a xs) = [s+i..(s+i+a)-1] ++ f (s+i+a) xs

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

--upFV l n = expand (fv 0 l $ FO n)
upFV :: Nat -> Nat -> FV -> FV
upFV l n FE = FE
upFV l n (FV n' l' us)
    | l  <= n'     = FV (n' + n) l' us
    | l' <= l - n' = FV n' l' $ upFV (l - n' - l') n us
    | otherwise    = FV n' (l - n') $ FV n (l' - (l - n')) us

pattern VarFV i <- FV i _ _
  where VarFV i =  FV i 1 FE

incFV :: FV -> FV
incFV = FV{-ok-} 0 1

-- compact u = r where (_, D2 r _) = cDiffT $ D2 (SFV 0 u) (SFV 1 FE)
compact :: FV -> FV
compact xs@(FV 0 _ _) = selfContract xs
compact xs = fv 1 0 $ selfContract xs

---------------------------------------------------------------------------------- skewed free vars set

-- skewed FV
data SFV = SFV !Nat !FV
    deriving (Eq, Show)

padSFV (SFV n x) = SFV n $ fv 0 n $ sDrop n x

fromSFV (SFV n u) = sDrop n u

instance PShow SFV where pShow (SFV n x) = pShow n <> pShow x

instance Arbitrary SFV where
    arbitrary = SFV <$> (Nat . getNonNegative <$> arbitrary) <*> arbitrary

instance Monoid SFV where
    mempty = SFV 0 mempty

    SFV m b `mappend` SFV n a = SFV (n + m) $ b <> fv m 0 a

prop_monoid_SFV = prop_Monoid (T :: T SFV)

instance Expandable SFV where

    expandT (padSFV -> SFV n b) = flip evalState b . traverse (\(SFV n a) -> state $ \u -> (SFV n $ u `expand` a, sDrop n u))

    primContractT (padSFV -> SFV _ b) = flip evalState b . traverse (\(SFV n a) -> state $ \u -> (SFV n $ u `primContract` a, sDrop n u))

prop_diffTest1_SFV = diffTest :: D1 SFV -> Bool
prop_diffTest2_SFV = diffTest :: D2 SFV -> Bool
prop_diffTest3_SFV = diffTest :: D3 SFV -> Bool

prop_assocTestL_SFV = assocTestL :: D3 SFV -> Bool
prop_assocTestR_SFV = assocTestR :: D3 SFV -> Bool

return []
main = $quickCheckAll

