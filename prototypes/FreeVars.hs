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
    , Pair, pattern Pair
    , List, pattern List
    , LamFV, pattern LamFV
    , VarFV(..)

    , ChangeFV(..)
    , expand'', expand'''
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

fromStr = fromBools . map (=='1')

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

{-
--prop_diffTestFV1 = diffTest :: D1 FV -> Bool
--prop_diffTestFV2 = diffTest :: D2 FV -> Bool
--prop_diffTestFV3 = diffTest :: D3 FV -> Bool

--prop_assocTestL_FV = assocTestL :: D3 FV -> Bool
--prop_assocTestR_FV = assocTestR :: D3 FV -> Bool
-}

propagateChange :: FV -> FV -> FV -> FV
propagateChange _ _ FE = FE
propagateChange new@(FV nn ln un) old@(FV no lo uo) x
    = fv nn 0 $  onTail (propagateChange (fv 0 (ln - l) un) (fv 0 (lo - l) uo)) l $ sDrop no x
  where
    l = min ln lo

{-
prop_propagate a b = do
    let ab = a <> b
        FV _ n _ = selfContract ab
    gs <- replicateM n arbitrary
    let ab' = foldr (\n -> fv n 1) FE gs
    return $ 
-}

data ChangeFV
    = Same !FV
    | Changed !FV !FV  -- new old
    deriving (Eq, Show)

instance HasFV ChangeFV where
    fvLens = \case
        Same u -> (u, \s -> if s == u then Same u else Changed s u)
        Changed n o -> (n, \s -> if s == o then Same o else Changed s o)

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

data Pair a b = Pair_ !ChangeFV !a !b
    deriving (Eq, Show)

instance (HasFV a, HasFV b) => HasFV (Pair a b) where
    fvLens (Pair_ (fvLens -> ~(s, f)) a b) = (s, \s -> Pair_ (f s) a b)

pattern Pair a b <- Pair_ s (expand'' s -> a) (expand'' s -> b)
  where Pair a@(fvLens -> ~(ux, _)) b@(fvLens -> ~(uy, _)) = Pair_ (Same $ ux <> uy) a b

--prop_HasFV_D2 (a :: FV) b = contractFV (D2 a b) == diffT (D2 a b)
--prop_HasFV_D2' (s :: FV) a b = expandFV s (D2 a b) == expandT s (D2 a b)

data LamFV u = LamFV_ !ChangeFV u
    deriving (Eq, Show)

instance HasFV a => HasFV (LamFV a) where
    fvLens (LamFV_ (fvLens -> (s, f)) x) = (s, \s -> LamFV_ (f s) x)

pattern LamFV a <- LamFV_ s (expand''' 1 s -> a)
  where LamFV a@(fvLens -> ~(ux, _)) = LamFV_ (Same $ sDrop 1 ux) a

--prop_LamFV (u :: FV) = contractFV (LamFV u) == (sDrop 1 u, LamFV $ onTail selfContract 1 u)
--prop_LamFV' s (u :: FV) = expandFV s (LamFV u) == LamFV (fv 0 1 s `expand` u)

expand'' Same{} x = x
expand'' (Changed new old) (fvLens -> (x, f)) = f $ propagateChange new old x

expand''' _ Same{} x = x
expand''' n (Changed new old) (fvLens -> (x, f)) = f $ onTail (propagateChange new old) n x

data List a = List_ !ChangeFV [a]
    deriving (Eq, Show)

instance HasFV a => HasFV (List a) where
    fvLens (List_ (fvLens -> (s, f)) xs) = (s, \s -> List_ (f s) xs)

pattern List a <- List_ s (map (expand'' s) -> a)
  where List a = List_ (Same $ mconcat $ map (fst . fvLens) a) a

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
{-
instance HasFV SFV where
    fvLens (SFV n u) = (u, SFV n)
-}
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

