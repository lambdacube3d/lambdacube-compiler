{-# LANGUAGE StandaloneDeriving #-}
module Main where

import Data.Monoid
import Text.Megaparsec.Pos (SourcePos(..), newPos, sourceName, sourceLine, sourceColumn)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Test.QuickCheck
import Test.QuickCheck.Property
import Test.Tasty
import Test.Tasty.QuickCheck

import LambdaCube.Compiler.Infer

----------------------------------------------------------------- Main

-- Usage: ":main --quickcheck-max-size 30 --quickcheck-tests 100"
main = defaultMain $ testGroup "Compiler"
  [ testGroup "Infer" $ concat [
        monoidTestProperties "SI"    (arbitrary :: Gen SI)
--      , monoidTestProperties "Infos" (arbitrary :: Gen Infos) -- list is always a monoid
--      , monoidTestProperties "MaxDB" (arbitrary :: Gen MaxDB)
      ]
  ]

----------------------------------------------------------------- Arbitraries

-- SourcePos

instance Arbitrary SourcePos where
  arbitrary = newPos <$> arbitrary <*> (getPositive <$> arbitrary) <*> (getPositive <$> arbitrary)
  shrink pos
    | n <- sourceName pos, l <- sourceLine pos, c <- sourceColumn pos
      = [newPos n' l' c' | n' <- shrink n, l' <- shrink l, c' <- shrink c]
  -- TODO: Diagonalize shrink

-- Range

instance Arbitrary Range where
  arbitrary = Range <$> arbitrary <*> arbitrary
  shrink (Range a b) = Range <$> shrink a <*> shrink b

deriving instance Show Range

-- SI

instance Arbitrary SI where
  arbitrary = oneof [NoSI . Set.fromList <$> arbitrary, RangeSI <$> arbitrary]
  shrink (NoSI ds) = []
  shrink (RangeSI r) = mempty: map RangeSI (shrink r)

instance MonoidEq SI where
  NoSI a    =::= NoSI  b   = a == b
  RangeSI a =::= RangeSI b = a == b

instance TestShow SI where
  testShow (NoSI a)    = "NoSI " ++ show a
  testShow (RangeSI a) = "RangeSI " ++ show a

-- Infos
{- list is always a monoid
instance Arbitrary Info where
  arbitrary = Info <$> arbitrary

instance Arbitrary Infos where
  arbitrary        = Infos . Map.fromList <$> arbitrary
  shrink (Infos m) = map (Infos . Map.fromList . shrink) $ Map.toList m

deriving instance Eq Infos

instance MonoidEq Infos where
  (=::=) = (==)

instance TestShow Infos where
  testShow (Infos i) = "Infos " ++ show i
-}
-- MaxDB
{- todo
instance Arbitrary MaxDB where
  arbitrary = MaxDB <$> {-fmap (fmap abs)-} arbitrary
  shrink (MaxDB m) = map MaxDB $ shrink m

instance MonoidEq MaxDB where
  MaxDB (Just n) =::= MaxDB (Just m) = n == m
  MaxDB Nothing  =::= MaxDB Nothing  = True
  MaxDB (Just 0) =::= MaxDB Nothing  = True
  MaxDB Nothing  =::= MaxDB (Just 0) = True
  _              =::= _              = False

instance TestShow MaxDB where
  testShow (MaxDB a) = "MaxDB " ++ show a
-}
----------------------------------------------------------------- Test building blocks

class Monoid m => MonoidEq m where
  (=::=) :: m -> m -> Bool

infix 4 =::=

monoidTestProperties name gen =
  [ testProperty (name ++ " monoid left identity")  (propMonoidLeftIdentity gen)
  , testProperty (name ++ " monoid right identity") (propMonoidRightIdentity gen)
  , testProperty (name ++ " monoid associativity")  (propMonoidAssociativity gen)
  ]

----------------------------------------------------------------- Properties

-- * Monoid

propMonoidLeftIdentity :: (MonoidEq m, TestShow m) => Gen m -> Property
propMonoidLeftIdentity gen = forAll' gen (\x -> x =*= mempty <> x)

propMonoidRightIdentity :: (MonoidEq m, TestShow m) => Gen m -> Property
propMonoidRightIdentity gen = forAll' gen (\x -> x =*= x <> mempty)

propMonoidAssociativity :: (Arbitrary m, MonoidEq m, TestShow m) => Gen m -> Property
propMonoidAssociativity gen =
  forAll' gen $ \x -> forAll' gen $ \y -> forAll' gen $ \z ->
    (x <> y) <> z =*= x <> (y <> z)

----------------------------------------------------------------- Tools

class TestShow t where
  testShow :: t -> String

-- | Like '=::=', but prints a counterexample when it fails.
infix 4 =*=
(=*=) :: (MonoidEq a, TestShow a) => a -> a -> Property
x =*= y =
  counterexample (testShow x ++ " /= " ++ testShow y) (x =::= y)

forAll' :: (TestShow a, Testable prop)
        => Gen a -> (a -> prop) -> Property
forAll' gen pf =
  MkProperty $
  gen >>= \x ->
    unProperty (counterexample (testShow x) (pf x))
