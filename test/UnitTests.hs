module Main where

import Data.Monoid
import Text.Parsec.Pos (SourcePos(..), newPos, sourceName, sourceLine, sourceColumn)
import qualified Data.Set as Set

import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck

import LambdaCube.Compiler.Infer


main = defaultMain $ testGroup "Compiler"
  [ testGroup "Infer" [
        testProperty "SI monoid left identity" (propMonoidLeftIdentity (arbitrary :: Gen SI))
      , testProperty "SI monoid right identity" (propMonoidRightIdentity (arbitrary :: Gen SI))
      , testProperty "SI monoid associativity" (propMonoidAssociativity (arbitrary :: Gen SI))
      ]
  ]

----------------------------------------------------------------- Arbitraries

instance Arbitrary SourcePos where
  arbitrary = newPos <$> arbitrary <*> arbitrary <*> arbitrary
  shrink pos
    | n <- sourceName pos, l <- sourceLine pos, c <- sourceColumn pos
      = [newPos n' l' c' | n' <- shrink n, l' <- shrink l, c' <- shrink c]
  -- TODO: Diagonalize shrink

instance Arbitrary SI where
  arbitrary = oneof [NoSI . Set.fromList <$> arbitrary, Range <$> arbitrary]
  shrink (NoSI ds) = []
  shrink (Range r) = NoSI (Set.empty):map Range (shrink r)

----------------------------------------------------------------- Properties

-- * Monoid

propMonoidLeftIdentity :: (Eq m, Monoid m, Show m) => Gen m -> Property
propMonoidLeftIdentity gen = forAll gen (\x -> x === mempty <> x)

propMonoidRightIdentity :: (Eq m, Monoid m, Show m) => Gen m -> Property
propMonoidRightIdentity gen = forAll gen (\x -> x === x <> mempty)

propMonoidAssociativity :: (Arbitrary m, Eq m, Monoid m, Show m) => Gen m -> Property
propMonoidAssociativity gen = forAll gen (\x y z -> (x <> y) <> z === x <> (y <> z))
