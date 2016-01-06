{-# LANGUAGE PatternGuards #-}
module Main where

import Data.Monoid
import Test.QuickCheck
import Text.Parsec.Pos (SourcePos(..), newPos, sourceName, sourceLine, sourceColumn)

import Test.Tasty
import Test.Tasty.QuickCheck


import Infer
import System.Exit (exitFailure)


main = defaultMain $ testGroup "Compiler"
  [ testGroup "Infer" [
        testProperty "SI Monoid Identity" (propMonoidIdentity (arbitrary :: Gen SI))
      , testProperty "SI Monoid Associativity" (propMonoidAssociativity (arbitrary :: Gen SI))
      ]
  ]

----------------------------------------------------------------- Arbitraries

instance Arbitrary SourcePos where
  arbitrary = newPos <$> arbitrary <*> arbitrary <*> arbitrary
  shrink pos
    | n <- sourceName pos, l <- sourceLine pos, c <- sourceColumn pos
      = [newPos n' l' c' | n' <- shrink n, l' <- shrink l, c' <- shrink c]
  -- TODO: Diagonilaze shrink

instance Arbitrary SI where
  arbitrary = oneof [return NoSI, Range <$> arbitrary]
  shrink NoSI = []
  shrink (Range r) = NoSI:map Range (shrink r)

----------------------------------------------------------------- Properties

-- * Monoid

propMonoidIdentity :: (Eq m, Monoid m, Show m) => Gen m -> Property
propMonoidIdentity gen = forAll gen (\x -> x === x <> mempty)

propMonoidAssociativity :: (Arbitrary m, Eq m, Monoid m, Show m) => Gen m -> Property
propMonoidAssociativity gen = forAll gen (\x y z -> (x <> y) <> z == x <> (y <> z))

