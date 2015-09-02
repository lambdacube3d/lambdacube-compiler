{-# LANGUAGE DeriveFunctor, OverloadedStrings #-}
module Linear where

import Data.Int
import Data.Word
import Data.Map

import Data.Text
import Data.Aeson
import Control.Monad

data V2 a = V2 !a !a deriving (Eq,Ord,Show,Read,Functor)
data V3 a = V3 !a !a !a deriving (Eq,Ord,Show,Read,Functor)
data V4 a = V4 !a !a !a !a deriving (Eq,Ord,Show,Read,Functor)

-- matrices are stored in column major order
type M22F = V2 V2F
type M23F = V3 V2F
type M24F = V4 V2F
type M32F = V2 V3F
type M33F = V3 V3F
type M34F = V4 V3F
type M42F = V2 V4F
type M43F = V3 V4F
type M44F = V4 V4F

type V2F = V2 Float
type V3F = V3 Float
type V4F = V4 Float
type V2I = V2 Int32
type V3I = V3 Int32
type V4I = V4 Int32
type V2U = V2 Word32
type V3U = V3 Word32
type V4U = V4 Word32
type V2B = V2 Bool
type V3B = V3 Bool
type V4B = V4 Bool

instance ToJSON a => ToJSON (V2 a) where
  toJSON (V2 x y) = object ["x" .= x, "y" .= y]

instance ToJSON a => ToJSON (V3 a) where
  toJSON (V3 x y z) = object ["x" .= x, "y" .= y, "z" .= z]

instance ToJSON a => ToJSON (V4 a) where
  toJSON (V4 x y z w) = object ["x" .= x, "y" .= y, "z" .= z, "w" .= w]

instance FromJSON a => FromJSON (V2 a) where
  parseJSON (Object obj) = V2 <$> obj .: "x" <*> obj .: "y"
  parseJSON _ = mzero

instance FromJSON a => FromJSON (V3 a) where
  parseJSON (Object obj) = V3 <$> obj .: "x" <*> obj .: "y" <*> obj .: "z"
  parseJSON _ = mzero

instance FromJSON a => FromJSON (V4 a) where
  parseJSON (Object obj) = V4 <$> obj .: "x" <*> obj .: "y" <*> obj .: "z" <*> obj .: "w"
  parseJSON _ = mzero

