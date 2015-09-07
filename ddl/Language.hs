{-# LANGUAGE RankNTypes, OverloadedStrings, DeriveGeneric, LambdaCase #-}
module Language where

import GHC.Generics
import Data.Aeson (ToJSON(..),FromJSON(..))
import Control.Monad.Writer
import Data.String
import Data.List

instance IsString Type where
  fromString a = Data a

data DataDef
  = DataDef
  { dataName      :: String
  , constructors  :: [ConstructorDef]
  }
  | TypeAlias
  { aliasName     :: String
  , aliasType     :: Type
  }
  deriving (Show,Generic)

data ConstructorDef
  = ConstructorDef
  { name          :: String
  , fields        :: [Field]
  }
  deriving (Show,Generic)

data Field
  = Field
  { fieldName :: String
  , fieldType :: Type
  }
  deriving (Show,Generic)

data Type
  = Int
  | Int32
  | Word
  | Word32
  | Float
  | Bool
  | String
  | V2 Type
  | V3 Type
  | V4 Type
  -- higher order types
  | Array Type
  | List Type
  | Tuple [Type]
  | Maybe Type
  | Map Type Type
  -- user defined
  | Data String
  deriving (Show,Generic)

parens :: String -> String
parens a
  | 1 == length (words a) = a
  | otherwise = "(" ++ a ++ ")"

psType :: Type -> String
psType = \case
  Int     -> "Int"
  Int32   -> "Int32"
  Word    -> "Word"
  Word32  -> "Word32"
  Float   -> "Float"
  Bool    -> "Bool"
  String  -> "String"

  V2 Int        -> "V2I"
  V2 Word       -> "V2U"
  V2 Float      -> "V2F"
  V2 Bool       -> "V2B"
  V2 (V2 Float) -> "M22F"
  V2 (V3 Float) -> "M32F"
  V2 (V4 Float) -> "M42F"

  V3 Int        -> "V3I"
  V3 Word       -> "V3U"
  V3 Float      -> "V3F"
  V3 Bool       -> "V3B"
  V3 (V2 Float) -> "M23F"
  V3 (V3 Float) -> "M33F"
  V3 (V4 Float) -> "M43F"

  V4 Int        -> "V4I"
  V4 Word       -> "V4U"
  V4 Float      -> "V4F"
  V4 Bool       -> "V4B"
  V4 (V2 Float) -> "M24F"
  V4 (V3 Float) -> "M34F"
  V4 (V4 Float) -> "M44F"

  Array t       -> "Array " ++ parens (hsType t)
  List t        -> "List " ++ parens (hsType t)
  Tuple l       -> "(" ++ intercalate "," (map hsType l) ++ ")"
  Maybe t       -> "Maybe " ++ parens (hsType t)
  Map String v  -> "StrMap " ++ parens (hsType v)
  Map k v       -> "Map " ++ parens (hsType k) ++ " " ++ parens (hsType v)
  -- user defined
  Data t        -> t
  x -> error $ "unknown type: " ++ show x

hsType :: Type -> String
hsType = \case
  Int     -> "Int"
  Int32   -> "Int32"
  Word    -> "Word"
  Word32  -> "Word32"
  Float   -> "Float"
  Bool    -> "Bool"
  String  -> "String"

  V2 Int        -> "V2I"
  V2 Word       -> "V2U"
  V2 Float      -> "V2F"
  V2 Bool       -> "V2B"
  V2 (V2 Float) -> "M22F"
  V2 (V3 Float) -> "M32F"
  V2 (V4 Float) -> "M42F"

  V3 Int        -> "V3I"
  V3 Word       -> "V3U"
  V3 Float      -> "V3F"
  V3 Bool       -> "V3B"
  V3 (V2 Float) -> "M23F"
  V3 (V3 Float) -> "M33F"
  V3 (V4 Float) -> "M43F"

  V4 Int        -> "V4I"
  V4 Word       -> "V4U"
  V4 Float      -> "V4F"
  V4 Bool       -> "V4B"
  V4 (V2 Float) -> "M24F"
  V4 (V3 Float) -> "M34F"
  V4 (V4 Float) -> "M44F"

  Array t       -> "[" ++ hsType t ++ "]"
  List t        -> "[" ++ hsType t ++ "]"
  Tuple l       -> "(" ++ intercalate "," (map hsType l) ++ ")"
  Maybe t       -> "Maybe " ++ parens (hsType t)
  Map k v       -> "Map " ++ parens (hsType k) ++ " " ++ parens (hsType v)
  -- user defined
  Data t        -> t
  x -> error $ "unknown type: " ++ show x

hasFieldNames :: [Field] -> Bool
hasFieldNames [] = False
hasFieldNames l = all (not . null . fieldName) l

constType :: DataDef -> String
constType = head . words . show

instance ToJSON ConstructorDef
instance ToJSON DataDef
instance ToJSON Field
instance ToJSON Type

instance FromJSON ConstructorDef
instance FromJSON DataDef
instance FromJSON Field
instance FromJSON Type

type DDef = Writer [DataDef]
type CDef = Writer [ConstructorDef]

data_ :: forall a . String -> CDef () -> DDef ()
data_ n l = tell [DataDef n $ execWriter l]

alias_ :: String -> Type -> DDef ()
alias_ n t = tell [TypeAlias n t]

a #= b = alias_ a b

class IsField a where
  toField :: a -> Field

instance IsField Field where
  toField a = a

instance IsField Type where
  toField a = Field "" a

const_ :: String -> [Type] -> CDef ()
const_ n t = tell [ConstructorDef n [Field a b | Field a b <- map toField t]]

constR_ :: String -> [Field] -> CDef ()
constR_ n t = tell [ConstructorDef n [Field a b | Field a b <- map toField t]]

enum_ :: String -> CDef ()
enum_ n = tell [ConstructorDef n []]

v2b = V2 Bool
v3b = V3 Bool
v4b = V4 Bool
v2u = V2 Word
v3u = V3 Word
v4u = V4 Word
v2i = V2 Int
v3i = V3 Int
v4i = V4 Int
v2f = V2 Float
v3f = V3 Float
v4f = V4 Float
m22 = V2 v2f
m23 = V3 v2f
m24 = V4 v2f
m32 = V2 v3f
m33 = V3 v3f
m34 = V4 v3f
m42 = V2 v4f
m43 = V3 v4f
m44 = V4 v4f

(#::) :: String -> Type -> Field
a #:: b = Field a b

{-
  definitions:
    ADT
    Record
    Vector

  instances:
    Show
    Eq
    Ord

  serialization:
    json: encode/decode
    other?
-}