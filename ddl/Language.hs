{-# LANGUAGE RankNTypes, OverloadedStrings, DeriveGeneric, LambdaCase #-}
module Language where

import GHC.Generics
import Data.Aeson (ToJSON(..),FromJSON(..))
import Control.Monad.Writer
import Data.String
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map

instance IsString Type where
  fromString a = Data a

data ModuleDef
  = ModuleDef
  { moduleName  :: String
  , imports     :: [String]
  , definitions :: [DataDef]
  }
  deriving (Show,Generic)

data DataDef
  = DataDef
  { dataName      :: String
  , constructors  :: [ConstructorDef]
  , instances     :: [Instance]
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

data Instance
  = Show
  | Eq
  | Ord
  deriving (Show,Generic)

data Target
  = Haskell
  | PureScript
  | Cpp
  | CSharp
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
  | Maybe Type
  | Map Type Type
  -- user defined
  | Data String
  deriving (Show,Generic)

parens :: String -> String
parens a
  | 1 == length (words a) = a
  | otherwise = "(" ++ a ++ ")"

type AliasMap = Map String Type

normalize :: AliasMap -> Type -> Type
normalize aliasMap t@(Data n) = Map.findWithDefault t n aliasMap
normalize _ t = t

psType :: AliasMap -> Type -> String
psType aliasMap = \case
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

  Array t       -> "Array " ++ parens (psType aliasMap t)
  List t        -> "List " ++ parens (psType aliasMap t)
  Maybe t       -> "Maybe " ++ parens (psType aliasMap t)
  Map k v
    | String <- normalize aliasMap k -> "StrMap " ++ parens (psType aliasMap v)
    | otherwise -> "Map " ++ parens (psType aliasMap k) ++ " " ++ parens (psType aliasMap v)
  -- user defined
  Data t        -> t
  x -> error $ "unknown type: " ++ show x

hsType :: AliasMap -> Type -> String
hsType aliasMap = \case
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

  Array t       -> "Vector " ++ parens (hsType aliasMap t)
  List t        -> "[" ++ hsType aliasMap t ++ "]"
  Maybe t       -> "Maybe " ++ parens (hsType aliasMap t)
  Map k v       -> "Map " ++ parens (hsType aliasMap k) ++ " " ++ parens (hsType aliasMap v)
  -- user defined
  Data t        -> t
  x -> error $ "unknown type: " ++ show x

swiftType :: AliasMap -> Type -> String
swiftType aliasMap = \case
  Int     -> "Int"
  Int32   -> "Int32"
  Word    -> "UInt"
  Word32  -> "UInt32"
  Float   -> "Float"
  Bool    -> "Bool"
  String  -> "String"
{-
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
-}
  Array t       -> "Array<" ++ parens (swiftType aliasMap t) ++ ">"
  List t        -> "Array<" ++ swiftType aliasMap t ++ ">"
  Maybe t       -> parens (swiftType aliasMap t) ++ "?"
  Map k v       -> "Dictionary<" ++ parens (swiftType aliasMap k) ++ ", " ++ parens (swiftType aliasMap v) ++ ">"
  -- user defined
  Data t        -> t
  _ -> "Int"
  x -> error $ "unknown type: " ++ show x

javaType :: AliasMap -> Type -> String -- TODO
javaType aliasMap a = case normalize aliasMap a of
  Data t        -> t
  Int           -> "int"
  Int32         -> "int"
  Word          -> "int"
  Word32        -> "int"
  Float         -> "float"
  Bool          -> "boolean"
  String        -> "String"
  Array t       -> "ArrayList<" ++ javaType aliasMap t ++ ">"
  List t        -> "ArrayList<" ++ javaType aliasMap t ++ ">"
  Map k v       -> "HashMap<" ++ javaType aliasMap k ++ ", " ++ javaType aliasMap v ++ ">"
  _ -> "int"

csType :: AliasMap -> Type -> String -- TODO
csType aliasMap a = case normalize aliasMap a of
  Data t        -> t
  Int           -> "int"
  Int32         -> "int"
  Word          -> "uint"
  Word32        -> "uint"
  Float         -> "float"
  Bool          -> "bool"
  String        -> "string"
  Array t       -> "List<" ++ csType aliasMap t ++ ">"
  List t        -> "List<" ++ csType aliasMap t ++ ">"
  Map k v       -> "Dictionary<" ++ csType aliasMap k ++ ", " ++ csType aliasMap v ++ ">"
  _ -> "int"

cppType :: AliasMap -> Type -> String
cppType aliasMap = \case
  Int           -> "Int"
  Int32         -> "Int32"
  Word          -> "Word"
  Word32        -> "Word32"
  Float         -> "Float"
  Bool          -> "Bool"
  String        -> "String"

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

  Array t       -> "std::vector<" ++ cppType aliasMap t ++ ">"
  List t        -> "std::vector<" ++ cppType aliasMap t ++ ">"
  Maybe t       -> "Maybe<" ++ cppType aliasMap t ++ ">"
  Map k v       -> "std::map<" ++ cppType aliasMap k ++ ", " ++ cppType aliasMap v ++ ">"
  -- user defined
  Data t        -> case normalize aliasMap (Data t) of
    Data _  -> "std::shared_ptr<::" ++ t ++ ">"
    _       -> "::" ++ t
  x -> error $ "unknown type: " ++ show x

hasFieldNames :: [Field] -> Bool
hasFieldNames [] = False
hasFieldNames l = all (not . null . fieldName) l

constType :: DataDef -> String
constType = head . words . show

instance ToJSON ConstructorDef
instance ToJSON DataDef
instance ToJSON Instance
instance ToJSON Field
instance ToJSON Type

instance FromJSON ConstructorDef
instance FromJSON DataDef
instance FromJSON Instance
instance FromJSON Field
instance FromJSON Type

type MDef = Writer [ModuleDef]
type DDef = Writer ([DataDef],[String])
type CDef = Writer ([ConstructorDef],[Instance])

module_ :: String -> DDef () -> MDef ()
module_ n m = tell [let (d,i) = execWriter m in ModuleDef n i d]

import_ :: [String] -> DDef ()
import_ l = tell (mempty,l)

data_ :: String -> CDef () -> DDef ()
data_ n l = tell ([let (c,i) = execWriter l in DataDef n c i],mempty)

alias_ :: String -> Type -> DDef ()
alias_ n t = tell ([TypeAlias n t],mempty)

a #= b = alias_ a b

class IsField a where
  toField :: a -> Field

instance IsField Field where
  toField a = a

instance IsField Type where
  toField a = Field "" a

deriving_ :: [Target] -> [Instance] -> CDef ()
deriving_ t l = tell (mempty,l)

const_ :: String -> [Type] -> CDef ()
const_ n t = tell ([ConstructorDef n [Field a b | Field a b <- map toField t]],mempty)

constR_ :: String -> [Field] -> CDef ()
constR_ n t = tell ([ConstructorDef n [Field a b | Field a b <- map toField t]],mempty)

enum_ :: String -> CDef ()
enum_ n = tell ([ConstructorDef n []],mempty)

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