{-# LANGUAGE StandaloneDeriving #-}
import System.Environment
import Control.Monad.Except
import Type
import Parser

deriving instance Show Lit
deriving instance (Show a, Show b, Show c, Show d) => Show (Pat_ a b c d)
deriving instance Show PatR
deriving instance Show Pat
deriving instance (Show a, Show b) => Show (Constraint' a b)
deriving instance (Show a, Show b) => Show (TypeFun a b)
instance Show Witness where show _ = "Witness"
deriving instance (Show a, Show b, Show c, Show d, Show e) => Show (Exp_ a b c d e)
deriving instance Show ExpR
deriving instance Show Exp
deriving instance Show NameSpace
deriving instance Show NameInfo
deriving instance Show N
deriving instance Show FixityDir
deriving instance Show Range
deriving instance (Show a, Show b) => Show (ValueDef a b)
deriving instance (Show a, Show b) => Show (TypeSig a b)
deriving instance Show ModuleR
deriving instance Show Definition
deriving instance Show WhereRHS
deriving instance Show GuardedRHS
deriving instance Show ConDef
deriving instance Show FieldTy
deriving instance Show Item
deriving instance Show Subst

main = do
  args <- getArgs
  forM_ args $ \a -> do
    r <- runExceptT $ parseLC a
    print r
    putStrLn a
