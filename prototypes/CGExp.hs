{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
module CGExp
    ( module CGExp
    , module Infer
    ) where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Writer
import Control.Arrow
import qualified Data.Set as S
import qualified Data.Map as M
import Text.Parsec.Pos

import Pretty
import qualified Infer as I
import Infer (Binder(..), SName, Lit(..), Visibility(..), FunName(..), CaseFunName(..), ConName(..), TyConName(..), Export(..), ModuleR(..))

--------------------------------------------------------------------------------

data Exp_ a
    = Bind_ Binder SName a a   -- TODO: prohibit meta binder here
    | Con_ (SName, a) [a]
    | ELit_ Lit
    | Fun_ (SName, a) [a]
    | App_ a a
    | Var_ SName a
    | TType_
  deriving (Show, Eq, Functor, Foldable, Traversable)

instance PShow Exp where pShowPrec p = text . show

pattern Bind a b c d = Exp (Bind_ a b c d)
pattern Con a b = Exp (Con_ a b)
pattern ELit a = Exp (ELit_ a)
pattern Fun a b = Exp (Fun_ a b)
pattern App a b = Exp (App_ a b)
pattern Var a b = Exp (Var_ a b)
pattern TType = Exp TType_

newtype Exp = Exp (Exp_ Exp)
  deriving (Show, Eq)

type ConvM a = StateT [SName] (Reader [SName]) a

toExp :: I.Exp -> Exp
toExp = flip runReader [] . flip evalStateT freshTypeVars . f
  where
    f = \case
        I.Var i -> asks $ uncurry Var . (!!! i)
        I.Bind b x y -> (gets head <* modify tail) >>= \n -> do
            t <- f x
            Bind b n t <$> local ((n, t):) (f y)
        I.Lam b x y -> (gets head <* modify tail) >>= \n -> do
            t <- f x
            Bind (BLam b) n t <$> local ((n, t):) (f y)
        I.Con (ConName s _ _ t) xs -> con s <$> f t <*> mapM f xs
        I.TyCon (TyConName s _ t _ _) xs -> con s <$> f t <*> mapM f xs
        I.ELit l -> pure $ ELit l
        I.Fun (FunName s _ t) xs -> fun s <$> f t <*> mapM f xs
        I.CaseFun (CaseFunName s t _) xs -> fun s <$> f t <*> mapM f xs
        I.App a b -> App <$> f a <*> f b
        I.Label _ _ x -> f x
        I.TType -> pure TType
        z -> error $ "toExp: " ++ show z

xs !!! i | i < 0 || i >= length xs = error $ show xs ++ " !! " ++ show i
xs !!! i = xs !! i

untick ('\'': s) = s
untick s = s

fun s t xs = Fun (untick s, t) xs

con (untick -> s) t xs = Con (s, t) xs

freeVars :: Exp -> S.Set SName
freeVars = \case
    Var n _ -> S.singleton n
    Con _ xs -> S.unions $ map freeVars xs
    ELit _ -> mempty
    Fun _ xs -> S.unions $ map freeVars xs
    App a b -> freeVars a `S.union` freeVars b
    Bind _ n a b -> freeVars a `S.union` (S.delete n $ freeVars b)
    TType -> mempty

type Ty = Exp

tyOf :: Exp -> Ty
tyOf = \case
    Lam h n t x -> Pi h n t $ tyOf x
    App f x -> app (tyOf f) x
    Var _ t -> t
    Pi{} -> Type
    Con (_, t) xs -> foldl app t xs
    Fun (_, t) xs -> foldl app t xs
    ELit l -> toExp $ I.litType l
    TType -> TType
    x -> error $ "tyOf: " ++ show x
  where
    app (Pi _ n a b) x = substE n x b

substE n x = \case
    z@(Var n' _) | n' == n -> x
                 | otherwise -> z 
    Bind h n' a b | n == n' -> Bind h n' (substE n x a) b
    Bind h n' a b -> Bind h n' (substE n x a) (substE n x b)
    Con cn xs -> Con cn (map (substE n x) xs)
    Fun cn xs -> Fun cn (map (substE n x) xs)
    TType -> TType
    App a b -> App (substE n x a) (substE n x b)
    z -> error $ "substE: " ++ show z

--------------------------------------------------------------------------------

type Pat = Exp

pattern PVar t n = Var n t

pattern PTuple :: [Pat] -> Pat
pattern PTuple a <- (const Nothing -> Just a)       -- todo

-------------

pattern EVar n <- Var n _
pattern TVar t n = Var n t

pattern Pi  h n a b = Bind (BPi h) n a b
pattern Lam h n a b = Bind (BLam h) n a b
pattern ELam n b <- (mkLam -> Just (n, b))

mkLam (Lam Visible n t b) = Just (Var n t, b)
mkLam _ = Nothing

pattern PrimN n xs <- Fun (n, t) (filterRelevant (n, 0) t -> xs) where PrimN n xs = Fun (n, error "PrimN: type") xs
pattern Prim1 n a = PrimN n [a]
pattern Prim2 n a b = PrimN n [a, b]
pattern Prim3 n a b c <- PrimN n [a, b, c]
pattern Prim4 n a b c d <- PrimN n [a, b, c, d]
pattern Prim5 n a b c d e <- PrimN n [a, b, c, d, e]

pattern EApp a b = Prim2 "app" a b

-- todo: remove
hackType = \case
    "Output" -> TType
    "Bool" -> TType
    n -> error $ "AN type for " ++ show n

filterRelevant i (Pi h n t t') (x: xs) = (if h == Visible || exception i then (x:) else id) $ filterRelevant (id *** (+1) $ i) (substE n x t') xs
  where
    -- todo: remove
    exception i = i `elem` [("ColorImage", 0), ("DepthImage", 0), ("StencilImage", 0)]
filterRelevant _ _ [] = []

pattern AN n xs <- Con (n, t) (filterRelevant (n, 0) t -> xs) where AN n xs = Con (n, hackType n) xs
pattern A0 n = AN n []
pattern A1 n a <- AN n [a]
pattern A2 n a b <- AN n [a, b]
pattern A3 n a b c <- AN n [a, b, c]
pattern A4 n a b c d <- AN n [a, b, c, d]
pattern A5 n a b c d e <- AN n [a, b, c, d, e]

pattern TCon0 n = A0 n
pattern TCon t n = Con (n, t) []

pattern Type   = TType
pattern Star   = TType
pattern TUnit  <- A0 "Tuple0"
pattern TBool  <- A0 "Bool"
pattern TWord  <- A0 "Word"
pattern TInt   <- A0 "Int"
pattern TFloat <- A0 "Float"
pattern TList n <- A1 "List" n

pattern TSampler <- A0 "Sampler" where TSampler = error "TSampler"
pattern TFrameBuffer a b <- A2 "FrameBuffer" a b
pattern Depth n     <- A1 "Depth" n
pattern Stencil n   <- A1 "Stencil" n
pattern Color n     <- A1 "Color" n

pattern Zero <- A0 "Zero"
pattern Succ n <- A1 "Succ" n

pattern TVec n a <- A2 "Vec" (Nat n) a
pattern TMat i j a <- A3 "Mat" (Nat i) (Nat j) a

pattern Nat n <- (fromNat -> Just n) -- where Nat n = toNat n
{-
toNat :: Int -> Exp
toNat 0 = Zero
toNat n = Succ (toNat $ n-1)
-}
fromNat :: Exp -> Maybe Int
fromNat Zero = Just 0
fromNat (Succ n) = (1 +) <$> fromNat n

pattern TTuple xs <- (getTuple -> Just xs)
pattern ETuple xs <- (getTuple -> Just xs)

getTuple = \case
    AN "Tuple0" [] -> Just []
    AN "Tuple2" [a, b] -> Just [a, b]
    AN "Tuple3" [a, b, c] -> Just [a, b, c]
    AN "Tuple4" [a, b, c, d] -> Just [a, b, c, d]
    _ -> Nothing

pattern ELet a b c <- (const Nothing -> Just (a, b, c)) where ELet a b c = error "ELet"
pattern EFieldProj :: Exp -> SName -> Exp
pattern EFieldProj a b <- (const Nothing -> Just (a, b))
pattern ERecord a <- (const Nothing -> Just a)

--------------------------------------------------------------------------------

showN = id
show5 = show

pattern ExpN a = a

type ErrorMsg = String
type ErrorT = ExceptT ErrorMsg
mapError f e = e
pattern InFile :: String -> ErrorMsg -> ErrorMsg
pattern InFile s e <- ((,) "?" -> (s, e)) where InFile _ e = e

type Info = (SourcePos, SourcePos, String)
type Infos = [Info]

type PolyEnv = I.GlobalEnv

joinPolyEnvs :: MonadError ErrorMsg m => Bool -> [PolyEnv] -> m PolyEnv
joinPolyEnvs _ = return . mconcat
getPolyEnv = id

type MName = SName
type VarMT = StateT FreshVars
type FreshVars = [String]
freshTypeVars = (flip (:) <$> map show [0..] <*> ['a'..'z'])

throwErrorTCM :: MonadError ErrorMsg m => Doc -> m a
throwErrorTCM d = throwError $ show d

infos = const []

type EName = SName

parseLC :: MonadError ErrorMsg m => FilePath -> String -> m ModuleR
parseLC f s = either throwError return (I.parse f s)

inference_ :: PolyEnv -> ModuleR -> ErrorT (WriterT Infos (VarMT Identity)) PolyEnv
inference_ pe m = either throwError return pe' where
    pe' = I.infer pe (I.removePreExps (I.mkGlobalEnv' (definitions m) `I.joinGlobalEnv'` I.extractGlobalEnv' pe) $ definitions m)

reduce = id

type Item = (I.Exp, I.Exp)

tyOfItem :: Item -> Exp
tyOfItem = toExp . snd

pattern ISubst a b <- ((,) () -> (a, (toExp -> b, tb)))

dummyPos :: SourcePos
dummyPos = newPos "" 0 0

showErr e = (dummyPos, dummyPos, e)

