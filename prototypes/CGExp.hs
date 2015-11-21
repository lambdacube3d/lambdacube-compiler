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
    , Lit (..)
    ) where

import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Set as S

import qualified Infer as I
import Infer (Binder(..), SName, Lit(..), Visibility(..), ConName(..))

--------------------------------------------------------------------------------

data Exp_ a
    = Bind_ Binder SName a a   -- TODO: prohibit meta binder here
    | Con_ (SName, a) [a] [a]
    | ELit_ Lit
    | Fun_ SName [a]
    | App_ a a
    | Var_ SName a
    | TType_
  deriving (Show, Eq, Functor, Foldable, Traversable)

pattern Bind a b c d = Exp (Bind_ a b c d)
pattern Con a b c = Exp (Con_ a b c)
pattern ELit a = Exp (ELit_ a)
pattern Fun a b = Exp (Fun_ a b)
pattern App a b = Exp (App_ a b)
pattern Var a b = Exp (Var_ a b)
pattern TType = Exp TType_

newtype Exp = Exp (Exp_ Exp)
  deriving (Show, Eq)

type ConvM a = StateT [SName] (Reader [SName]) a

toExp :: I.Exp -> Exp
toExp = flip runReader [] . flip evalStateT (flip (:) <$> map show [0..] <*> ['a'..'z']) . f
  where
    f = \case
        I.Var i -> asks $ uncurry Var . (!!! i)
        I.Bind b x y -> (gets head <* modify tail) >>= \n -> do
            t <- f x
            Bind b n t <$> local ((n, t):) (f y)
        I.Lam b x y -> (gets head <* modify tail) >>= \n -> do
            t <- f x
            Bind (BLam b) n t <$> local ((n, t):) (f y)
        I.Con (ConName s t) xs -> con s <$> f t <*> mapM f xs
        I.ELit l -> pure $ ELit l
        I.FunN s xs -> Fun s <$> mapM f xs
        I.App a b -> App <$> f a <*> f b
        I.Label _ _ x -> f x
        I.TType -> pure TType
        z -> error $ "toExp: " ++ show z

xs !!! i | i < 0 || i >= length xs = error $ show xs ++ " !! " ++ show i
xs !!! i = xs !! i

con s t xs = Con (s', t) ys zs where
    (ys, zs) = splitAt n xs
    s' | s `elem` ["FrameBuffer'", "VertexOut'", "FragmentOut'", "AccumulationContext'"] = init s
       | otherwise = s
    n = case s of
        "ScreenOut" -> 2
        "Accumulate" -> 4
        "Rasterize" -> 3
        "Transform" -> 3
        "Fetch" -> 3
        "FrameBuffer'" -> 5
        "FragmentOut'" -> 3
        "VertexOut'" -> 3
        "Attribute" -> 1
        "Smooth" -> 2
        "ColorImage" -> 5 -- !
        "V4" -> 1
        "AccumulationContext'" -> 3
        "ColorOp" -> 7
        "NoBlending" -> 1
        _ -> 0


freeVars :: Exp -> S.Set SName
freeVars = \case
    Var n _ -> S.singleton n
    Con _ xs ys -> S.unions $ map freeVars (xs ++ ys)
    ELit _ -> mempty
    Fun _ xs -> S.unions $ map freeVars xs
    App a b -> freeVars a `S.union` freeVars b
    Bind _ n a b -> freeVars a `S.union` (S.delete n $ freeVars b)
    TType -> mempty

type Ty = Exp

tyOf :: Exp -> Ty
tyOf = \case
    Lam h n t x -> Pi h n t $ tyOf x
--    App f x -> app (tyOf f) x
    Var _ t -> t
    Pi{} -> Type
    Con (_, t) xs ys -> foldl app t (xs ++ ys)
    TType -> TType
    x -> error $ "tyOf: " ++ show x
  where
    app (Pi _ n a b) x = substE n x b

substE n x = \case
    z@(Var n' _) | n' == n -> x
                 | otherwise -> z 
    Bind h n' a b | n == n' -> Bind h n' (substE n x a) b
    Bind h n' a b -> Bind h n' (substE n x a) (substE n x b)
    Con cn xs ys -> Con cn (map (substE n x) xs) (map (substE n x) ys)
    z -> error $ "substE: " ++ show z

--------------------------------------------------------------------------------

type Pat = Exp

pattern PVar t n = Var n t

pattern PTuple a <- (const Nothing -> Just a)

-------------

pattern EVar n <- Var n _
pattern TVar t n = Var n t

pattern Pi  h n a b = Bind (BPi h) n a b
pattern Lam h n a b = Bind (BLam h) n a b
pattern ELam n b <- (mkLam -> Just (n, b))

mkLam (Lam Visible n t b) = Just (Var n t, b)
mkLam _ = Nothing

pattern PrimN n xs = Fun n xs
pattern Prim1 n a = PrimN n [a]
pattern Prim2 n a b = PrimN n [a, b]
pattern Prim3 n a b c = PrimN n [a, b, c]
pattern Prim4 n a b c d = PrimN n [a, b, c, d]
pattern Prim5 n a b c d e = PrimN n [a, b, c, d, e]

pattern EApp a b = Prim2 "app" a b

pattern AN n xs <- Con (n, _) _ xs
pattern A0 n <- AN n []
pattern A1 n a <- AN n [a]
pattern A2 n a b <- AN n [a, b]
pattern A3 n a b c <- AN n [a, b, c]
pattern A4 n a b c d <- AN n [a, b, c, d]
pattern A5 n a b c d e <- AN n [a, b, c, d, e]

pattern TCon0 n <- A0 n

pattern Type   = TType
pattern TUnit  <- A0 "Unit"
pattern TBool  <- A0 "Bool"
pattern TWord  <- A0 "Word"
pattern TInt   <- A0 "Int"
pattern TFloat <- A0 "Float"
pattern TList n <- A1 "List" n

pattern TSampler <- A0 "Sampler" where TSampler = undefined
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

pattern TTuple xs <- (getTTuple -> Just xs) -- where TTuple xs = 
pattern ETuple xs <- (getETuple -> Just xs) -- where ETuple xs = 

getTTuple = \case
    AN "T2" [a, b] -> Just [a, b]
    _ -> Nothing
getETuple = \case
    AN "T2C" [_, _, a, b] -> Just [a, b]
    _ -> Nothing

pattern ELet a b c <- (const Nothing -> Just (a, b, c))
pattern EFieldProj a b <- (const Nothing -> Just (a, b))
pattern ERecord a <- (const Nothing -> Just a)

--------------------------------------------------------------------------------

ppShow = show

showN = id

pattern ExpN a = a

