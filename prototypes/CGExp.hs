{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RecursiveDo #-}
module CGExp
    ( module CGExp
    , Lit(..), Export(..), ModuleR(..)
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
import Infer (SName, Lit(..), Visibility(..), Export(..), ModuleR(..))

--------------------------------------------------------------------------------

data Exp_ a
    = Pi_ Visibility SName a a
    | Lam_ Visibility Pat a a
    | Con_ (SName, a) [a]
    | ELit_ Lit
    | Fun_ (SName, a) [a]
    | App_ a a
    | Var_ SName a
    | TType_
    | Let_ Pat a a
    | EFieldProj_ a SName
  deriving (Show, Eq, Functor, Foldable, Traversable)

instance PShow Exp where pShowPrec p = text . show

pattern Pi h n a b = Exp (Pi_ h n a b)
pattern Lam h n a b = Exp (Lam_ h n a b)
pattern Con a b = Exp (Con_ a b)
pattern ELit a = Exp (ELit_ a)
pattern Fun a b = Exp (Fun_ a b)
pattern EApp a b = Exp (App_ a b)
pattern Var a b = Exp (Var_ a b)
pattern TType = Exp TType_
pattern ELet a b c = Exp (Let_ a b c)
pattern EFieldProj a b = Exp (EFieldProj_ a b)

newtype Exp = Exp (Exp_ Exp)
  deriving (Show, Eq)

type ConvM a = StateT [SName] (Reader [SName]) a

newName = gets head <* modify tail

toExp :: I.Exp -> Exp
toExp = flip runReader [] . flip evalStateT freshTypeVars . f
  where
    f = \case
        I.FunN "swizzvector" [_, _, _, exp, getSwizzVec -> Just (concat -> s)] -> newName >>= \n -> do
            e <- f exp
            return $ app' (EFieldProj (Pi Visible n (tyOf e) (TVec (length s) TFloat)) s) e
        I.FunN "swizzscalar" [_, _, exp, mkSwizzStr -> Just s] -> newName >>= \n -> do
            e <- f exp
            return $ app' (EFieldProj (Pi Visible n (tyOf e) TFloat) s) e
        I.Var i -> asks $ uncurry Var . (!!! i)
        I.Pi b x y -> newName >>= \n -> do
            t <- f x
            Pi b n t <$> local ((n, t):) (f y)
        I.Lam b x y -> newName >>= \n -> do
            t <- f x
            Lam b (PVar t n) t <$> local ((n, t):) (f y)
        I.Con (I.ConName s _ _ t) xs -> con s <$> f t <*> mapM f xs
        I.TyCon (I.TyConName s _ _ t _ _) xs -> con s <$> f t <*> mapM f xs
        I.ELit l -> pure $ ELit l
        I.Fun (I.FunName s _ t) xs -> fun s <$> f t <*> mapM f xs
        I.CaseFun (I.CaseFunName s t _) xs -> fun s <$> f t <*> mapM f xs
        I.App a b -> app' <$> f a <*> f b
        I.Label x _ -> f x
        I.TType -> pure TType
        I.LabelEnd x -> f x
        z -> error $ "toExp: " ++ show z

getSwizzVec = \case
    I.VV2 _ (mkSwizzStr -> Just sx) (mkSwizzStr -> Just sy) -> Just [sx, sy]
    I.VV3 _ (mkSwizzStr -> Just sx) (mkSwizzStr -> Just sy) (mkSwizzStr -> Just sz) -> Just [sx, sy, sz]
    I.VV4 _ (mkSwizzStr -> Just sx) (mkSwizzStr -> Just sy) (mkSwizzStr -> Just sz) (mkSwizzStr -> Just sw) -> Just [sx, sy, sz, sw]
    _ -> Nothing

mkSwizzStr = \case
    I.ConN "Sx" [] -> Just "x"
    I.ConN "Sy" [] -> Just "y"
    I.ConN "Sz" [] -> Just "z"
    I.ConN "Sw" [] -> Just "w"
    _ -> Nothing

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
    EApp a b -> freeVars a `S.union` freeVars b
    Pi _ n a b -> freeVars a `S.union` (S.delete n $ freeVars b)
    Lam _ n a b -> freeVars a `S.union` (foldr S.delete (freeVars b) (patVars n))
    EFieldProj a _ -> freeVars a
    TType -> mempty
    ELet n a b -> freeVars a `S.union` (foldr S.delete (freeVars b) (patVars n))

type Ty = Exp

tyOf :: Exp -> Ty
tyOf = \case
    Lam h (PVar _ n) t x -> Pi h n t $ tyOf x
    EApp f x -> app (tyOf f) x
    Var _ t -> t
    Pi{} -> Type
    Con (_, t) xs -> foldl app t xs
    Fun (_, t) xs -> foldl app t xs
    ELit l -> toExp $ I.litType l
    TType -> TType
    ELet a b c -> tyOf $ EApp (ELam a c) b
    EFieldProj t s -> t
    x -> error $ "tyOf: " ++ show x
  where
    app (Pi _ n a b) x = substE n x b

substE n x = \case
    z@(Var n' _) | n' == n -> x
                 | otherwise -> z 
    Pi h n' a b | n == n' -> Pi h n' (substE n x a) b
    Pi h n' a b -> Pi h n' (substE n x a) (substE n x b)
    Lam h n' a b -> Lam h n' (substE n x a) $ if n `elem` patVars n' then b else substE n x b
    Con cn xs -> Con cn (map (substE n x) xs)
    Fun cn xs -> Fun cn (map (substE n x) xs)
    TType -> TType
    EApp a b -> app' (substE n x a) (substE n x b)
    z -> error $ "substE: " ++ show z

app' (Lam _ (PVar _ n) _ x) b = substE n b x
app' a b = EApp a b

--------------------------------------------------------------------------------

data Pat
    = PVar Exp SName
    | PTuple [Pat]
    deriving (Eq, Show)

instance PShow Pat where pShowPrec p = text . show

patVars (PVar _ n) = [n]
patVars (PTuple ps) = concatMap patVars ps

patTy (PVar t _) = t
patTy (PTuple ps) = Con ("Tuple" ++ show (length ps), tupTy $ length ps) $ map patTy ps

tupTy n = foldr (:~>) Type $ replicate n Type

-------------

pattern EVar n <- Var n _
pattern TVar t n = Var n t

pattern ELam n b <- (mkLam -> Just (n, b)) where ELam n b = eLam n b

pattern a :~> b = Pi Visible "" a b
infixr 1 :~>

eLam p x = Lam Visible p (patTy p) x

mkLam (Lam Visible p t b) = Just (p, b)
mkLam _ = Nothing

pattern PrimN n xs <- Fun (n, t) (filterRelevant (n, 0) t -> xs) where PrimN n xs = Fun (n, hackType n) xs
pattern Prim1 n a = PrimN n [a]
pattern Prim2 n a b = PrimN n [a, b]
pattern Prim3 n a b c <- PrimN n [a, b, c]
pattern Prim4 n a b c d <- PrimN n [a, b, c, d]
pattern Prim5 n a b c d e <- PrimN n [a, b, c, d, e]

-- todo: remove
hackType = \case
    "Output" -> TType
    "Bool" -> TType
    "Float" -> TType
    "Nat" -> TType
    "Zero" -> TNat
    "Succ" -> TNat :~> TNat
    "String" -> TType
    "Sampler" -> TType
    "VecS" -> TType :~> TNat :~> TType
--    "EFieldProj" -> Pi Visible "projt" TType $ Pi Visible "projt2" TString $ Pi Visible "projvec" (TVec (error "pn1") TFloat) (TVec (error "pn2") TFloat)
    n -> error $ "type of " ++ show n

filterRelevant _ _ [] = []
filterRelevant i (Pi h n t t') (x: xs) = (if h == Visible || exception i then (x:) else id) $ filterRelevant (id *** (+1) $ i) (substE n x t') xs
  where
    -- todo: remove
    exception i = i `elem` [("ColorImage", 0), ("DepthImage", 0), ("StencilImage", 0)]

pattern AN n xs <- Con (n, t) (filterRelevant (n, 0) t -> xs) where AN n xs = Con (n, hackType n) xs
pattern A0 n = AN n []
pattern A1 n a = AN n [a]
pattern A2 n a b = AN n [a, b]
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
pattern TNat   = A0 "Nat"
pattern TFloat = A0 "Float"
pattern TString = A0 "String"
pattern TList n <- A1 "List" n

pattern TSampler = A0 "Sampler"
pattern TFrameBuffer a b <- A2 "FrameBuffer" a b
pattern Depth n     <- A1 "Depth" n
pattern Stencil n   <- A1 "Stencil" n
pattern Color n     <- A1 "Color" n

pattern Zero = A0 "Zero"
pattern Succ n = A1 "Succ" n

pattern TVec n a = A2 "VecS" a (Nat n)
pattern TMat i j a <- A3 "Mat" (Nat i) (Nat j) a

pattern Nat n <- (fromNat -> Just n) where Nat n = toNat n

toNat :: Int -> Exp
toNat 0 = Zero
toNat n = Succ (toNat $ n-1)

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
    AN "Tuple5" [a, b, c, d, e] -> Just [a, b, c, d, e]
    AN "Tuple6" [a, b, c, d, e, f] -> Just [a, b, c, d, e, f]
    AN "Tuple7" [a, b, c, d, e, f, g] -> Just [a, b, c, d, e, f, g]
    _ -> Nothing

pattern ERecord a <- (const Nothing -> Just a)

--------------------------------------------------------------------------------

showN = id
show5 = show

pattern ExpN a = a

newtype ErrorMsg = ErrorMsg String
instance Show ErrorMsg where show (ErrorMsg s) = s

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
throwErrorTCM d = throwError $ ErrorMsg $ show d

infos = const []

type EName = SName

parseLC :: MonadError ErrorMsg m => FilePath -> String -> m ModuleR
parseLC f s = either (throwError . ErrorMsg) return (I.parse f s)

inference_ :: PolyEnv -> ModuleR -> ErrorT (WriterT Infos (VarMT Identity)) PolyEnv
inference_ pe m = mdo
    defs <- either (throwError . ErrorMsg) return $ definitions m $ I.mkGlobalEnv' defs `I.joinGlobalEnv'` I.extractGlobalEnv' pe
    either (throwError . ErrorMsg) return $ I.infer pe defs

reduce = id

type Item = (I.Exp, I.Exp)

tyOfItem :: Item -> Exp
tyOfItem = toExp . snd

pattern ISubst a b <- ((,) () -> (a, (toExp -> b, tb)))

dummyPos :: SourcePos
dummyPos = newPos "" 0 0

showErr e = (dummyPos, dummyPos, e)

