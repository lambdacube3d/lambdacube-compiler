{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}  -- TODO: remove
{-# OPTIONS_GHC -fno-warn-unused-binds #-}  -- TODO: remove
-- {-# OPTIONS_GHC -O0 #-}
module LambdaCube.Compiler.Infer
    ( Binder (..), SName, Lit(..), Visibility(..), Export(..), Module(..)
    , Exp (..), ExpType, GlobalEnv
    , pattern Var, pattern Fun, pattern CaseFun, pattern TyCaseFun, pattern App_, pattern PMLabel, pattern FixLabel
    , pattern Con, pattern TyCon, pattern Pi, pattern Lam
    , outputType, boolType, trueExp
    , down
    , litType
    , initEnv, Env(..), pattern EBind2
    , Infos(..), listInfos, ErrorMsg(..), PolyEnv(..), ErrorT, throwErrorTCM, parseLC, joinPolyEnvs, filterPolyEnv, inference_
    , ImportItems (..)
    , SI(..), Range(..)
    , nType, neutType, appTy, mkConPars
    , MaxDB(..)
    ) where
import Data.Monoid
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Map as Map

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Identity
import Control.Arrow hiding ((<+>))
import Control.DeepSeq

import LambdaCube.Compiler.Pretty hiding (Doc, braces, parens)
import LambdaCube.Compiler.Lexer
import LambdaCube.Compiler.Parser

-------------------------------------------------------------------------------- core expression representation

data Exp
    = TType
    | ELit Lit
    | Con_   MaxDB ConName   !Int [Exp]
    | TyCon_ MaxDB TyConName [Exp]
    | Pi_  MaxDB Visibility Exp Exp
    | Lam_ MaxDB Exp
    | Neut Neutral
    | Label LabelKind Exp{-folded expression-} Exp{-unfolded expression-}
    | LabelEnd_ LEKind Exp
  deriving (Show)

data Neutral
    = Fun__       MaxDB FunName       [Exp]
    | CaseFun__   MaxDB CaseFunName   [Exp]    -- todo: neutral at the end
    | TyCaseFun__ MaxDB TyCaseFunName [Exp]    -- todo: neutral at the end
    | App__ MaxDB Neutral Exp
    | Var_ !Int                 -- De Bruijn variable
  deriving (Show)

data ConName = ConName SName MFixity Int{-ordinal number, e.g. Zero:0, Succ:1-} TyConName Type

data TyConName = TyConName SName MFixity Int{-num of indices-} Type [ConName]{-constructors-} CaseFunName

data FunName = FunName SName MFixity Type

data CaseFunName = CaseFunName SName Type Int{-num of parameters-}

data TyCaseFunName = TyCaseFunName SName Type

type Type = Exp
type ExpType = (Exp, Type)
type SExp2 = SExp' ExpType

instance Show ConName where show (ConName n _ _ _ _) = n
instance Eq ConName where ConName n _ _ _ _ == ConName n' _ _ _ _ = n == n'
instance Show TyConName where show (TyConName n _ _ _ _ _) = n
instance Eq TyConName where TyConName n _ _ _ _ _ == TyConName n' _ _ _ _ _ = n == n'
instance Show FunName where show (FunName n _ _) = n
instance Eq FunName where FunName n _ _ == FunName n' _ _ = n == n'
instance Show CaseFunName where show (CaseFunName n _ _) = caseName n
instance Eq CaseFunName where CaseFunName n _ _ == CaseFunName n' _ _ = n == n'
instance Show TyCaseFunName where show (TyCaseFunName n _) = MatchName n
instance Eq TyCaseFunName where TyCaseFunName n _ == TyCaseFunName n' _ = n == n'

-------------------------------------------------------------------------------- auxiliary functions and patterns

infixl 2 `App`, `app_`
infixr 1 :~>

pattern Fun_ a b <- Fun__ _ a b where Fun_ a b = Fun__ (foldMap maxDB_ b) a b
pattern CaseFun_ a b <- CaseFun__ _ a b where CaseFun_ a b = CaseFun__ (foldMap maxDB_ b) a b
pattern TyCaseFun_ a b <- TyCaseFun__ _ a b where TyCaseFun_ a b = TyCaseFun__ (foldMap maxDB_ b) a b
pattern App_ a b <- App__ _ a b where App_ a b = App__ (maxDB_ a <> maxDB_ b) a b
pattern Fun a b = Neut (Fun_ a b)
pattern CaseFun a b = Neut (CaseFun_ a b)
pattern TyCaseFun a b = Neut (TyCaseFun_ a b)
pattern App a b <- Neut (App_ (Neut -> a) b)
pattern Var a = Neut (Var_ a)

conParams (conTypeName -> TyConName _ _ _ _ _ (CaseFunName _ _ pars)) = pars
mkConPars n (snd . getParams -> TyCon (TyConName _ _ _ _ _ (CaseFunName _ _ pars)) xs) = take (min n pars) xs
conName a b c d = ConName a b c (get $ snd $ getParams d) d
  where
    get (TyCon s _) = s

pattern Closed :: () => Up a => a -> a
pattern Closed a <- a where Closed a = closedExp a

pattern Con x n y <- Con_ _ x n y where Con x n y = Con_ (foldMap maxDB_ y) x n y
pattern ConN s a   <- Con (ConName s _ _ _ _) _ a
pattern TCon s i t a <- Con (ConName s _ i _ t) _ a where TCon s i t a = Con (conName s Nothing i t) 0 a  -- todo: don't match on type
pattern TyCon x y <- TyCon_ _ x y where TyCon x y = TyCon_ (foldMap maxDB_ y) x y
pattern Lam y <- Lam_ _ y where Lam y = Lam_ (lowerDB (maxDB_ y)) y
pattern Pi v x y <- Pi_ _ v x y where Pi v x y = Pi_ (maxDB_ x <> lowerDB (maxDB_ y)) v x y
pattern FunN a b <- Fun (FunName a _ _) b
pattern TFun a t b <- Fun (FunName a _ t) b where TFun a t b = Fun (FunName a Nothing t) b
pattern TFun' a t b <- Fun_ (FunName a _ t) b where TFun' a t b = Fun_ (FunName a Nothing t) b
pattern TyConN s a <- TyCon (TyConName s _ _ _ _ _) a
pattern TTyCon s t a <- TyCon (TyConName s _ _ t _ _) a where TTyCon s t a = TyCon (TyConName s Nothing (error "todo: inum") t (error "todo: tcn cons 2") $ CaseFunName (error "TTyCon-A") (error "TTyCon-B") $ length a) a
pattern TTyCon0 s  <- TyCon (TyConName s _ _ TType _ _) [] where TTyCon0 s = Closed $ TyCon (TyConName s Nothing 0 TType (error "todo: tcn cons 3") $ CaseFunName (error "TTyCon0-A") (error "TTyCon0-B") 0) []
pattern a :~> b = Pi Visible a b

pattern Unit        = TTyCon0 "'Unit"
pattern TInt        = TTyCon0 "'Int"
pattern TNat        = TTyCon0 "'Nat"
pattern TBool       = TTyCon0 "'Bool"
pattern TFloat      = TTyCon0 "'Float"
pattern TString     = TTyCon0 "'String"
pattern TChar       = TTyCon0 "'Char"
pattern TOrdering   = TTyCon0 "'Ordering"
pattern TTuple2 a b = TTyCon "'Tuple2" (TType :~> TType :~> TType) [a, b]
pattern TVec a b    = TTyCon "'VecS" (TType :~> TNat :~> TType) [b, a]
pattern Empty s   <- TyCon (TyConName "'Empty" _ _ _ _ _) [EString s] where
        Empty s    = TyCon (TyConName "'Empty" Nothing (error "todo: inum2_") (TString :~> TType) (error "todo: tcn cons 3_") $ error "Empty") [EString s]

pattern TT          = Closed (TCon "TT" 0 Unit [])
pattern Zero        = Closed (TCon "Zero" 0 TNat [])
pattern Succ n      = TCon "Succ" 1 (TNat :~> TNat) [n]

pattern CstrT t a b = TFun "'EqCT" (TType :~> Var 0 :~> Var 1 :~> TType) [t, a, b]
pattern CstrT' t a b = TFun' "'EqCT" (TType :~> Var 0 :~> Var 1 :~> TType) [t, a, b]
pattern ReflCstr x  = TFun "reflCstr" (TType :~> CstrT TType (Var 0) (Var 0)) [x]
pattern Coe a b w x = TFun "coe" (TType :~> TType :~> CstrT TType (Var 1) (Var 0) :~> Var 2 :~> Var 2) [a,b,w,x]
pattern ParEval t a b = TFun "parEval" (TType :~> Var 0 :~> Var 1 :~> Var 2) [t, a, b]
pattern Undef t     = TFun "undefined" (Pi Hidden TType (Var 0)) [t]
pattern T2 a b      = TFun "'T2" (TType :~> TType :~> TType) [a, b]
pattern T2C a b     = TFun "t2C" (Unit :~> Unit :~> Unit) [a, b]
pattern CSplit a b c <- FunN "'Split" [a, b, c]

pattern EInt a      = ELit (LInt a)
pattern EFloat a    = ELit (LFloat a)
pattern EChar a     = ELit (LChar a)
pattern EString a   = ELit (LString a)
pattern EBool a <- (getEBool -> Just a) where EBool = Closed . mkBool
pattern ENat n <- (fromNatE -> Just n) where ENat = Closed . toNatE

pattern LCon <- (isCon -> True)
pattern CFun <- (isCaseFun -> True)
pattern NoTup <- (noTup -> True)

--pattern Sigma a b  <- TyConN "Sigma" [a, Lam b] where Sigma a b = TTyCon "Sigma" (error "sigmatype") [a, Lam Visible a{-todo: don't duplicate-} b]
--pattern TVec a b    = TTyCon "'Vec" (TNat :~> TType :~> TType) [a, b]
--pattern Tuple2 a b c d = TCon "Tuple2" 0 Tuple2Type [a, b, c, d]
--pattern Tuple0      = TCon "Tuple0" 0 TTuple0 []
--pattern TTuple0 :: Exp
--pattern TTuple0  <- _ where TTuple0   = TTyCon0 "'Tuple0"
--pattern Tuple2Type :: Exp
--pattern Tuple2Type  <- _ where Tuple2Type   = Pi Hidden TType $ Pi Hidden TType $ Var 1 :~> Var 1 :~> TTuple2 (Var 3) (Var 2)
--tTuple3 a b c = TTyCon "'Tuple3" (TType :~> TType :~> TType :~> TType) [a, b, c]

toNatE :: Int -> Exp
toNatE 0         = Zero
toNatE n | n > 0 = Succ (toNatE (n - 1))

fromNatE :: Exp -> Maybe Int
fromNatE Zero = Just 0
fromNatE (Succ n) = (1 +) <$> fromNatE n
fromNatE _ = Nothing

mkBool False = TCon "False" 0 TBool []
mkBool True  = TCon "True"  1 TBool []

getEBool (ConN "False" []) = Just False
getEBool (ConN "True" []) = Just True
getEBool _ = Nothing

isCaseFun (Fun f _) = True
isCaseFun (CaseFun f _) = True
isCaseFun (TyCaseFun f _) = True
isCaseFun _ = False

isCon = \case
    TType   -> True
    Con _ _ _ -> True
    TyCon _ _ -> True
    ELit _  -> True
    _ -> False

mkOrdering x = Closed $ case x of
    LT -> TCon "LT" 0 TOrdering []
    EQ -> TCon "EQ" 1 TOrdering []
    GT -> TCon "GT" 2 TOrdering []

noTup (TyConN s _) = take 6 s /= "'Tuple" -- todo
noTup _ = False

conTypeName :: ConName -> TyConName
conTypeName (ConName _ _ _ t _) = t

outputType = TTyCon0 "'Output"
boolType = TBool
trueExp = EBool True

-------------------------------------------------------------------------------- label handling

data LabelKind
    = LabelPM   -- pattern match label
    | LabelFix  -- fix unfold label
  deriving (Show)

pattern PMLabel x y  = Label LabelPM x y
pattern FixLabel x y = Label LabelFix x y

data LEKind
    = LEPM
    | LEClosed
  deriving (Show, Eq)

pattern LabelEnd x = LabelEnd_ LEPM x
--pattern ClosedExp x = LabelEnd_ LEClosed x

label LabelFix x y = FixLabel x y
label LabelPM x (UL (LabelEnd y)) = y
label LabelPM x y = PMLabel x y

pattern UL a <- (unlabel -> a) where UL = unlabel

unlabel (PMLabel a _) = unlabel a
unlabel (FixLabel _ a) = unlabel a
--unlabel (LabelEnd_ _ a) = unlabel a
unlabel a = a

pattern UL' a <- (unlabel' -> a) where UL' = unlabel'

--unlabel (PMLabel a _) = unlabel a
--unlabel (FixLabel _ a) = unlabel a
unlabel' (LabelEnd_ _ a) = unlabel' a
unlabel' a = a


-------------------------------------------------------------------------------- low-level toolbox

class Up a => Subst b a where
    subst :: Int -> b -> a -> a

down :: (Subst Exp a) => Int -> a -> Maybe a
down t x | used t x = Nothing
         | otherwise = Just $ subst t (error "impossible: down" :: Exp) x

instance Eq Exp where
    PMLabel a _ == PMLabel a' _ = a == a'
    FixLabel a _ == FixLabel a' _ = a == a'
    FixLabel _ a == a' = a == a'
    a == FixLabel _ a' = a == a'
    LabelEnd_ k a == a' = a == a'
    a == LabelEnd_ k' a' = a == a'
    Lam a == Lam a' = a == a'
    Pi a b c == Pi a' b' c' = (a, b, c) == (a', b', c')
    Con a n b == Con a' n' b' = (a, n, b) == (a', n', b')
    TyCon a b == TyCon a' b' = (a, b) == (a', b')
    TType == TType = True
    ELit l == ELit l' = l == l'
    Neut a == Neut a' = a == a'
    _ == _ = False

instance Eq Neutral where
    Fun_ a b == Fun_ a' b' = (a, b) == (a', b')
    CaseFun_ a b == CaseFun_ a' b' = (a, b) == (a', b')
    TyCaseFun_ a b == TyCaseFun_ a' b' = (a, b) == (a', b')
    App_ a b == App_ a' b' = (a, b) == (a', b')
    Var_ a == Var_ a' = a == a'
    _ == _ = False

isClosed (maxDB_ -> MaxDB x) = isNothing x

-- 0 means that no free variable is used
-- 1 means that only var 0 is used
maxDB = max 0 . fromMaybe 0 . getMaxDB . maxDB_
upDB n (MaxDB i) = MaxDB $ max 0 . (+n) <$> i

free x | isClosed x = mempty
free x = fold (\i k -> Set.fromList [k - i | k >= i]) 0 x

instance Up Exp where
    up_ 0 = \_ e -> e
    up_ n = f where
        f i e | isClosed e = e
        f i e = case e of
            Lam_ md b -> Lam_ (upDB n md) (f (i+1) b)
            Pi_ md h a b -> Pi_ (upDB n md) h (f i a) (f (i+1) b)
            Con_ md s pn as  -> Con_ (upDB n md) s pn $ map (f i) as
            TyCon_ md s as -> TyCon_ (upDB n md) s $ map (f i) as
            Neut x -> Neut $ up_ n i x
            Label lk x y -> Label lk (f i x) $ f i y
            LabelEnd_ k x -> LabelEnd_ k $ f i x

    used i e
        | i >= maxDB e = False
        | otherwise = ((getAny .) . fold ((Any .) . (==))) i e

    fold f i = \case
        PMLabel x _ -> fold f i x
        FixLabel _ x -> fold f i x
        Lam b -> {-fold f i t <>  todo: explain why this is not needed -} fold f (i+1) b
        Pi _ a b -> fold f i a <> fold f (i+1) b
        Con _ _ as -> foldMap (fold f i) as
        TyCon _ as -> foldMap (fold f i) as
        TType -> mempty
        ELit _ -> mempty
        LabelEnd_ _ x -> fold f i x
        Neut x -> fold f i x

    maxDB_ = \case
        Lam_ c _ -> c
        Pi_ c _ _ _ -> c
        Con_ c _ _ _ -> c
        TyCon_ c _ _ -> c

        Neut x -> maxDB_ x
        PMLabel x y -> maxDB_ x -- `combineDB` maxDB_ y
        FixLabel x y -> maxDB_ x <> maxDB_ y
        TType -> mempty
        ELit _ -> mempty
        LabelEnd_ _ x -> maxDB_ x

    closedExp = \case
        Lam_ _ c -> Lam_ mempty c
        Pi_ _ a b c -> Pi_ mempty a b c
        Con_ _ a b c -> Con_ mempty a b c
        TyCon_ _ a b -> TyCon_ mempty a b
        Neut a -> Neut $ closedExp a
        e -> e

instance Subst Exp Exp where
    subst i0 x = f i0
      where
        f i (Neut n) = substNeut n
          where
            substNeut e | isClosed e = Neut e
            substNeut e = case e of
                Var_ k -> case compare k i of GT -> Var $ k - 1; LT -> Var k; EQ -> up (i - i0) x
                Fun_ s as  -> eval $ Fun s $ f i <$> as
                CaseFun_ s as  -> eval $ CaseFun s $ f i <$> as
                TyCaseFun_ s as -> eval $ TyCaseFun s $ f i <$> as
                App_ a b  -> app_ (substNeut a) (f i b)
        f i e | {-i >= maxDB e-} isClosed e = e
        f i e = case e of
            Label lk z v -> label lk (f i z) $ f i v
            Lam b -> Lam (f (i+1) b)
            Con s n as  -> Con s n $ f i <$> as
            Pi h a b  -> Pi h (f i a) (f (i+1) b)
            TyCon s as -> TyCon s $ f i <$> as
            LabelEnd_ k a -> LabelEnd_ k $ f i a

instance Up Neutral where

    up_ n = f where
        f i e | isClosed e = e
        f i e = case e of
            Var_ k -> Var_ $ if k >= i then k+n else k
            Fun__ md s as  -> Fun__ (upDB n md) s $ map (up_ n i) as
            CaseFun__ md s as  -> CaseFun__ (upDB n md) s $ map (up_ n i) as
            TyCaseFun__ md s as -> TyCaseFun__ (upDB n md) s $ map (up_ n i) as
            App__ md a b -> App__ (upDB n md) (up_ n i a) (up_ n i b)

    used i e
        | i >= maxDB e = False
        | otherwise = ((getAny .) . fold ((Any .) . (==))) i e

    fold f i = \case
        Var_ k -> f i k
        Fun_ _ as -> foldMap (fold f i) as
        CaseFun_ _ as -> foldMap (fold f i) as
        TyCaseFun_ _ as -> foldMap (fold f i) as
        App_ a b -> fold f i a <> fold f i b

    maxDB_ = \case
        Var_ k -> varDB k
        Fun__ c _ as -> c
        CaseFun__ c _ as -> c
        TyCaseFun__ c _ as -> c
        App__ c a b -> c

    closedExp = \case
        x@Var_{} -> error "impossible"
        Fun__ _ a as -> Fun__ mempty a as
        CaseFun__ _ a as -> CaseFun__ mempty a as
        TyCaseFun__ _ a as -> TyCaseFun__ mempty a as
        App__ _ a b -> App__ mempty a b

instance (Subst x a, Subst x b) => Subst x (a, b) where
    subst i x (a, b) = (subst i x a, subst i x b)

varType :: String -> Int -> Env -> (Binder, Exp)
varType err n_ env = f n_ env where
    f n (EAssign i (x, _) es) = second (subst i x) $ f (if n < i then n else n+1) es
    f n (EBind2 b t es)  = if n == 0 then (b, up 1 t) else second (up 1) $ f (n-1) es
    f n (ELet2 _ (x, t) es) = if n == 0 then (BLam Visible{-??-}, up 1 t) else second (up 1) $ f (n-1) es
    f n e = either (error $ "varType: " ++ err ++ "\n" ++ show n_ ++ "\n" ++ ppShow env) (f n) $ parent e

-------------------------------------------------------------------------------- reduction

eval = \case
    App a b -> app_ a b
    CstrT TType a b -> cstrT_ TType a b
    CstrT t a b -> cstrT t a b
    ReflCstr a -> reflCstr a
    Coe a b TT d -> d

    CaseFun (CaseFunName _ t pars) (drop (pars + 1) -> ps@(last -> UL (Con (ConName _ _ i _ _) _ vs))) | i /= (-1) -> foldl app_ (ps !! i) vs

    TyCaseFun (TyCaseFunName n ty) [_, t, UL (TyCon (TyConName n' _ _ _ _ _) vs), f] | n == n' -> foldl app_ t vs
    TyCaseFun (TyCaseFunName n ty) [_, t, LCon, f] -> f
    T2 a b -> t2 a b
    T2C a b -> t2C a b
    ParEval t a b -> parEval a b
      where
        parEval (LabelEnd x) _ = LabelEnd x
        parEval _ (LabelEnd x) = LabelEnd x
        parEval a b = ParEval t a b

{- todo: generate
    Fun n@(FunName "natElim" _ _) [a, z, s, Succ x] -> let      -- todo: replace let with better abstraction
                sx = s `app_` x
            in sx `app_` eval (Fun n [a, z, s, x])
    FunN "natElim" [_, z, s, Zero] -> z
    Fun na@(FunName "finElim" _ _) [m, z, s, n, ConN "FSucc" [i, x]] -> let six = s `app_` i `app_` x-- todo: replace let with better abstraction
        in six `app_` eval (Fun na [m, z, s, i, x])
    FunN "finElim" [m, z, s, n, ConN "FZero" [i]] -> z `app_` i
-}

    FunN "unsafeCoerce" [_, _, x@LCon] -> x

    -- general compiler primitives
    FunN "primAddInt" [EInt i, EInt j] -> EInt (i + j)
    FunN "primSubInt" [EInt i, EInt j] -> EInt (i - j)
    FunN "primModInt" [EInt i, EInt j] -> EInt (i `mod` j)
    FunN "primSqrtFloat" [EFloat i] -> EFloat $ sqrt i
    FunN "primRound" [EFloat i] -> EInt $ round i
    FunN "primIntToFloat" [EInt i] -> EFloat $ fromIntegral i
    FunN "primCompareInt" [EInt x, EInt y] -> mkOrdering $ x `compare` y
    FunN "primCompareFloat" [EFloat x, EFloat y] -> mkOrdering $ x `compare` y
    FunN "primCompareChar" [EChar x, EChar y] -> mkOrdering $ x `compare` y
    FunN "primCompareString" [EString x, EString y] -> mkOrdering $ x `compare` y

    -- LambdaCube 3D specific primitives
    FunN "PrimGreaterThan" [_, _, _, _, _, _, _, x, y] | Just r <- twoOpBool (>) x y -> r
    FunN "PrimGreaterThanEqual" [_, _, _, _, _, _, _, x, y] | Just r <- twoOpBool (>=) x y -> r
    FunN "PrimLessThan" [_, _, _, _, _, _, _, x, y] | Just r <- twoOpBool (<) x y -> r
    FunN "PrimLessThanEqual" [_, _, _, _, _, _, _, x, y] | Just r <- twoOpBool (<=) x y -> r
    FunN "PrimEqualV" [_, _, _, _, _, _, _, x, y] | Just r <- twoOpBool (==) x y -> r
    FunN "PrimNotEqualV" [_, _, _, _, _, _, _, x, y] | Just r <- twoOpBool (/=) x y -> r
    FunN "PrimEqual" [_, _, _, x, y] | Just r <- twoOpBool (==) x y -> r
    FunN "PrimNotEqual" [_, _, _, x, y] | Just r <- twoOpBool (/=) x y -> r
    FunN "PrimSubS" [_, _, _, _, x, y] | Just r <- twoOp (-) x y -> r
    FunN "PrimSub"  [_, _, x, y] | Just r <- twoOp (-) x y -> r
    FunN "PrimAddS" [_, _, _, _, x, y] | Just r <- twoOp (+) x y -> r
    FunN "PrimAdd"  [_, _, x, y] | Just r <- twoOp (+) x y -> r
    FunN "PrimMulS" [_, _, _, _, x, y] | Just r <- twoOp (*) x y -> r
    FunN "PrimMul"  [_, _, x, y] | Just r <- twoOp (*) x y -> r
    FunN "PrimDivS" [_, _, _, _, _, x, y] | Just r <- twoOp_ (/) div x y -> r
    FunN "PrimDiv"  [_, _, _, _, _, x, y] | Just r <- twoOp_ (/) div x y -> r
    FunN "PrimModS" [_, _, _, _, _, x, y] | Just r <- twoOp_ modF mod x y -> r
    FunN "PrimMod"  [_, _, _, _, _, x, y] | Just r <- twoOp_ modF mod x y -> r
    FunN "PrimNeg"  [_, x] | Just r <- oneOp negate x -> r
    FunN "PrimAnd"  [EBool x, EBool y] -> EBool (x && y)
    FunN "PrimOr"   [EBool x, EBool y] -> EBool (x || y)
    FunN "PrimXor"  [EBool x, EBool y] -> EBool (x /= y)
    FunN "PrimNot"  [_, _, _, EBool x] -> EBool $ not x

    x -> x
  where
    cstrT t (UL a) (UL a') | a == a' = Unit
    cstrT t (ConN "Succ" [a]) (ConN "Succ" [a']) = cstrT TNat a a'
    cstrT t (FixLabel _ a) a' = cstrT t a a'
    cstrT t a (FixLabel _ a') = cstrT t a a'
    cstrT t a a' = CstrT t a a'

    -- todo: use typ
    cstrT_ typ = cstr__ []
      where
        cstr__ = cstr_

        cstr_ [] (UL a) (UL a') | a == a' = Unit
        cstr_ ns (LabelEnd_ k a) a' = cstr_ ns a a'
        cstr_ ns a (LabelEnd_ k a') = cstr_ ns a a'
        cstr_ ns (FixLabel _ a) a' = cstr_ ns a a'
        cstr_ ns a (FixLabel _ a') = cstr_ ns a a'
    --    cstr_ ns (PMLabel a _) a' = cstr_ ns a a'
    --    cstr_ ns a (PMLabel a' _) = cstr_ ns a a'
    --    cstr_ ns TType TType = Unit
        cstr_ ns (Con a n xs) (Con a' n' xs') | a == a' && n == n' = foldr t2 Unit $ zipWith (cstr__ ns) xs xs'
        cstr_ [] (TyConN "'FrameBuffer" [a, b]) (TyConN "'FrameBuffer" [a', b']) = t2 (cstrT TNat a a') (cstr__ [] b b')    -- todo: elim
        cstr_ ns (TyCon a xs) (TyCon a' xs') | a == a' = foldr t2 Unit $ zipWith (cstr__ ns) xs xs'
    --    cstr_ ns (TyCon a []) (TyCon a' []) | a == a' = Unit
        cstr_ ns (Var i) (Var i') | i == i', i < length ns = Unit
        cstr_ (_: ns) (down 0 -> Just a) (down 0 -> Just a') = cstr__ ns a a'
    --    cstr_ ((t, t'): ns) (UApp (down 0 -> Just a) (Var 0)) (UApp (down 0 -> Just a') (Var 0)) = traceInj2 (a, "V0") (a', "V0") $ cstr__ ns a a'
    --    cstr_ ((t, t'): ns) a (UApp (down 0 -> Just a') (Var 0)) = traceInj (a', "V0") a $ cstr__ ns (Lam Visible t a) a'
    --    cstr_ ((t, t'): ns) (UApp (down 0 -> Just a) (Var 0)) a' = traceInj (a, "V0") a' $ cstr__ ns a (Lam Visible t' a')
--        cstr_ ns (Lam b) (Lam b') = cstr__ ((a, a'): ns) b b'   -- todo
        cstr_ ns (Pi h a b) (Pi h' a' b') | h == h' = t2 (cstr__ ns a a') (cstr__ ((a, a'): ns) b b')
    --    cstr_ ns (Meta a b) (Meta a' b') = t2 (cstr__ ns a a') (cstr__ ((a, a'): ns) b b')
    --    cstr_ [] t (Meta a b) = Meta a $ cstr_ [] (up 1 t) b
    --    cstr_ [] (Meta a b) t = Meta a $ cstr_ [] b (up 1 t)
    --    cstr_ ns (unApp -> Just (a, b)) (unApp -> Just (a', b')) = traceInj2 (a, show b) (a', show b') $ t2 (cstr__ ns a a') (cstr__ ns b b')
    --    cstr_ ns (unApp -> Just (a, b)) (unApp -> Just (a', b')) = traceInj2 (a, show b) (a', show b') $ t2 (cstr__ ns a a') (cstr__ ns b b')
    --    cstr_ ns (Label f xs _) (Label f' xs' _) | f == f' = foldr1 T2 $ zipWith (cstr__ ns) xs xs'

        cstr_ [] (UL (FunN "'VecScalar" [a, b])) (TVec a' b') = t2 (cstrT TNat a a') (cstr__ [] b b')
        cstr_ [] (UL (FunN "'VecScalar" [a, b])) (UL (FunN "'VecScalar" [a', b'])) = t2 (cstrT TNat a a') (cstr__ [] b b')
        cstr_ [] (UL (FunN "'VecScalar" [a, b])) t@(TTyCon0 n) | isElemTy n = t2 (cstrT TNat a (ENat 1)) (cstr__ [] b t)
        cstr_ [] t@(TTyCon0 n) (UL (FunN "'VecScalar" [a, b])) | isElemTy n = t2 (cstrT TNat a (ENat 1)) (cstr__ [] b t)

        cstr_ ns@[] (UL (FunN "'FragOps'" [a])) (TyConN "'FragmentOperation" [x]) = cstr__ ns a x
        cstr_ ns@[] (UL (FunN "'FragOps'" [a])) (TyConN "'Tuple2" [TyConN "'FragmentOperation" [x], TyConN "'FragmentOperation" [y]]) = cstr__ ns a $ TTuple2 x y

        cstr_ ns@[] (TyConN "'Tuple2" [x, y]) (UL (FunN "'JoinTupleType" [x', y'])) = t2 (cstr__ ns x x') (cstr__ ns y y')
        cstr_ ns@[] (UL (FunN "'JoinTupleType" [x', y'])) (TyConN "'Tuple2" [x, y]) = t2 (cstr__ ns x' x) (cstr__ ns y' y)
        cstr_ ns@[] (UL (FunN "'JoinTupleType" [x', y'])) x@NoTup  = t2 (cstr__ ns x' x) (cstr__ ns y' $ TTyCon0 "'Tuple0")

        cstr_ ns@[] (x@NoTup) (UL (FunN "'InterpolatedType" [x'])) = cstr__ ns (TTyCon "'Interpolated" (TType :~> TType) [x]) x'

    --    cstr_ [] (TyConN "'FrameBuffer" [a, b]) (UL (FunN "'TFFrameBuffer" [TyConN "'Image" [a', b']])) = T2 (cstrT TNat a a') (cstr__ [] b b')

        cstr_ [] a@App{} a'@App{} = CstrT TType a a'
        cstr_ [] a@CFun a'@CFun = CstrT TType a a'
        cstr_ [] a@LCon a'@CFun = CstrT TType a a'
        cstr_ [] a@LCon a'@App{} = CstrT TType a a'
        cstr_ [] a@CFun a'@LCon = CstrT TType a a'
        cstr_ [] a@App{} a'@LCon = CstrT TType a a'
        cstr_ [] a@PMLabel{} a' = CstrT TType a a'
        cstr_ [] a a'@PMLabel{} = CstrT TType a a'
        cstr_ [] a a' | isVar a || isVar a' = CstrT TType a a'
        cstr_ ns a a' = Empty $ unlines [ "can not unify"
                                        , ppShow a
                                        , "with"
                                        , ppShow a'
                                        ]
{-
    --    unApp (UApp a b) | isInjective a = Just (a, b)         -- TODO: injectivity check
        unApp (Con a xs@(_:_)) = Just (Con a (init xs), last xs)
        unApp (TyCon a xs@(_:_)) = Just (TyCon a (init xs), last xs)
        unApp _ = Nothing
-}
        isInjective _ = True--False

        isVar Var{} = True
        isVar (App a b) = isVar a
        isVar _ = False

        traceInj2 (a, a') (b, b') c | debug && (susp a || susp b) = trace_ ("  inj'?  " ++ show a ++ " : " ++ a' ++ "   ----   " ++ show b ++ " : " ++ b') c
        traceInj2 _ _ c = c
        traceInj (x, y) z a | debug && susp x = trace_ ("  inj?  " ++ show x ++ " : " ++ y ++ "    ----    " ++ show z) a
        traceInj _ _ a = a

        susp Con{} = False
        susp TyCon{} = False
        susp _ = True

        isElemTy n = n `elem` ["'Bool", "'Float", "'Int"]

    reflCstr = \case
    {-
        Unit -> TT
        TType -> TT  -- ?
        Con n xs -> foldl (t2C te{-todo: more precise env-}) TT $ map (reflCstr te{-todo: more precise env-}) xs
        TyCon n xs -> foldl (t2C te{-todo: more precise env-}) TT $ map (reflCstr te{-todo: more precise env-}) xs
        x -> {-error $ "reflCstr: " ++ show x-} ReflCstr x
    -}
        x -> TT

    t2C TT TT = TT
    t2C a b = T2C a b

    t2 Unit a = a
    t2 a Unit = a
    t2 (Empty a) (Empty b) = Empty (a <> b)
    t2 (Empty s) _ = Empty s
    t2 _ (Empty s) = Empty s
    t2 a b = T2 a b

    oneOp :: (forall a . Num a => a -> a) -> Exp -> Maybe Exp
    oneOp f = oneOp_ f f

    oneOp_ f _ (EFloat x) = Just $ EFloat $ f x
    oneOp_ _ f (EInt x) = Just $ EInt $ f x
    oneOp_ _ _ _ = Nothing

    twoOp :: (forall a . Num a => a -> a -> a) -> Exp -> Exp -> Maybe Exp
    twoOp f = twoOp_ f f

    twoOp_ f _ (EFloat x) (EFloat y) = Just $ EFloat $ f x y
    twoOp_ _ f (EInt x) (EInt y) = Just $ EInt $ f x y
    twoOp_ _ _ _ _ = Nothing

    modF x y = x - fromIntegral (floor (x / y)) * y

    twoOpBool :: (forall a . Ord a => a -> a -> Bool) -> Exp -> Exp -> Maybe Exp
    twoOpBool f (EFloat x) (EFloat y) = Just $ EBool $ f x y
    twoOpBool f (EInt x) (EInt y) = Just $ EBool $ f x y
    twoOpBool _ _ _ = Nothing

cstr a b = eval $ CstrT TType a b

app_ :: Exp -> Exp -> Exp
app_ (Lam x) a = subst 0 a x
app_ (Con s n xs) a = if n < conParams s then Con s (n+1) xs else Con s n (xs ++ [a])
app_ (TyCon s xs) a = TyCon s (xs ++ [a])
app_ (Label lk x e) a = label lk (app_ x a) $ app_ e a
app_ (LabelEnd_ k x) a = LabelEnd_ k (app_ x a)   -- ???
app_ (Neut f) a = Neut $ App_ f a

-------------------------------------------------------------------------------- constraints env

data CEnv a
    = MEnd a
    | Meta Exp (CEnv a)
    | Assign !Int ExpType (CEnv a)       -- De Bruijn index decreasing assign reservedOp, only for metavariables (non-recursive)
  deriving (Show, Functor)

instance (Subst Exp a) => Up (CEnv a) where
    up1_ i = \case
        MEnd a -> MEnd $ up1_ i a
        Meta a b -> Meta (up1_ i a) (up1_ (i+1) b)
        Assign j a b -> handleLet i j $ \i' j' -> assign j' (up1_ i' a) (up1_ i' b)
          where
            handleLet i j f
                | i >  j = f (i-1) j
                | i <= j = f i (j+1)

    used i a = error "used @(CEnv _)"

    fold _ _ _ = error "fold @(CEnv _)"

    maxDB_ _ = error "maxDB_ @(CEnv _)"

instance (Subst Exp a) => Subst Exp (CEnv a) where
    subst i x = \case
        MEnd a -> MEnd $ subst i x a
        Meta a b  -> Meta (subst i x a) (subst (i+1) (up 1 x) b)
        Assign j a b
            | j > i, Just a' <- down i a       -> assign (j-1) a' (subst i (subst (j-1) (fst a') x) b)
            | j > i, Just x' <- down (j-1) x   -> assign (j-1) (subst i x' a) (subst i x' b)
            | j < i, Just a' <- down (i-1) a   -> assign j a' (subst (i-1) (subst j (fst a') x) b)
            | j < i, Just x' <- down j x       -> assign j (subst (i-1) x' a) (subst (i-1) x' b)
            | j == i    -> Meta (eval $ CstrT (snd a) x $ fst a) $ up1_ 0 b

--assign :: (Int -> Exp -> CEnv Exp -> a) -> (Int -> Exp -> CEnv Exp -> a) -> Int -> Exp -> CEnv Exp -> a
swapAssign _ clet i (Var j, t) b | i > j = clet j (Var (i-1), t) $ subst j (Var (i-1)) $ up1_ i b
swapAssign clet _ i a b = clet i a b

assign = swapAssign Assign Assign


-------------------------------------------------------------------------------- environments

-- SExp + Exp zipper
data Env
    = EBind1 SI Binder Env SExp2            -- zoom into first parameter of SBind
    | EBind2_ SI Binder Type Env             -- zoom into second parameter of SBind
    | EApp1 SI Visibility Env SExp2
    | EApp2 SI Visibility ExpType Env
    | ELet1 LI Env SExp2
    | ELet2 LI ExpType Env
    | EGlobal String{-full source of current module-} GlobalEnv [Stmt]
    | ELabelEnd Env

    | EAssign Int ExpType Env
    | CheckType_ SI Type Env
    | CheckIType SExp2 Env
--    | CheckSame Exp Env
    | CheckAppType SI Visibility Type Env SExp2   --pattern CheckAppType _ h t te b = EApp1 _ h (CheckType t te) b
  deriving Show

pattern EBind2 b e env <- EBind2_ _ b e env where EBind2 b e env = EBind2_ (debugSI "6") b e env
pattern CheckType e env <- CheckType_ _ e env where CheckType e env = CheckType_ (debugSI "7") e env

parent = \case
    EAssign _ _ x        -> Right x
    EBind2 _ _ x         -> Right x
    EBind1 _ _ x _       -> Right x
    EApp1 _ _ x _        -> Right x
    EApp2 _ _ _ x        -> Right x
    ELet1 _ x _          -> Right x
    ELet2 _ _ x          -> Right x
    CheckType _ x        -> Right x
    CheckIType _ x       -> Right x
--    CheckSame _ x        -> Right x
    CheckAppType _ _ _ x _ -> Right x
    ELabelEnd x          -> Right x
    EGlobal s x _        -> Left (s, x)

-------------------------------------------------------------------------------- simple typing

litType = \case
    LInt _    -> TInt
    LFloat _  -> TFloat
    LString _ -> TString
    LChar _   -> TChar

class NType a where nType :: a -> Type

instance NType FunName where nType (FunName _ _ t) = t
instance NType ConName where nType (ConName _ _ _ _ t) = t
instance NType TyConName where nType (TyConName _ _ _ t _ _) = t
instance NType CaseFunName where nType (CaseFunName _ t _) = t
instance NType TyCaseFunName where nType (TyCaseFunName _ t) = t

neutType te = \case
    App_ f x        -> appTy (neutType te f) x
    Var_ i          -> snd $ varType "C" i te
    Fun_ s ts       -> foldl appTy (nType s) ts
    CaseFun_ s ts   -> foldl appTy (nType s) ts
    TyCaseFun_ s ts -> foldl appTy (nType s) ts

appTy (Pi _ a b) x = subst 0 x b
appTy t x = error $ "appTy: " ++ show t

-------------------------------------------------------------------------------- inference

type TCM m = ExceptT String (WriterT Infos m)

--runTCM = either error id . runExcept

expAndType s (e, t, si) = (e, t)

-- todo: do only if NoTypeNamespace extension is not on
lookupName s@('\'':s') m = expAndType s <$> (Map.lookup s m `mplus` Map.lookup s' m)
lookupName s m           = expAndType s <$> Map.lookup s m
--elemIndex' s@('\'':s') m = elemIndex s m `mplus` elemIndex s' m
--elemIndex' s m = elemIndex s m

getDef te si s = maybe (throwError $ "can't find: " ++ s ++ " in " ++ showSI te si {- ++ "\nitems:\n" ++ intercalate ", " (take' "..." 10 $ Map.keys $ snd $ extractEnv te)-}) return (lookupName s $ snd $ extractEnv te)
{-
take' e n xs = case splitAt n xs of
    (as, []) -> as
    (as, _) -> as ++ [e]
-}
showSI :: Env -> SI -> String
showSI e = showSI_ (fst $ extractEnv e)

type ExpType' = CEnv ExpType

inferN :: forall m . Monad m => TraceLevel -> Env -> SExp2 -> TCM m ExpType'
inferN tracelevel = infer  where

    infer :: Env -> SExp2 -> TCM m ExpType'
    infer te exp = (if tracelevel >= 1 then trace_ ("infer: " ++ showEnvSExp te exp) else id) $ (if debug then fmap (fmap{-todo-} $ recheck' "infer" te) else id) $ case exp of
        SAnn x t        -> checkN (CheckIType x te) t TType
        SLabelEnd x     -> infer (ELabelEnd te) x
        SVar (si, _) i  -> focus_' te exp (Var i, snd $ varType "C2" i te)
        SLit si l       -> focus_' te exp (ELit l, litType l)
        STyped si et    -> focus_' te exp et
        SGlobal (si, s) -> focus_' te exp =<< getDef te si s
        SApp si h a b   -> infer (EApp1 (si `validate` [sourceInfo a, sourceInfo b]) h te b) a
        SLet le a b     -> infer (ELet1 le te b{-in-}) a{-let-} -- infer te SLamV b `SAppV` a)
        SBind si h _ a b -> infer ((if h /= BMeta then CheckType_ (sourceInfo exp) TType else id) $ EBind1 si h te $ (if isPi h then TyType else id) b) a

    checkN :: Env -> SExp2 -> Exp -> TCM m ExpType'
    checkN te x t = (if tracelevel >= 1 then trace_ $ "check: " ++ showEnvSExpType te x t else id) $ checkN_ te x t

    checkN_ te e t
            -- temporal hack
        | x@(SGlobal (si, MatchName n)) `SAppV` SLamV (Wildcard_ siw _) `SAppV` a `SAppV` SVar siv v `SAppV` b <- e
            = infer te $ x `SAppV` SLam Visible SType (STyped mempty (subst (v+1) (Var 0) $ up 1 t, TType)) `SAppV` a `SAppV` SVar siv v `SAppV` b
            -- temporal hack
        | x@(SGlobal (si, "'NatCase")) `SAppV` SLamV (Wildcard_ siw _) `SAppV` a `SAppV` b `SAppV` SVar siv v <- e
            = infer te $ x `SAppV` STyped mempty (Lam $ subst (v+1) (Var 0) $ up 1 t, TNat :~> TType) `SAppV` a `SAppV` b `SAppV` SVar siv v
{-
            -- temporal hack
        | x@(SGlobal "'VecSCase") `SAppV` SLamV (SLamV (Wildcard _)) `SAppV` a `SAppV` b `SAppV` c `SAppV` SVar v <- e
            = infer te $ x `SAppV` (SLamV (SLamV (STyped (subst (v+1) (Var 0) $ up 2 t, TType)))) `SAppV` a `SAppV` b `SAppV` c `SAppV` SVar v
-}
            -- temporal hack
        | SGlobal (si, "undefined") <- e = focus_' te e (Undef t, t)
        | SLabelEnd x <- e = checkN (ELabelEnd te) x t
        | SApp si h a b <- e = infer (CheckAppType si h t te b) a
        | SLam h a b <- e, Pi h' x y <- t, h == h'  = do
            tellType te e t
            let same = checkSame te a x
            if same then checkN (EBind2 (BLam h) x te) b y else error $ "checkSame:\n" ++ show a ++ "\nwith\n" ++ showEnvExp te (x, TType)
        | Pi Hidden a b <- t, notHiddenLam e = checkN (EBind2 (BLam Hidden) a te) (up1 e) b
        | otherwise = infer (CheckType_ (sourceInfo e) t te) e
      where
        -- todo
        notHiddenLam = \case
            SLam Visible _ _ -> True
            SGlobal (si,s) | (Lam _, Pi Hidden _ _) <- fromMaybe (error $ "infer: can't find: " ++ s) $ lookupName s $ snd $ extractEnv te -> False
                           | otherwise -> True
            _ -> False
{-
    -- todo
    checkSame te (Wildcard _) a = return (te, True)
    checkSame te x y = do
        (ex, _) <- checkN te x TType
        return $ ex == y
-}
    checkSame te (Wildcard _) a = True
    checkSame te (SGlobal (_,"'Type")) TType = True
    checkSame te SType TType = True
    checkSame te (SBind _ BMeta _ SType (STyped _ (Var 0, _))) a = True
    checkSame te a b = error $ "checkSame: " ++ show (a, b)

    hArgs (Pi Hidden _ b) = 1 + hArgs b
    hArgs _ = 0

    focus_' env si eet = tellType env si (snd eet) >> focus_ env eet

    focus_ :: Env -> ExpType -> TCM m ExpType'
    focus_ env eet@(e, et) = (if tracelevel >= 1 then trace_ $ "focus: " ++ showEnvExp env eet else id) $ (if debug then fmap (fmap{-todo-} $ recheck' "focus" env) else id) $ case env of
        ELabelEnd te -> focus_ te (LabelEnd e, et)
--        CheckSame x te -> focus_ (EBind2_ (debugSI "focus_ CheckSame") BMeta (cstr x e) te) $ up 1 eet
        CheckAppType si h t te b   -- App1 h (CheckType t te) b
            | Pi h' x (down 0 -> Just y) <- et, h == h' -> case t of
                Pi Hidden t1 t2 | h == Visible -> focus_ (EApp1 si h (CheckType_ (sourceInfo b) t te) b) eet  -- <<e>> b : {t1} -> {t2}
                _ -> focus_ (EBind2_ (sourceInfo b) BMeta (cstr t y) $ EApp1 si h te b) $ up 1 eet
            | otherwise -> focus_ (EApp1 si h (CheckType_ (sourceInfo b) t te) b) eet
        EApp1 si h te b
            | Pi h' x y <- et, h == h' -> checkN (EApp2 si h eet te) b x
            | Pi Hidden x y  <- et, h == Visible -> focus_ (EApp1 mempty Hidden env $ Wildcard $ Wildcard SType) eet  --  e b --> e _ b
--            | CheckType (Pi Hidden _ _) te' <- te -> error "ok"
--            | CheckAppType Hidden _ te' _ <- te -> error "ok"
            | otherwise -> infer (CheckType_ (sourceInfo b) (Var 2) $ cstr' h (up 2 et) (Pi Visible (Var 1) (Var 1)) (up 2 e) $ EBind2_ (sourceInfo b) BMeta TType $ EBind2_ (sourceInfo b) BMeta TType te) (up 3 b)
          where
            cstr' h x y e = EApp2 mempty h (eval $ Coe (up 1 x) (up 1 y) (Var 0) (up 1 e), up 1 y) . EBind2_ (sourceInfo b) BMeta (cstr x y)
        ELet2 le (x{-let-}, xt) te -> focus_ te $ subst 0 (mkELet le x xt){-let-} eet{-in-}
        CheckIType x te -> checkN te x e
        CheckType_ si t te
            | hArgs et > hArgs t
                            -> focus_ (EApp1 mempty Hidden (CheckType_ si t te) $ Wildcard $ Wildcard SType) eet
            | hArgs et < hArgs t, Pi Hidden t1 t2 <- t
                            -> focus_ (CheckType_ si t2 $ EBind2 (BLam Hidden) t1 te) eet
            | otherwise    -> focus_ (EBind2_ si BMeta (cstr t et) te) $ up 1 eet
        EApp2 si h (a, at) te    -> focus_' te si (app_ a e, appTy at e)        --  h??
        EBind1 si h te b   -> infer (EBind2_ (sourceInfo b) h e te) b
        EBind2_ si (BLam h) a te -> focus_ te $ lamPi h a eet
        EBind2_ si (BPi h) a te -> focus_' te si (Pi h a e, TType)
        _ -> focus2 env $ MEnd eet

    focus2 :: Env -> CEnv ExpType -> TCM m ExpType'
    focus2 env eet = case env of
        ELet1 le te b{-in-} -> infer (ELet2 le (replaceMetas' eet{-let-}) te) b{-in-}
        EBind2_ si BMeta tt te
            | Unit <- tt    -> refocus te $ subst 0 TT eet
            | Empty msg <- tt   -> throwError $ "type error: " ++ msg ++ "\nin " ++ showSI te si ++ "\n"-- todo: better error msg
            | T2 x y <- tt, let te' = EBind2_ si BMeta (up 1 y) $ EBind2_ si BMeta x te
                            -> refocus te' $ subst 2 (eval $ T2C (Var 1) (Var 0)) $ up 2 eet
            | CstrT t a b <- tt, a == b  -> refocus te $ subst 0 TT eet
            | CstrT t a b <- tt, Just r <- cst (a, t) b -> r
            | CstrT t a b <- tt, Just r <- cst (b, t) a -> r
            | isCstr tt, EBind2 h x te' <- te{-, h /= BMeta todo: remove-}, Just x' <- down 0 tt, x == x'
                            -> refocus te $ subst 1 (Var 0) eet
            | EBind2 h x te' <- te, h /= BMeta, Just b' <- down 0 tt
                            -> refocus (EBind2_ si h (up 1 x) $ EBind2_ si BMeta b' te') $ subst 2 (Var 0) $ up 1 eet
            | ELet2 le (x, xt) te' <- te, Just b' <- down 0 tt
                            -> refocus (ELet2 le (up 1 x, up 1 xt) $ EBind2_ si BMeta b' te') $ subst 2 (Var 0) $ up 1 eet
            | EBind1 si h te' x <- te -> refocus (EBind1 si h (EBind2_ si BMeta tt te') $ up1_ 1 x) eet
            | ELet1 le te' x     <- te, floatLetMeta $ snd $ replaceMetas' $ Meta tt $ eet
                                    -> refocus (ELet1 le (EBind2_ si BMeta tt te') $ up1_ 1 x) eet
            | CheckAppType si h t te' x <- te -> refocus (CheckAppType si h (up 1 t) (EBind2_ si BMeta tt te') $ up1 x) eet
            | EApp1 si h te' x <- te -> refocus (EApp1 si h (EBind2_ si BMeta tt te') $ up1 x) eet
            | EApp2 si h x te' <- te -> refocus (EApp2 si h (up 1 x) $ EBind2_ si BMeta tt te') eet
            | CheckType_ si t te' <- te -> refocus (CheckType_ si (up 1 t) $ EBind2_ si BMeta tt te') eet
--            | CheckIType x te' <- te -> refocus (CheckType_ si (up 1 t) $ EBind2_ si BMeta tt te') eet
            | ELabelEnd te'   <- te -> refocus (ELabelEnd $ EBind2_ si BMeta tt te') eet
            | otherwise             -> focus2 te $ Meta tt eet
          where
            refocus = refocus_ focus2
            cst :: ExpType -> Exp -> Maybe (TCM m ExpType')
            cst x = \case
                Var i | fst (varType "X" i te) == BMeta
                      , Just y <- down i x
                      -> Just $ join swapAssign (\i x -> refocus $ EAssign i x te) i y $ subst 0 {-ReflCstr y-}TT $ subst (i+1) (fst $ up 1 y) eet
                _ -> Nothing

        EAssign i b te -> case te of
            EBind2_ si h x te' | i > 0, Just b' <- down 0 b
                              -> refocus' (EBind2_ si h (subst (i-1) (fst b') x) (EAssign (i-1) b' te')) eet
            ELet2 le (x, xt) te' | i > 0, Just b' <- down 0 b
                              -> refocus' (ELet2 le (subst (i-1) (fst b') x, subst (i-1) (fst b') xt) (EAssign (i-1) b' te')) eet
            ELet1 le te' x    -> refocus' (ELet1 le (EAssign i b te') $ substS (i+1) (up 1 b) x) eet
            EBind1 si h te' x -> refocus' (EBind1 si h (EAssign i b te') $ substS (i+1) (up 1 b) x) eet
            CheckAppType si h t te' x -> refocus' (CheckAppType si h (subst i (fst b) t) (EAssign i b te') $ substS i b x) eet
            EApp1 si h te' x  -> refocus' (EApp1 si h (EAssign i b te') $ substS i b x) eet
            EApp2 si h x te'  -> refocus' (EApp2 si h (subst i (fst b) x) $ EAssign i b te') eet
            CheckType_ si t te'   -> refocus' (CheckType_ si (subst i (fst b) t) $ EAssign i b te') eet
            ELabelEnd te'     -> refocus' (ELabelEnd $ EAssign i b te') eet
            EAssign j a te' | i < j
                              -> refocus' (EAssign (j-1) (subst i (fst b) a) $ EAssign i (up1_ (j-1) b) te') eet
            t  | Just te' <- pull i te -> refocus' te' eet
               | otherwise      -> swapAssign (\i x -> focus2 te . Assign i x) (\i x -> refocus' $ EAssign i x te) i b eet
            -- todo: CheckSame Exp Env
          where
            refocus' = fix refocus_
            pull i = \case
                EBind2 BMeta _ te | i == 0 -> Just te
                EBind2_ si h x te   -> EBind2_ si h <$> down (i-1) x <*> pull (i-1) te
                EAssign j b te  -> EAssign (if j <= i then j else j-1) <$> down i b <*> pull (if j <= i then i+1 else i) te
                _               -> Nothing

        EGlobal{} -> return eet
        _ -> case eet of
            MEnd x -> throwError_ $ "focus todo: " ++ ppShow x
            _ -> throwError_ $ "focus checkMetas: " ++ ppShow env ++ "\n" ++ ppShow (fst <$> eet)
      where
        refocus_ :: (Env -> CEnv ExpType -> TCM m ExpType') -> Env -> CEnv ExpType -> TCM m ExpType'
        refocus_ _ e (MEnd at) = focus_ e at
        refocus_ f e (Meta x at) = f (EBind2 BMeta x e) at
        refocus_ _ e (Assign i x at) = focus2 (EAssign i x e) at

        replaceMetas' = replaceMetas $ lamPi Hidden

lamPi h = (***) <$> (\a b -> Lam b) <*> Pi h

replaceMetas bind = \case
    Meta a t -> bind a $ replaceMetas bind t
    Assign i x t | x' <- up1_ i x -> bind (eval $ CstrT (snd x') (Var i) $ fst x') . up 1 . up1_ i $ replaceMetas bind t
    MEnd t ->  t


isCstr CstrT{} = True
isCstr (UL (FunN s _)) = s `elem` ["'Eq", "'Ord", "'Num", "'CNum", "'Signed", "'Component", "'Integral", "'NumComponent", "'Floating"]       -- todo: use Constraint type to decide this
isCstr (UL c) = {- trace_ (ppShow c ++ show c) $ -} False

-------------------------------------------------------------------------------- re-checking

type Message = String

recheck :: Message -> Env -> ExpType -> ExpType
recheck msg e = recheck' msg e

-- todo: check type also
recheck' :: Message -> Env -> ExpType -> ExpType
recheck' msg' e (x, xt) = (recheck_ "main" (checkEnv e) (x, xt), xt)
  where
    checkEnv = \case
        e@EGlobal{} -> e
        EBind1 si h e b -> EBind1 si h (checkEnv e) b
        EBind2_ si h t e -> EBind2_ si h (checkType e t) $ checkEnv e            --  E [\(x :: t) -> e]    -> check  E [t]
        ELet1 le e b -> ELet1 le (checkEnv e) b
        ELet2 le x e -> ELet2 le (recheck'' "env" e x) $ checkEnv e
        EApp1 si h e b -> EApp1 si h (checkEnv e) b
        EApp2 si h a e -> EApp2 si h (recheck'' "env" e a) $ checkEnv e    --  E [a x]  ->  check
        EAssign i x e -> EAssign i (recheck'' "env" e $ up1_ i x) $ checkEnv e                -- __ <i := x>
        CheckType_ si x e -> CheckType_ si (checkType e x) $ checkEnv e
--        CheckSame x e -> CheckSame (recheck'' "env" e x) $ checkEnv e
        CheckAppType si h x e y -> CheckAppType si h (checkType e x) (checkEnv e) y

    recheck'' msg te a@(x, xt) = (recheck_ msg te a, xt)
    checkType te e = recheck_ "check" te (e, TType)

    recheck_ msg te = \case
        (Var k, zt) -> Var k    -- todo: check var type
        (Lam b, Pi h a bt) -> Lam $ recheck_ "9" (EBind2 (BLam h) a te) (b, bt)
        (Pi h a b, TType) -> Pi h (checkType te a) $ checkType (EBind2 (BPi h) a te) b
        (ELit l, zt) -> ELit l  -- todo: check literal type
        (TType, TType) -> TType
        (Neut (App_ a b), zt)
            | (Neut a', at) <- recheck'' "app1" te (Neut a, neutType te a)
            -> checkApps [] zt (Neut . App_ a' . head) te at [b]
        (Con s n as, zt)     -> checkApps [] zt (Con s n . drop (conParams s)) te (nType s) $ mkConPars n zt ++ as
        (TyCon s as, zt)      -> checkApps [] zt (TyCon s) te (nType s) as
        (Fun s as, zt)        -> checkApps [] zt (Fun s) te (nType s) as
        (CaseFun s as, zt)    -> checkApps [] zt (CaseFun s) te (nType s) as
        (TyCaseFun s as, zt)  -> checkApps [] zt (TyCaseFun s) te (nType s) as
        (Label lk a x, zt)  -> Label lk (recheck_ msg te (a, zt)) x
        (LabelEnd_ k x, zt) -> LabelEnd_ k $ recheck_ msg te (x, zt)
      where
        checkApps acc zt f _ t [] | t == zt = f $ reverse acc
        checkApps acc zt f te t@(Pi h x y) (b_: xs) = checkApps (b: acc) zt f te (appTy t b) xs where b = recheck_ "checkApps" te (b_, x)
        checkApps acc zt f te t _ = error_ $ "checkApps " ++ msg ++ "\n" ++ showEnvExp te{-todo-} (t, TType) ++ "\n\n" ++ showEnvExp e (x, xt)

-- Ambiguous: (Int ~ F a) => Int
-- Not ambiguous: (Show a, a ~ F b) => b
ambiguityCheck :: String -> Exp -> Maybe String
ambiguityCheck s ty = case ambigVars ty of
    [] -> Nothing
    err -> Just $ s ++ " has ambiguous type:\n" ++ ppShow ty ++ "\nproblematic vars:\n" ++ show err

ambigVars :: Exp -> [(Int, Exp)]
ambigVars ty = [(n, c) | (n, c) <- hid, not $ any (`Set.member` defined) $ Set.insert n $ free c]
  where
    (defined, hid, i) = compDefined False ty

floatLetMeta :: Exp -> Bool
floatLetMeta ty = (i-1) `Set.member` defined
  where
    (defined, hid, i) = compDefined True ty

compDefined b ty = (defined, hid, i)
  where
    defined = dependentVars hid $ Set.map (if b then (+i) else id) $ free ty

    i = length hid_
    hid = zipWith (\k t -> (k, up (k+1) t)) (reverse [0..i-1]) hid_
    (hid_, ty') = hiddenVars ty

hiddenVars (Pi Hidden a b) = first (a:) $ hiddenVars b
hiddenVars t = ([], t)

-- compute dependent type vars in constraints
-- Example:  dependentVars [(a, b) ~ F b c, d ~ F e] [c] == [a,b,c]
dependentVars :: [(Int, Exp)] -> Set.Set Int -> Set.Set Int
dependentVars ie = cycle mempty
  where
    freeVars = free

    cycle acc s
        | Set.null s = acc
        | otherwise = cycle (acc <> s) (grow s Set.\\ acc)

    grow = flip foldMap ie $ \case
      (n, t) -> (Set.singleton n <-> freeVars t) <> case t of
        CstrT _{-todo-} ty f -> freeVars ty <-> freeVars f
        CSplit a b c -> freeVars a <-> (freeVars b <> freeVars c)
        _ -> mempty
      where
        a --> b = \s -> if Set.null $ a `Set.intersection` s then mempty else b
        a <-> b = (a --> b) <> (b --> a)


-------------------------------------------------------------------------------- global env

type GlobalEnv = Map.Map SName (Exp, Type, SI)

-- monad used during elaborating statments -- TODO: use zippers instead
type ElabStmtM m = ReaderT (Extensions, String{-full source-}) (StateT GlobalEnv (ExceptT String (WriterT Infos m)))

extractEnv :: Env -> (String, GlobalEnv)
extractEnv = either id extractEnv . parent

initEnv :: GlobalEnv
initEnv = Map.fromList
    [ (,) "'Type" (TType, TType, debugSI "source-of-Type")
    ]

extractDesugarInfo :: GlobalEnv -> DesugarInfo
extractDesugarInfo ge =
    ( Map.fromList
        [ (n, f) | (n, (d, _, si)) <- Map.toList ge, f <- maybeToList $ case UL' d of
            Con (ConName _ f _ _ _) 0 [] -> f
            TyCon (TyConName _ f _ _ _ _) [] -> f
            (getLams -> UL (getLams -> Fun (FunName _ f _) _)) -> f
            Fun (FunName _ f _) [] -> f
            _ -> Nothing
        ]
    , Map.fromList $
        [ (n, Left ((t, inum), map f cons))
        | (n, (UL' (Con cn 0 []), _, si)) <- Map.toList ge, let TyConName t _ inum _ cons _ = conTypeName cn
        ] ++
        [ (n, Right $ pars t)
        | (n, (UL' (TyCon (TyConName _ f _ t _ _) []), _, _)) <- Map.toList ge
        ]
    )
  where
    f (ConName n _ _ _ ct) = (n, pars ct)
    pars = length . filter ((==Visible) . fst) . fst . getParams

-------------------------------------------------------------------------------- infos

newtype Infos = Infos (Map.Map Range (Set.Set String))
    deriving (NFData)

instance Monoid Infos where
    mempty = Infos mempty
    Infos x `mappend` Infos y = Infos $ Map.unionWith mappend x y

mkInfoItem (RangeSI r) i = Infos $ Map.singleton r $ Set.singleton i
mkInfoItem _ _ = mempty

listInfos (Infos m) = [(r, Set.toList i) | (r, i) <- Map.toList m]

-------------------------------------------------------------------------------- inference for statements

handleStmt :: MonadFix m => [Stmt] -> Stmt -> ElabStmtM m ()
handleStmt defs = \case
  Primitive n mf (trSExp' -> t_) -> do
        t <- inferType tr =<< ($ t_) <$> addF
        tellStmtType (fst n) t
        addToEnv n $ flip (,) t $ lamify t $ Fun (FunName (snd n) mf t)
  Let n mf mt ar t_ -> do
        af <- addF
        let t__ = maybe id (flip SAnn . af) mt t_
        (x, t) <- inferTerm (snd n) tr id $ trSExp' $ fromMaybe (SBuiltin "primFix" `SAppV` SLamV t__) $ downS 0 t__
        tellStmtType (fst n) t
        addToEnv n (mkELet (True, n, SData mf, ar) x t, t)
  PrecDef{} -> return ()
  TypeFamily s ps t -> handleStmt defs $ Primitive s Nothing $ addParamsS ps t
  Data s (map (second trSExp') -> ps) (trSExp' -> t_) addfa (map (second trSExp') -> cs) -> do
    exs <- asks fst
    af <- if addfa then gets $ addForalls exs . (snd s:) . defined' else return id
    vty <- inferType tr $ addParamsS ps t_
    tellStmtType (fst s) vty
    let
        pnum' = length $ filter ((== Visible) . fst) ps
        inum = arity vty - length ps

        mkConstr j (cn, af -> ct)
            | c == SGlobal s && take pnum' xs == downToS (length . fst . getParamsS $ ct) pnum'
            = do
                cty <- removeHiddenUnit <$> inferType tr (addParamsS [(Hidden, x) | (Visible, x) <- ps] ct)
                tellStmtType (fst cn) cty
                let     pars = zipWith (\x -> second $ STyped (debugSI "mkConstr1") . flip (,) TType . up_ (1+j) x) [0..] $ drop (length ps) $ fst $ getParams cty
                        act = length . fst . getParams $ cty
                        acts = map fst . fst . getParams $ cty
                        conn = conName (snd cn) (listToMaybe [f | PrecDef n f <- defs, n == cn]) j cty
                addToEnv cn (Con conn 0 [], cty)
                return ( conn
                       , addParamsS pars
                       $ foldl SAppV (SVar (debugSI "22", ".cs") $ j + length pars) $ drop pnum' xs ++ [apps' (SGlobal cn) (zip acts $ downToS (j+1+length pars) (length ps) ++ downToS 0 (act- length ps))]
                       )
            | otherwise = throwError "illegal data definition (parameters are not uniform)" -- ++ show (c, cn, take pnum' xs, act)
            where
                (c, map snd -> xs) = getApps $ snd $ getParamsS ct

        motive = addParamsS (replicate inum (Visible, Wildcard SType)) $
           SPi Visible (apps' (SGlobal s) $ zip (map fst ps) (downToS inum $ length ps) ++ zip (map fst $ fst $ getParamsS t_) (downToS 0 inum)) SType

    mdo
        let tcn = TyConName (snd s) Nothing inum vty (map fst cons) cfn
        let cfn = CaseFunName (snd s) ct $ length ps
        addToEnv s (TyCon tcn [], vty)
        cons <- zipWithM mkConstr [0..] cs
        ct <- inferType tr
            ( (\x -> traceD ("type of case-elim before elaboration: " ++ ppShow x) x) $ addParamsS
                ( [(Hidden, x) | (_, x) <- ps]
                ++ (Visible, motive)
                : map ((,) Visible . snd) cons
                ++ replicate inum (Hidden, Wildcard SType)
                ++ [(Visible, apps' (SGlobal s) $ zip (map fst ps) (downToS (inum + length cs + 1) $ length ps) ++ zip (map fst $ fst $ getParamsS t_) (downToS 0 inum))]
                )
            $ foldl SAppV (SVar (debugSI "23", ".ct") $ length cs + inum + 1) $ downToS 1 inum ++ [SVar (debugSI "24", ".24") 0]
            )
        addToEnv (fst s, caseName (snd s)) (lamify ct $ CaseFun cfn, ct)
        let ps' = fst $ getParams vty
            t =   (TType :~> TType)
              :~> addParams ps' (Var (length ps') `app_` TyCon tcn (downTo 0 $ length ps'))
              :~>  TType
              :~> Var 2 `app_` Var 0
              :~> Var 3 `app_` Var 1
        addToEnv (fst s, MatchName (snd s)) (lamify t $ TyCaseFun (TyCaseFunName (snd s) t), t)

  stmt -> error $ "handleStmt: " ++ show stmt

mkELet (False, n, mf, ar) x xt = x
mkELet (True, n, SData mf, ar) x t{-type of x-} = term
  where
    term = label LabelPM (addLams' ar t 0) $ par ar t x 0

    addLams' [] _ i = Fun (FunName (snd n) mf t) $ downTo 0 i
    addLams' (h: ar) (Pi h' d t) i | h == h' = Lam $ addLams' ar t (i+1)
    addLams' ar@(Visible: _) (Pi h@Hidden d t) i = Lam $ addLams' ar t (i+1)

    par ar tt (FunN "primFix" [_, f]) i = f `app_` label LabelFix (addLams' ar tt i) (foldl app_ term $ downTo 0 i)
    par ar (Pi Hidden k tt) (Lam z) i = Lam $ par (dropHidden ar) tt z (i+1)
      where
        dropHidden (Hidden: ar) = ar
        dropHidden ar = ar
    par ar t x _ = x

removeHiddenUnit (Pi Hidden Unit (down 0 -> Just t)) = removeHiddenUnit t
removeHiddenUnit (Pi h a b) = Pi h a $ removeHiddenUnit b
removeHiddenUnit t = t

addParams ps t = foldr (uncurry Pi) t ps

addLams ps t = foldr (uncurry $ \h a b -> Lam b) t ps

lamify t x = addLams (fst $ getParams t) $ x $ downTo 0 $ arity t

{-
getApps' = second reverse . run where
  run (App a b) = second (b:) $ run a
  run x = (x, [])
-}
arity :: Exp -> Int
arity = length . fst . getParams

getParams :: Exp -> ([(Visibility, Exp)], Exp)
getParams (UL' (Pi h a b)) = first ((h, a):) $ getParams b
getParams x = ([], x)

getLams (Lam b) = getLams b
getLams x = x

getGEnv f = do
    (exs, src) <- ask
    gets (\ge -> EGlobal src ge mempty) >>= f
inferTerm msg tr f t = asks fst >>= \exs -> getGEnv $ \env -> let env' = f env in smartTrace exs $ \tr -> 
    fmap (recheck msg env' . replaceMetas (lamPi Hidden)) $ lift (lift $ inferN (if tr then traceLevel exs else 0) env' t)
inferType tr t = asks fst >>= \exs -> getGEnv $ \env -> fmap (fst . recheck "inferType" env . flip (,) TType . replaceMetas (Pi Hidden) . fmap fst) $ lift (lift $ inferN (if tr then traceLevel exs else 0) (CheckType_ (debugSI "inferType CheckType_") TType env) t)

addToEnv :: Monad m => SIName -> (Exp, Exp) -> ElabStmtM m ()
addToEnv (si, s) (x, t) = do
--    maybe (pure ()) throwError_ $ ambiguityCheck s t      -- TODO
    exs <- asks fst
    when (trLight exs) $ mtrace (s ++ "  ::  " ++ ppShow t)
    v <- gets $ Map.lookup s
    case v of
      Nothing -> modify $ Map.insert s (closedExp x, closedExp t, si)
      Just (_, _, si') -> getGEnv $ \ge -> throwError $ "already defined " ++ s ++ " at " ++ showSI ge si ++ "\n and at " ++ showSI ge si'

downTo n m = map Var [n+m-1, n+m-2..n]

defined' = Map.keys

addF = asks fst >>= \exs -> gets $ addForalls exs . defined'

tellType te si t = tell $ mkInfoItem (sourceInfo si) $ removeEscs $ showDoc $ mkDoc True (t, TType)
tellStmtType si t = getGEnv $ \te -> tellType te si t


-------------------------------------------------------------------------------- inference output

data PolyEnv = PolyEnv
    { getPolyEnv :: GlobalEnv
    , infos      :: Infos
    }

filterPolyEnv p pe = pe { getPolyEnv = Map.filterWithKey (\k _ -> p k) $ getPolyEnv pe }

joinPolyEnvs :: MonadError ErrorMsg m => Bool -> [PolyEnv] -> m PolyEnv
joinPolyEnvs _ = return . foldr mappend' mempty'           -- todo
  where
    mempty' = PolyEnv mempty mempty
    PolyEnv a b `mappend'` PolyEnv a' b' = PolyEnv (a `mappend` a') (b `mappend` b')

-------------------------------------------------------------------------------- pretty print
-- todo: do this via conversion to SExp

instance PShow Exp where
    pShowPrec _ = showDoc_ . mkDoc False

instance PShow (CEnv Exp) where
    pShowPrec _ = showDoc_ . mkDoc False

instance PShow Env where
    pShowPrec _ e = showDoc_ $ envDoc e $ pure $ shAtom $ underlined "<<HERE>>"

showEnvExp :: Env -> ExpType -> String
showEnvExp e c = showDoc $ envDoc e $ epar <$> mkDoc False c

showEnvSExp :: Up a => Env -> SExp' a -> String
showEnvSExp e c = showDoc $ envDoc e $ epar <$> sExpDoc c

showEnvSExpType :: Up a => Env -> SExp' a -> Exp -> String
showEnvSExpType e c t = showDoc $ envDoc e $ epar <$> (shAnn "::" False <$> sExpDoc c <**> mkDoc False (t, TType))
  where
    infixl 4 <**>
    (<**>) :: NameDB (a -> b) -> NameDB a -> NameDB b
    a <**> b = get >>= \s -> lift $ evalStateT a s <*> evalStateT b s

{-
expToSExp :: Exp -> SExp
expToSExp = \case
    PMLabel x _     -> expToSExp x
    FixLabel _ x    -> expToSExp x
--    Var k           -> shAtom <$> shVar k
    App a b         -> SApp Visible{-todo-} (expToSExp a) (expToSExp b)
{-
    Lam h a b       -> join $ shLam (used 0 b) (BLam h) <$> f a <*> pure (f b)
    Bind h a b      -> join $ shLam (used 0 b) h <$> f a <*> pure (f b)
    Cstr a b        -> shCstr <$> f a <*> f b
    FunN s xs       -> foldl (shApp Visible) (shAtom s) <$> mapM f xs
    CaseFun s xs    -> foldl (shApp Visible) (shAtom $ show s) <$> mapM f xs
    TyCaseFun s xs  -> foldl (shApp Visible) (shAtom $ show s) <$> mapM f xs
    ConN s xs       -> foldl (shApp Visible) (shAtom s) <$> mapM f xs
    TyConN s xs     -> foldl (shApp Visible) (shAtom s) <$> mapM f xs
--    TType           -> pure $ shAtom "Type"
    ELit l          -> pure $ shAtom $ show l
    Assign i x e    -> shLet i (f x) (f e)
    LabelEnd x      -> shApp Visible (shAtom "labend") <$> f x
-}
nameSExp :: SExp -> NameDB SExp
nameSExp = \case
    SGlobal s       -> pure $ SGlobal s
    SApp h a b      -> SApp h <$> nameSExp a <*> nameSExp b
    SBind h a b     -> newName >>= \n -> SBind h <$> nameSExp a <*> local (n:) (nameSExp b)
    SLet a b        -> newName >>= \n -> SLet <$> nameSExp a <*> local (n:) (nameSExp b)
    STyped_ x (e, _) -> nameSExp $ expToSExp e  -- todo: mark boundary
    SVar i          -> SGlobal <$> shVar i
-}
envDoc :: Env -> Doc -> Doc
envDoc x m = case x of
    EGlobal{}           -> m
    EBind1 _ h ts b     -> envDoc ts $ join $ shLam (used 0 b) h <$> m <*> pure (sExpDoc b)
    EBind2 h a ts       -> envDoc ts $ join $ shLam True h <$> mkDoc ts' (a, TType) <*> pure m
    EApp1 _ h ts b      -> envDoc ts $ shApp h <$> m <*> sExpDoc b
    EApp2 _ h (Lam (Var 0), Pi Visible TType _) ts -> envDoc ts $ shApp h (shAtom "tyType") <$> m
    EApp2 _ h a ts      -> envDoc ts $ shApp h <$> mkDoc ts' a <*> m
    ELet1 _ ts b        -> envDoc ts $ shLet_ m (sExpDoc b)
    ELet2 _ x ts        -> envDoc ts $ shLet_ (mkDoc ts' x) m
    EAssign i x ts      -> envDoc ts $ shLet i (mkDoc ts' x) m
    CheckType t ts      -> envDoc ts $ shAnn ":" False <$> m <*> mkDoc ts' (t, TType)
--    CheckSame t ts      -> envDoc ts $ shCstr <$> m <*> mkDoc ts' t
    CheckAppType si h t te b -> envDoc (EApp1 si h (CheckType_ (sourceInfo b) t te) b) m
    ELabelEnd ts        -> envDoc ts $ shApp Visible (shAtom "labEnd") <$> m
  where
    ts' = False

class MkDoc a where
    mkDoc :: Bool -> a -> Doc

instance MkDoc ExpType where
    mkDoc ts e = mkDoc ts $ fst e

instance MkDoc Exp where
    mkDoc ts e = fmap inGreen <$> f e
      where
        f = \case
            PMLabel x _     -> f x
            FixLabel _ x    -> f x
            Neut x          -> mkDoc ts x
--            Lam h a b       -> join $ shLam (used 0 b) (BLam h) <$> f a <*> pure (f b)
            Lam b          -> join $ shLam True (BLam Visible) <$> f TType{-todo-} <*> pure (f b)
            Pi h a b        -> join $ shLam (used 0 b) (BPi h) <$> f a <*> pure (f b)
            ENat n          -> pure $ shAtom $ show n
            ConN s xs       -> foldl (shApp Visible) (shAtom_ s) <$> mapM f xs
            TyConN s xs     -> foldl (shApp Visible) (shAtom_ s) <$> mapM f xs
            TType           -> pure $ shAtom "Type"
            ELit l          -> pure $ shAtom $ show l
            LabelEnd_ k x   -> shApp Visible (shAtom $ "labend" ++ show k) <$> f x

        shAtom_ = shAtom . if ts then switchTick else id

instance MkDoc Neutral where
    mkDoc ts e = fmap inGreen <$> f e
      where
        g = mkDoc ts
        f = \case
            Var_ k           -> shAtom <$> shVar k
            App_ a b         -> shApp Visible <$> g a <*> g b
            CstrT' TType a b -> shCstr <$> g a <*> g b
            Fun_ s xs        -> foldl (shApp Visible) (shAtom_ $ show s) <$> mapM g xs
            CaseFun_ s xs    -> foldl (shApp Visible) (shAtom_ $ show s) <$> mapM g xs
            TyCaseFun_ s xs  -> foldl (shApp Visible) (shAtom_ $ show s) <$> mapM g xs

        shAtom_ = shAtom . if ts then switchTick else id

instance MkDoc (CEnv Exp) where
    mkDoc ts e = fmap inGreen <$> f e
      where
        f :: CEnv Exp -> Doc
        f = \case
            MEnd a          -> mkDoc ts a
            Meta a b        -> join $ shLam True BMeta <$> mkDoc ts a <*> pure (f b)
            Assign i (x, _) e -> shLet i (mkDoc ts x) (f e)

-------------------------------------------------------------------------------- main

smartTrace :: MonadError String m => Extensions -> (Bool -> m a) -> m a
smartTrace exs f | traceLevel exs >= 2 = f True
smartTrace exs f | traceLevel exs == 0 = f False
smartTrace exs f = catchError (f False) $ \err ->
    trace_ (unlines
        [ "---------------------------------"
        , err
        , "try again with trace"
        , "---------------------------------"
        ]) $ f True

type TraceLevel = Int
traceLevel exs = if TraceTypeCheck `elem` exs then 1 else 0 :: TraceLevel  -- 0: no trace
tr = False --traceLevel >= 2
trLight exs = traceLevel exs >= 1

inference_ :: PolyEnv -> Module -> ErrorT (WriterT Infos Identity) PolyEnv
inference_ (PolyEnv pe is) m = ff $ runWriter $ runExceptT $ mdo
    let (x, dns) = definitions m $ mkDesugarInfo defs `joinDesugarInfo` extractDesugarInfo pe
    defs <- either (throwError . ErrorMsg) return x
    mapM_ (maybe (return ()) (throwErrorTCM . text)) dns
    mapExceptT (fmap $ ErrorMsg +++ snd) . flip runStateT (initEnv <> pe) . flip runReaderT (extensions m, sourceCode m) . mapM_ (handleStmt defs) $ defs
  where
    ff (Left e, is) = throwError e
    ff (Right ge, is) = do
        tell is
        return $ PolyEnv ge is


