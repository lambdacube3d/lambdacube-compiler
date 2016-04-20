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
    ( SName, Lit(..), Visibility(..)
    , Exp (..), Neutral (..), ExpType, GlobalEnv
    , pattern Var, pattern CaseFun, pattern TyCaseFun, pattern App_, app_
    , pattern Con, pattern TyCon, pattern Pi, pattern Lam, pattern Fun, pattern ELit, pattern Func, pattern LabelEnd, pattern FL, pattern UFL, unFunc_
    , outputType, boolType, trueExp
    , down, Subst (..), free, subst, upDB
    , initEnv, Env(..)
    , SI(..), Range(..) -- todo: remove
    , Info(..), Infos, listAllInfos, listTypeInfos, listTraceInfos
    , inference, IM
    , nType, conType, neutType, neutType', appTy, mkConPars, makeCaseFunPars, makeCaseFunPars'
    , MaxDB, unfixlabel
    , ErrorMsg, errorRange
    , FName (..)
    , MkDoc (..)
    ) where

import Data.Monoid
import Data.Maybe
import Data.List
import qualified Data.Set as Set
import qualified Data.Map as Map

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Arrow hiding ((<+>))
import Control.DeepSeq

import LambdaCube.Compiler.Pretty hiding (Doc, braces, parens)
import LambdaCube.Compiler.Lexer
import LambdaCube.Compiler.Parser

-------------------------------------------------------------------------------- core expression representation

data Exp
    = TType
    | ELit_ Lit
    | Con_   !MaxDB ConName !Int{-number of ereased arguments applied-} [Exp]
    | TyCon_ !MaxDB TyConName [Exp]
    | Pi_  !MaxDB Visibility Exp Exp
    | Lam_ !MaxDB Exp
    | Neut Neutral
  deriving (Show)

pattern ELit a <- (unfixlabel -> ELit_ a) where ELit = ELit_

data Neutral
    = Fun_ !MaxDB FunName [Exp]{-local vars-} !Int{-number of missing parameters-} [Exp]{-given parameters, reversed-} Neutral{-unfolded expression-}{-not neut?-}
    | CaseFun__   !MaxDB CaseFunName   [Exp] Neutral
    | TyCaseFun__ !MaxDB TyCaseFunName [Exp] Neutral
    | App__ !MaxDB Neutral Exp
    | Var_ !Int                 -- De Bruijn variable
    | LabelEnd_ Exp                 -- not neut?
    | Delta (SData ([Exp] -> Exp))  -- not neut?
  deriving (Show)

data ConName = ConName FName Int{-ordinal number, e.g. Zero:0, Succ:1-} Type

data TyConName = TyConName FName Int{-num of indices-} Type [(ConName, Type)]{-constructors-} CaseFunName

data FunName = FunName FName (Maybe Exp) Type

data CaseFunName = CaseFunName FName Type Int{-num of parameters-}

data TyCaseFunName = TyCaseFunName FName Type

type Type = Exp
type ExpType = (Exp, Type)
type SExp2 = SExp' ExpType

instance Show ConName where show (ConName n _ _) = show n
instance Eq ConName where ConName _ n _ == ConName _ n' _ = n == n'
instance Show TyConName where show (TyConName n _ _ _ _) = show n
instance Eq TyConName where TyConName n _ _ _ _ == TyConName n' _ _ _ _ = n == n'
instance Show FunName where show (FunName n _ _) = show n
instance Eq FunName where FunName n _ _ == FunName n' _ _ = n == n'
instance Show CaseFunName where show (CaseFunName n _ _) = CaseName $ show n
instance Eq CaseFunName where CaseFunName n _ _ == CaseFunName n' _ _ = n == n'
instance Show TyCaseFunName where show (TyCaseFunName n _) = MatchName $ show n
instance Eq TyCaseFunName where TyCaseFunName n _ == TyCaseFunName n' _ = n == n'

data FName
    = CFName !Int (SData String)
    | FVecScalar
    | FEqCT | FT2 | Fcoe | FparEval | Ft2C | FprimFix
    | FUnit
    | FInt
    | FWord
    | FNat
    | FBool
    | FFloat
    | FString
    | FChar
    | FOrdering
    | FVecS
    | FEmpty
    | FHList
    | FOutput
    | FType
    | FHCons
    | FHNil
    | FZero
    | FSucc
    | FFalse
    | FTrue
    | FLT
    | FGT
    | FEQ
    | FTT
    | FNil
    | FCons
    | FSplit
    -- todo: elim
    | FEq
    | FOrd
    | FNum
    | FSigned
    | FComponent
    | FIntegral
    | FFloating
    deriving (Eq, Ord)

cFName (RangeSI (Range fn p _), s) = fromMaybe (CFName (hashPos fn p) $ SData s) $ lookup s fntable

fntable =
    [ (,) "'VecScalar"  FVecScalar
    , (,) "'EqCT"  FEqCT
    , (,) "'T2"  FT2
    , (,) "coe"  Fcoe
    , (,) "parEval"  FparEval
    , (,) "t2C"  Ft2C
    , (,) "primFix"  FprimFix
    , (,) "'Unit"  FUnit
    , (,) "'Int"  FInt
    , (,) "'Word"  FWord
    , (,) "'Nat"  FNat
    , (,) "'Bool"  FBool
    , (,) "'Float"  FFloat
    , (,) "'String"  FString
    , (,) "'Char"  FChar
    , (,) "'Ordering"  FOrdering
    , (,) "'VecS"  FVecS
    , (,) "'Empty"  FEmpty
    , (,) "'HList"  FHList
    , (,) "'Eq"  FEq
    , (,) "'Ord"  FOrd
    , (,) "'Num"  FNum
    , (,) "'Signed"  FSigned
    , (,) "'Component"  FComponent
    , (,) "'Integral"  FIntegral
    , (,) "'Floating"  FFloating
    , (,) "'Output"  FOutput
    , (,) "'Type"  FType
    , (,) "HCons"  FHCons
    , (,) "HNil"  FHNil
    , (,) "Zero"  FZero
    , (,) "Succ"  FSucc
    , (,) "False"  FFalse
    , (,) "True"  FTrue
    , (,) "LT"  FLT
    , (,) "GT"  FGT
    , (,) "EQ"  FEQ
    , (,) "TT"  FTT
    , (,) "Nil"  FNil
    , (,) "Cons"  FCons
    , (,) "'Split"  FSplit
    ]

instance Show FName where
  show (CFName _ (SData s)) = s
  show s = fromMaybe (error "show") $ lookup s $ map (\(a, b) -> (b, a)) fntable

-------------------------------------------------------------------------------- auxiliary functions and patterns

infixl 2 `App`, `app_`
infixr 1 :~>

pattern NoLE <- (isNoLabelEnd -> True)

isNoLabelEnd (LabelEnd_ _) = False
isNoLabelEnd _ = True

pattern Fun' f vs i xs n <- Fun_ _ f vs i xs n where Fun' f vs i xs n = Fun_ (foldMap maxDB_ vs <> foldMap maxDB_ xs {- <> iterateN i lowerDB (maxDB_ n)-}) f vs i xs n
pattern Fun f i xs n = Fun' f [] i xs n
pattern UTFun a t b <- (unfixlabel -> Neut (Fun (FunName a _ t) _ (reverse -> b) NoLE))
pattern UFunN a b <- UTFun a _ b
pattern DFun_ fn xs <- Fun fn 0 (reverse -> xs) (Delta _) where
    DFun_ fn@(FunName n _ _) xs = Fun fn 0 (reverse xs) d where
        d = Delta $ SData $ getFunDef n $ \xs -> Neut $ Fun fn 0 (reverse xs) d
pattern TFun' a t b = DFun_ (FunName a Nothing t) b
pattern TFun a t b = Neut (TFun' a t b)

pattern CaseFun_ a b c <- CaseFun__ _ a b c where CaseFun_ a b c = CaseFun__ (maxDB_ c <> foldMap maxDB_ b) a b c
pattern TyCaseFun_ a b c <- TyCaseFun__ _ a b c where TyCaseFun_ a b c = TyCaseFun__ (foldMap maxDB_ b <> maxDB_ c) a b c
pattern App_ a b <- App__ _ a b where App_ a b = App__ (maxDB_ a <> maxDB_ b) a b
pattern CaseFun a b c = Neut (CaseFun_ a b c)
pattern TyCaseFun a b c = Neut (TyCaseFun_ a b c)
pattern App a b <- Neut (App_ (Neut -> a) b)
pattern Var a = Neut (Var_ a)

conParams (conTypeName -> TyConName _ _ _ _ (CaseFunName _ _ pars)) = pars
mkConPars n (snd . getParams . unfixlabel -> TyCon (TyConName _ _ _ _ (CaseFunName _ _ pars)) xs) = take (min n pars) xs
--mkConPars 0 TType = []  -- ?
mkConPars n x@Neut{} = error $ "mkConPars!: " ++ ppShow x
mkConPars n x = error $ "mkConPars: " ++ ppShow (n, x)

makeCaseFunPars te n = case neutType te n of
    (unfixlabel -> TyCon (TyConName _ _ _ _ (CaseFunName _ _ pars)) xs) -> take pars xs
    x -> error $ "makeCaseFunPars: " ++ ppShow x

makeCaseFunPars' te n = case neutType' te n of
    (unfixlabel -> TyCon (TyConName _ _ _ _ (CaseFunName _ _ pars)) xs) -> take pars xs

pattern Closed :: () => Up a => a -> a
pattern Closed a <- a where Closed a = closedExp a

pattern Con x n y <- Con_ _ x n y where Con x n y = Con_ (foldMap maxDB_ y) x n y
pattern ConN s a  <- Con (ConName s _ _) _ a
pattern ConN' s a  <- Con (ConName _ s _) _ a
tCon s i t a = Con (ConName s i t) 0 a
tCon_ k s i t a = Con (ConName s i t) k a
pattern TyCon x y <- TyCon_ _ x y where TyCon x y = TyCon_ (foldMap maxDB_ y) x y
pattern Lam y <- Lam_ _ y where Lam y = Lam_ (lowerDB (maxDB_ y)) y
pattern Pi v x y <- Pi_ _ v x y where Pi v x y = Pi_ (maxDB_ x <> lowerDB (maxDB_ y)) v x y
pattern TyConN s a <- TyCon (TyConName s _ _ _ _) a
pattern TTyCon s t a <- TyCon (TyConName s _ t _ _) a
tTyCon s t a cs = TyCon (TyConName s (error "todo: inum") t (map ((,) (error "tTyCon")) cs) $ CaseFunName (error "TTyCon-A") (error "TTyCon-B") $ length a) a
pattern TTyCon0 s  <- (unfixlabel -> TyCon (TyConName s _ TType _ _) [])
tTyCon0 s cs = Closed $ TyCon (TyConName s 0 TType (map ((,) (error "tTyCon0")) cs) $ CaseFunName (error "TTyCon0-A") (error "TTyCon0-B") 0) []
pattern a :~> b = Pi Visible a b

pattern Unit        <- TTyCon0 FUnit      where Unit = tTyCon0 FUnit [Unit]
pattern TInt        <- TTyCon0 FInt       where TInt = tTyCon0 FInt $ error "cs 1"
pattern TNat        <- TTyCon0 FNat       where TNat = tTyCon0 FNat $ error "cs 3"
pattern TBool       <- TTyCon0 FBool      where TBool = tTyCon0 FBool $ error "cs 4"
pattern TFloat      <- TTyCon0 FFloat     where TFloat = tTyCon0 FFloat $ error "cs 5"
pattern TString     <- TTyCon0 FString    where TString = tTyCon0 FString $ error "cs 6"
pattern TChar       <- TTyCon0 FChar      where TChar = tTyCon0 FChar $ error "cs 7"
pattern TOrdering   <- TTyCon0 FOrdering  where TOrdering = tTyCon0 FOrdering $ error "cs 8"
pattern TVec a b    <- TyConN FVecS {-(TType :~> TNat :~> TType)-} [b, a]

pattern Empty s   <- TyCon (TyConName FEmpty _ _ _ _) [EString s] where
        Empty s    = TyCon (TyConName FEmpty (error "todo: inum2_") (TString :~> TType) (error "todo: tcn cons 3_") $ error "Empty") [EString s]

pattern TT          <- ConN' _ _ where TT = Closed (tCon FTT 0 Unit [])
pattern Zero        <- ConN FZero _ where Zero = Closed (tCon FZero 0 TNat [])
pattern Succ n      <- ConN FSucc (n:_) where Succ n = tCon FSucc 1 (TNat :~> TNat) [n]

pattern CstrT t a b = Neut (CstrT' t a b)
pattern CstrT' t a b = TFun' FEqCT (TType :~> Var 0 :~> Var 1 :~> TType) [t, a, b]
pattern Coe a b w x = TFun Fcoe (TType :~> TType :~> CstrT TType (Var 1) (Var 0) :~> Var 2 :~> Var 2) [a,b,w,x]
pattern ParEval t a b = TFun FparEval (TType :~> Var 0 :~> Var 1 :~> Var 2) [t, a, b]
pattern T2 a b      = TFun FT2 (TType :~> TType :~> TType) [a, b]
pattern CSplit a b c <- UFunN FSplit [a, b, c]

pattern EInt a      = ELit (LInt a)
pattern EFloat a    = ELit (LFloat a)
pattern EChar a     = ELit (LChar a)
pattern EString a   = ELit (LString a)
pattern EBool a <- (getEBool -> Just a) where EBool = mkBool
pattern ENat n <- (fromNatE -> Just n) where ENat = toNatE
pattern ENat' n <- (fromNatE' -> Just n)

toNatE :: Int -> Exp
toNatE 0         = Zero
toNatE n | n > 0 = Closed (Succ (toNatE (n - 1)))

fromNatE :: Exp -> Maybe Int
fromNatE (unfixlabel -> ConN' 0 _) = Just 0
fromNatE (unfixlabel -> ConN' 1 [n]) = (1 +) <$> fromNatE n
fromNatE _ = Nothing

fromNatE' :: Exp -> Maybe Int
fromNatE' (unfixlabel -> Zero) = Just 0
fromNatE' (unfixlabel -> Succ n) = (1 +) <$> fromNatE' n
fromNatE' _ = Nothing

mkBool False = Closed $ tCon FFalse 0 TBool []
mkBool True  = Closed $ tCon FTrue  1 TBool []

getEBool (unfixlabel -> ConN' 0 _) = Just False
getEBool (unfixlabel -> ConN' 1 _) = Just True
getEBool _ = Nothing

mkOrdering x = Closed $ case x of
    LT -> tCon FLT 0 TOrdering []
    EQ -> tCon FEQ 1 TOrdering []
    GT -> tCon FGT 2 TOrdering []

conTypeName :: ConName -> TyConName
conTypeName (ConName _ _ t) = case snd $ getParams t of TyCon n _ -> n

outputType = tTyCon0 FOutput $ error "cs 9"
boolType = TBool
trueExp = EBool True

-------------------------------------------------------------------------------- label handling

pattern LabelEnd x = Neut (LabelEnd_ x)

--pmLabel' :: FunName -> [Exp] -> Int -> [Exp] -> Exp -> Exp
pmLabel' _ (FunName _ _ _) _ 0 as (Neut (Delta (SData f))) = f $ reverse as
pmLabel' md f vs i xs (unfixlabel -> Neut y) = Neut $ Fun_ md f vs i xs y
pmLabel' _ f _ i xs y = error $ "pmLabel: " ++ show (f, i, length xs, y)

pmLabel :: FunName -> [Exp] -> Int -> [Exp] -> Exp -> Exp
pmLabel f vs i xs e = pmLabel' (foldMap maxDB_ vs <> foldMap maxDB_ xs) f vs (i + numLams e) xs (Neut $ dropLams e)

dropLams (unfixlabel -> Lam x) = dropLams x
dropLams (unfixlabel -> Neut x) = x

numLams (unfixlabel -> Lam x) = 1 + numLams x
numLams x = 0

pattern FL' y <- Fun' f _ 0 xs (LabelEnd_ y)
pattern FL y <- Neut (FL' y)

pattern Func n def ty xs <- (mkFunc -> Just (n, def, ty, xs))

mkFunc (Neut (Fun (FunName n (Just def) ty) 0 xs LabelEnd_{})) | Just def' <- removeLams (length xs) def = Just (n, def', ty, xs)
mkFunc _ = Nothing

removeLams 0 (LabelEnd x) = Just x
removeLams n (Lam x) | n > 0 = Lam <$> removeLams (n-1) x
removeLams _ _ = Nothing

pattern UFL y <- (unFunc -> Just y)

unFunc (Neut (Fun' (FunName _ (Just def) _) _ n xs y)) = Just $ iterateN n Lam $ Neut y
unFunc _ = Nothing

unFunc_ (Neut (Fun' _ _ n xs y)) = Just $ iterateN n Lam $ Neut y
unFunc_ _ = Nothing

unfixlabel (FL y) = unfixlabel y
unfixlabel a = a

-------------------------------------------------------------------------------- low-level toolbox

class Subst b a where
    subst_ :: Int -> MaxDB -> b -> a -> a

subst i x a = subst_ i (maxDB_ x) x a

instance Subst ExpType SExp2 where
    subst_ j _ x = mapS (\_ _ -> error "subst: TODO") (const . SGlobal) f2 0
      where
        f2 sn i k = case compare i (k + j) of
            GT -> SVar sn $ i - 1
            LT -> SVar sn i
            EQ -> STyped $ up k x

down :: (Subst Exp a, Up a{-usedVar-}) => Int -> a -> Maybe a
down t x | usedVar t x = Nothing
         | otherwise = Just $ subst_ t mempty (error "impossible: down" :: Exp) x

instance Eq Exp where
    FL a == a' = a == a'
    a == FL a' = a == a'
    Lam a == Lam a' = a == a'
    Pi a b c == Pi a' b' c' = (a, b, c) == (a', b', c')
    Con a n b == Con a' n' b' = (a, n, b) == (a', n', b')
    TyCon a b == TyCon a' b' = (a, b) == (a', b')
    TType == TType = True
    ELit l == ELit l' = l == l'
    Neut a == Neut a' = a == a'
    _ == _ = False

instance Eq Neutral where
    Fun' f vs i a _ == Fun' f' vs' i' a' _ = (f, vs, i, a) == (f', vs', i', a')
    FL' a == a' = a == Neut a'
    a == FL' a' = Neut a == a'
    LabelEnd_ a == LabelEnd_ a' = a == a'
    CaseFun_ a b c == CaseFun_ a' b' c' = (a, b, c) == (a', b', c')
    TyCaseFun_ a b c == TyCaseFun_ a' b' c' = (a, b, c) == (a', b', c')
    App_ a b == App_ a' b' = (a, b) == (a', b')
    Var_ a == Var_ a' = a == a'
    _ == _ = False

free x | cmpDB 0 x = mempty
free x = foldVar (\i k -> Set.fromList [k - i | k >= i]) 0 x

instance Up Exp where
    up_ 0 = \_ e -> e
    up_ n = f where
        f i e | cmpDB i e = e
        f i e = case e of
            Lam_ md b -> Lam_ (upDB n md) (f (i+1) b)
            Pi_ md h a b -> Pi_ (upDB n md) h (f i a) (f (i+1) b)
            Con_ md s pn as  -> Con_ (upDB n md) s pn $ map (f i) as
            TyCon_ md s as -> TyCon_ (upDB n md) s $ map (f i) as
            Neut x -> Neut $ up_ n i x

    usedVar i e
        | cmpDB i e = False
        | otherwise = ((getAny .) . foldVar ((Any .) . (==))) i e

    foldVar f i = \case
        Lam b -> foldVar f (i+1) b
        Pi _ a b -> foldVar f i a <> foldVar f (i+1) b
        Con _ _ as -> foldMap (foldVar f i) as
        TyCon _ as -> foldMap (foldVar f i) as
        TType -> mempty
        ELit{} -> mempty
        Neut x -> foldVar f i x

    closedExp = \case
        Lam_ _ c -> Lam_ mempty c
        Pi_ _ a b c -> Pi_ mempty a (closedExp b) c
        Con_ _ a b c -> Con_ mempty a b (closedExp <$> c)
        TyCon_ _ a b -> TyCon_ mempty a (closedExp <$> b)
        e@TType{} -> e
        e@ELit{} -> e
        Neut a -> Neut $ closedExp a

instance HasMaxDB Exp where
    maxDB_ = \case
        Lam_ c _ -> c
        Pi_ c _ _ _ -> c
        Con_ c _ _ _ -> c
        TyCon_ c _ _ -> c

        TType -> mempty
        ELit{} -> mempty
        Neut x -> maxDB_ x

instance Subst Exp Exp where
    subst_ i0 dx x = f i0
      where
        f i (Neut n) = substNeut n
          where
            substNeut e | cmpDB i e = Neut e
            substNeut e = case e of
                Var_ k -> case compare k i of GT -> Var $ k - 1; LT -> Var k; EQ -> up (i - i0) x
                CaseFun_ s as n -> evalCaseFun s (f i <$> as) (substNeut n)
                TyCaseFun_ s as n -> evalTyCaseFun s (f i <$> as) (substNeut n)
                App_ a b  -> app_ (substNeut a) (f i b)
                Fun_ md fn vs c xs v -> pmLabel' (md <> upDB i dx) fn (f i <$> vs) c (f i <$> xs) $ f (i + c) $ Neut v
                LabelEnd_ a -> LabelEnd $ f i a
                d@Delta{} -> Neut d
        f i e | cmpDB i e = e
        f i e = case e of
            Lam_ md b -> Lam_ (md <> upDB i dx) (f (i+1) b)
            Con_ md s n as  -> Con_ (md <> upDB i dx) s n $ f i <$> as
            Pi_ md h a b  -> Pi_ (md <> upDB i dx) h (f i a) (f (i+1) b)
            TyCon_ md s as -> TyCon_ (md <> upDB i dx) s $ f i <$> as

instance Up Neutral where

    up_ 0 = \_ e -> e
    up_ n = f where
        f i e | cmpDB i e = e
        f i e = case e of
            Var_ k -> Var_ $ if k >= i then k+n else k
            CaseFun__ md s as ne -> CaseFun__ (upDB n md) s (up_ n i <$> as) (up_ n i ne)
            TyCaseFun__ md s as ne -> TyCaseFun__ (upDB n md) s (up_ n i <$> as) (up_ n i ne)
            App__ md a b -> App__ (upDB n md) (up_ n i a) (up_ n i b)
            Fun_ md fn vs c x y -> Fun_ (upDB n md) fn (up_ n i <$> vs) c (up_ n i <$> x) $ up_ n (i + c) y
            LabelEnd_ x -> LabelEnd_ $ up_ n i x
            d@Delta{} -> d

    usedVar i e
        | cmpDB i e = False
        | otherwise = ((getAny .) . foldVar ((Any .) . (==))) i e

    foldVar f i = \case
        Var_ k -> f i k
        CaseFun_ _ as n -> foldMap (foldVar f i) as <> foldVar f i n
        TyCaseFun_ _ as n -> foldMap (foldVar f i) as <> foldVar f i n
        App_ a b -> foldVar f i a <> foldVar f i b
        Fun' _ vs j x d -> foldMap (foldVar f i) vs <> foldMap (foldVar f i) x -- <> foldVar f (i+j) d
        LabelEnd_ x -> foldVar f i x
        Delta{} -> mempty

    closedExp = \case
        x@Var_{} -> error "impossible"
        CaseFun__ _ a as n -> CaseFun__ mempty a (closedExp <$> as) (closedExp n)
        TyCaseFun__ _ a as n -> TyCaseFun__ mempty a (closedExp <$> as) (closedExp n)
        App__ _ a b -> App__ mempty (closedExp a) (closedExp b)
        Fun_ _ f l i x y -> Fun_ mempty f l i (closedExp <$> x) y
        LabelEnd_ a -> LabelEnd_ (closedExp a)
        d@Delta{} -> d

instance HasMaxDB Neutral where
    maxDB_ = \case
        Var_ k -> varDB k
        CaseFun__ c _ _ _ -> c
        TyCaseFun__ c _ _ _ -> c
        App__ c a b -> c
        Fun_ c _ _ _ _ _ -> c
        LabelEnd_ x -> maxDB_ x
        Delta{} -> mempty

instance (Subst x a, Subst x b) => Subst x (a, b) where
    subst_ i dx x (a, b) = (subst_ i dx x a, subst_ i dx x b)

varType' :: Int -> [Exp] -> Exp
varType' i vs = vs !! i

varType :: String -> Int -> Env -> (Binder, Exp)
varType err n_ env = f n_ env where
    f n (EAssign i (x, _) es) = second (subst i x) $ f (if n < i then n else n+1) es
    f n (EBind2 b t es)  = if n == 0 then (b, up 1 t) else second (up 1) $ f (n-1) es
    f n (ELet2 _ (x, t) es) = if n == 0 then (BLam Visible{-??-}, up 1 t) else second (up 1) $ f (n-1) es
    f n e = either (error $ "varType: " ++ err ++ "\n" ++ show n_ ++ "\n" ++ ppShow env) (f n) $ parent e

-------------------------------------------------------------------------------- reduction
evalCaseFun a ps (Con n@(ConName _ i _) _ vs)
    | i /= (-1) = foldl app_ (ps !!! (i + 1)) vs
    | otherwise = error "evcf"
  where
    xs !!! i | i >= length xs = error $ "!!! " ++ show a ++ " " ++ show i ++ " " ++ show n ++ "\n" ++ ppShow ps
    xs !!! i = xs !! i
evalCaseFun a b (FL c) = evalCaseFun a b c
evalCaseFun a b (Neut c) = CaseFun a b c
evalCaseFun a b x = error $ "evalCaseFun: " ++ show (a, x)

evalTyCaseFun a b (FL c) = evalTyCaseFun a b c
evalTyCaseFun a b (Neut c) = TyCaseFun a b c
evalTyCaseFun (TyCaseFunName FType ty) (_: t: f: _) TType = t
evalTyCaseFun (TyCaseFunName n ty) (_: t: f: _) (TyCon (TyConName n' _ _ _ _) vs) | n == n' = foldl app_ t vs
--evalTyCaseFun (TyCaseFunName n ty) [_, t, f] (DFun (FunName n' _) vs) | n == n' = foldl app_ t vs  -- hack
evalTyCaseFun (TyCaseFunName n ty) (_: t: f: _) _ = f

evalCoe a b (FL x) d = evalCoe a b x d
evalCoe a b TT d = d
evalCoe a b t d = Coe a b t d

{- todo: generate
    DFun n@(FunName "natElim" _) [a, z, s, Succ x] -> let      -- todo: replace let with better abstraction
                sx = s `app_` x
            in sx `app_` eval (DFun n [a, z, s, x])
    MT "natElim" [_, z, s, Zero] -> z
    DFun na@(FunName "finElim" _) [m, z, s, n, ConN "FSucc" [i, x]] -> let six = s `app_` i `app_` x-- todo: replace let with better abstraction
        in six `app_` eval (DFun na [m, z, s, i, x])
    MT "finElim" [m, z, s, n, ConN "FZero" [i]] -> z `app_` i
-}

getFunDef s f = case s of
  FEqCT -> \case (t: a: b: _) -> cstr t a b
  FT2 -> \case (a: b: _) -> t2 a b
  Ft2C -> \case (a: b: _) -> t2C a b
  Fcoe -> \case (a: b: t: d: _) -> evalCoe a b t d
  FparEval -> \case (t: a: b: _) -> parEval t a b
      where
        parEval _ (LabelEnd x) _ = LabelEnd x
        parEval _ _ (LabelEnd x) = LabelEnd x
        parEval t a b = ParEval t a b
  CFName _ (SData s) -> case s of
    "unsafeCoerce" -> \case xs@(_: _: x@NonNeut: _) -> x; xs -> f xs
    "reflCstr" -> \case (a: _) -> TT

    "hlistNilCase" -> \case (_: x: (unfixlabel -> Con n@(ConName _ 0 _) _ _): _) -> x; xs -> f xs
    "hlistConsCase" -> \case (_: _: _: x: (unfixlabel -> Con n@(ConName _ 1 _) _ (_: _: a: b: _)): _) -> x `app_` a `app_` b; xs -> f xs

    -- general compiler primitives
    "primAddInt" -> \case (EInt i: EInt j: _) -> EInt (i + j); xs -> f xs
    "primSubInt" -> \case (EInt i: EInt j: _) -> EInt (i - j); xs -> f xs
    "primModInt" -> \case (EInt i: EInt j: _) -> EInt (i `mod` j); xs -> f xs
    "primSqrtFloat" -> \case (EFloat i: _) -> EFloat $ sqrt i; xs -> f xs
    "primRound" -> \case (EFloat i: _) -> EInt $ round i; xs -> f xs
    "primIntToFloat" -> \case (EInt i: _) -> EFloat $ fromIntegral i; xs -> f xs
    "primIntToNat" -> \case (EInt i: _) -> ENat $ fromIntegral i; xs -> f xs
    "primCompareInt" -> \case (EInt x: EInt y: _) -> mkOrdering $ x `compare` y; xs -> f xs
    "primCompareFloat" -> \case (EFloat x: EFloat y: _) -> mkOrdering $ x `compare` y; xs -> f xs
    "primCompareChar" -> \case (EChar x: EChar y: _) -> mkOrdering $ x `compare` y; xs -> f xs
    "primCompareString" -> \case (EString x: EString y: _) -> mkOrdering $ x `compare` y; xs -> f xs

    -- LambdaCube 3D specific primitives
    "PrimGreaterThan" -> \case (t: _: _: _: _: _: _: x: y: _) | Just r <- twoOpBool (>) t x y -> r; xs -> f xs
    "PrimGreaterThanEqual" -> \case (t: _: _: _: _: _: _: x: y: _) | Just r <- twoOpBool (>=) t x y -> r; xs -> f xs
    "PrimLessThan" -> \case (t: _: _: _: _: _: _: x: y: _) | Just r <- twoOpBool (<) t x y -> r; xs -> f xs
    "PrimLessThanEqual" -> \case (t: _: _: _: _: _: _: x: y: _) | Just r <- twoOpBool (<=) t x y -> r; xs -> f xs
    "PrimEqualV" -> \case (t: _: _: _: _: _: _: x: y: _) | Just r <- twoOpBool (==) t x y -> r; xs -> f xs
    "PrimNotEqualV" -> \case (t: _: _: _: _: _: _: x: y: _) | Just r <- twoOpBool (/=) t x y -> r; xs -> f xs
    "PrimEqual" -> \case (t: _: _: x: y: _) | Just r <- twoOpBool (==) t x y -> r; xs -> f xs
    "PrimNotEqual" -> \case (t: _: _: x: y: _) | Just r <- twoOpBool (/=) t x y -> r; xs -> f xs
    "PrimSubS" -> \case (_: _: _: _: x: y: _) | Just r <- twoOp (-) x y -> r; xs -> f xs
    "PrimSub" -> \case (_: _: x: y: _) | Just r <- twoOp (-) x y -> r; xs -> f xs
    "PrimAddS" -> \case (_: _: _: _: x: y: _) | Just r <- twoOp (+) x y -> r; xs -> f xs
    "PrimAdd" -> \case (_: _: x: y: _) | Just r <- twoOp (+) x y -> r; xs -> f xs
    "PrimMulS" -> \case (_: _: _: _: x: y: _) | Just r <- twoOp (*) x y -> r; xs -> f xs
    "PrimMul" -> \case (_: _: x: y: _) | Just r <- twoOp (*) x y -> r; xs -> f xs
    "PrimDivS" -> \case (_: _: _: _: _: x: y: _) | Just r <- twoOp_ (/) div x y -> r; xs -> f xs
    "PrimDiv" -> \case (_: _: _: _: _: x: y: _) | Just r <- twoOp_ (/) div x y -> r; xs -> f xs
    "PrimModS" -> \case (_: _: _: _: _: x: y: _) | Just r <- twoOp_ modF mod x y -> r; xs -> f xs
    "PrimMod" -> \case (_: _: _: _: _: x: y: _) | Just r <- twoOp_ modF mod x y -> r; xs -> f xs
    "PrimNeg" -> \case (_: x: _) | Just r <- oneOp negate x -> r; xs -> f xs
    "PrimAnd" -> \case (EBool x: EBool y: _) -> EBool (x && y); xs -> f xs
    "PrimOr" -> \case (EBool x: EBool y: _) -> EBool (x || y); xs -> f xs
    "PrimXor" -> \case (EBool x: EBool y: _) -> EBool (x /= y); xs -> f xs
    "PrimNot" -> \case (TNat: _: _: EBool x: _) -> EBool $ not x; xs -> f xs

    _ -> f

  _ -> f

cstr = f []
  where
    f z ty a a' = f_ z (unfixlabel ty) (unfixlabel a) (unfixlabel a')

    f_ _ _ a a' | a == a' = Unit
    f_ ns typ (LabelEnd a) (LabelEnd a') = f ns typ a a'
    f_ ns typ (Con a n xs) (Con a' n' xs') | a == a' && n == n' && length xs == length xs' = 
        ff ns (foldl appTy (conType typ a) $ mkConPars n typ) $ zip xs xs'
    f_ ns typ (TyCon a xs) (TyCon a' xs') | a == a' && length xs == length xs' = 
        ff ns (nType a) $ zip xs xs'
    f_ (_: ns) typ{-down?-} (down 0 -> Just a) (down 0 -> Just a') = f ns typ a a'
    f_ ns TType (Pi h a b) (Pi h' a' b') | h == h' = t2 (f ns TType a a') (f ((a, a'): ns) TType b b')

    f_ [] TType (UFunN FVecScalar [a, b]) (UFunN FVecScalar [a', b']) = t2 (f [] TNat a a') (f [] TType b b')
    f_ [] TType (UFunN FVecScalar [a, b]) (TVec a' b') = t2 (f [] TNat a a') (f [] TType b b')
    f_ [] TType (UFunN FVecScalar [a, b]) t@NonNeut = t2 (f [] TNat a (ENat 1)) (f [] TType b t)
    f_ [] TType (TVec a' b') (UFunN FVecScalar [a, b]) = t2 (f [] TNat a' a) (f [] TType b' b)
    f_ [] TType t@NonNeut (UFunN FVecScalar [a, b]) = t2 (f [] TNat a (ENat 1)) (f [] TType b t)

    f_ [] typ a@Neut{} a' = CstrT typ a a'
    f_ [] typ a a'@Neut{} = CstrT typ a a'
    f_ ns typ a a' = Empty $ unlines [ "can not unify", ppShow a, "with", ppShow a' ]

    ff _ _ [] = Unit
    ff ns tt@(Pi v t _) ((t1, t2'): ts) = t2 (f ns t t1 t2') $ ff ns (appTy tt t1) ts
    ff ns t zs = error $ "ff: " -- ++ show (a, n, length xs', length $ mkConPars n typ) ++ "\n" ++ ppShow (nType a) ++ "\n" ++ ppShow (foldl appTy (nType a) $ mkConPars n typ) ++ "\n" ++ ppShow (zip xs xs') ++ "\n" ++ ppShow zs ++ "\n" ++ ppShow t

pattern NonNeut <- (nonNeut -> True)

nonNeut FL{} = True
nonNeut Neut{} = False
nonNeut _ = True

t2C (unfixlabel -> TT) (unfixlabel -> TT) = TT
t2C a b = TFun Ft2C (Unit :~> Unit :~> Unit) [a, b]

t2 (unfixlabel -> Unit) a = a
t2 a (unfixlabel -> Unit) = a
t2 (unfixlabel -> Empty a) (unfixlabel -> Empty b) = Empty (a <> b)
t2 (unfixlabel -> Empty s) _ = Empty s
t2 _ (unfixlabel -> Empty s) = Empty s
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

twoOpBool :: (forall a . Ord a => a -> a -> Bool) -> Exp -> Exp -> Exp -> Maybe Exp
twoOpBool f t (EFloat x)  (EFloat y)  = Just $ EBool $ f x y
twoOpBool f t (EInt x)    (EInt y)    = Just $ EBool $ f x y
twoOpBool f t (EString x) (EString y) = Just $ EBool $ f x y
twoOpBool f t (EChar x)   (EChar y)   = Just $ EBool $ f x y
twoOpBool f TNat (ENat x)    (ENat y)    = Just $ EBool $ f x y
twoOpBool _ _ _ _ = Nothing

app_ :: Exp -> Exp -> Exp
app_ (Lam x) a = subst 0 a x
app_ (Con s n xs) a = if n < conParams s then Con s (n+1) xs else Con s n (xs ++ [a])
app_ (TyCon s xs) a = TyCon s (xs ++ [a])
app_ (Neut f) a = neutApp f a
  where
    neutApp (FL' x) a = app_ x a    -- ???
    neutApp (Fun' f vs i xs e) a | i > 0 = pmLabel f vs (i-1) (a: xs) (subst (i-1) (up (i-1) a) $ Neut e)
    neutApp f a = Neut $ App_ f a

-------------------------------------------------------------------------------- constraints env

data CEnv a
    = MEnd a
    | Meta Exp (CEnv a)
    | Assign !Int ExpType (CEnv a)       -- De Bruijn index decreasing assign reservedOp, only for metavariables (non-recursive)
  deriving (Show, Functor)

instance (Subst Exp a, Up a) => Up (CEnv a) where
    up_ n i = iterateN n $ up1_ i
    up1_ i = \case
        MEnd a -> MEnd $ up1_ i a
        Meta a b -> Meta (up1_ i a) (up1_ (i+1) b)
        Assign j a b -> handleLet i j $ \i' j' -> assign j' (up1_ i' a) (up1_ i' b)
          where
            handleLet i j f
                | i >  j = f (i-1) j
                | i <= j = f i (j+1)

    usedVar i a = error "usedVar @(CEnv _)"

    foldVar _ _ _ = error "foldVar @(CEnv _)"

--    maxDB_ _ = error "maxDB_ @(CEnv _)"

instance (Subst Exp a, Up a) => Subst Exp (CEnv a) where
    subst_ i dx x = \case
        MEnd a -> MEnd $ subst_ i dx x a
        Meta a b  -> Meta (subst_ i dx x a) (subst_ (i+1) (upDB 1 dx) (up 1 x) b)
        Assign j a b
            | j > i, Just a' <- down i a       -> assign (j-1) a' (subst i (subst (j-1) (fst a') x) b)
            | j > i, Just x' <- down (j-1) x   -> assign (j-1) (subst i x' a) (subst i x' b)
            | j < i, Just a' <- down (i-1) a   -> assign j a' (subst (i-1) (subst j (fst a') x) b)
            | j < i, Just x' <- down j x       -> assign j (subst (i-1) x' a) (subst (i-1) x' b)
            | j == i    -> Meta (cstr (snd a) x $ fst a) $ up1_ 0 b

--assign :: (Int -> Exp -> CEnv Exp -> a) -> (Int -> Exp -> CEnv Exp -> a) -> Int -> Exp -> CEnv Exp -> a
swapAssign _ clet i (Var j, t) b | i > j = clet j (Var (i-1), t) $ subst j (Var (i-1)) $ up1_ i b
swapAssign clet _ i a b = clet i a b

assign = swapAssign Assign Assign


-------------------------------------------------------------------------------- De-Bruijn limit

newtype MaxDB = MaxDB {getMaxDB :: Int} -- True: closed

instance Monoid MaxDB where
    mempty = MaxDB 0
    MaxDB a  `mappend` MaxDB a'  = MaxDB $ max a a'
      where
        max 0 x = x
        max _ _ = 1 --

instance Show MaxDB where show _ = "MaxDB"

varDB i = MaxDB 1 --

lowerDB = id --

cmpDB _ (maxDB_ -> MaxDB x) = x == 0

upDB _ (MaxDB 0) = MaxDB 0
upDB x (MaxDB i) = MaxDB $ x + i

{-
data Na = Ze | Su Na

newtype MaxDB = MaxDB {getMaxDB :: Na} -- True: closed

instance Monoid MaxDB where
    mempty = MaxDB Ze
    MaxDB a  `mappend` MaxDB a'  = MaxDB $ max a a'
      where
        max Ze x = x
        max (Su i) x = Su $ case x of
            Ze -> i
            Su j -> max i j

instance Show MaxDB where show _ = "MaxDB"

varDB i = MaxDB $ Su $ fr i
  where
    fr 0 = Ze
    fr i = Su $ fr $ i-1

lowerDB (MaxDB Ze) = MaxDB Ze
lowerDB (MaxDB (Su i)) = MaxDB i

cmpDB _ (maxDB_ -> MaxDB x) = case x of Ze -> True; _ -> False -- == 0

upDB _ (MaxDB Ze) = MaxDB Ze
upDB x (MaxDB i) = MaxDB $ ad x i where
  ad 0 i = i
  ad n i = Su $ ad (n-1) i
-}

class HasMaxDB a where
    maxDB_ :: a -> MaxDB

instance (HasMaxDB a, HasMaxDB b) => HasMaxDB (a, b) where
    maxDB_ (a, b) = maxDB_ a <> maxDB_ b


-------------------------------------------------------------------------------- environments

-- SExp + Exp zipper
data Env
    = EBind1 SI Binder Env SExp2            -- zoom into first parameter of SBind
    | EBind2_ SI Binder Type Env             -- zoom into second parameter of SBind
    | EApp1 SI Visibility Env SExp2
    | EApp2 SI Visibility ExpType Env
    | ELet1 SIName Env SExp2
    | ELet2 SIName ExpType Env
    | EGlobal
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
    EGlobal              -> Left ()

-------------------------------------------------------------------------------- simple typing

litType = \case
    LInt _    -> TInt
    LFloat _  -> TFloat
    LString _ -> TString
    LChar _   -> TChar

class NType a where nType :: a -> Type

instance NType FunName where nType (FunName _ _ t) = t
instance NType TyConName where nType (TyConName _ _ t _ _) = t
instance NType CaseFunName where nType (CaseFunName _ t _) = t
instance NType TyCaseFunName where nType (TyCaseFunName _ t) = t

conType (snd . getParams . unfixlabel -> TyCon (TyConName _ _ _ cs _) _) (ConName _ n t) = t --snd $ cs !! n

neutType te = \case
    App_ f x        -> appTy (neutType te f) x
    Var_ i          -> snd $ varType "C" i te
    CaseFun_ s ts n -> appTy (foldl appTy (nType s) $ makeCaseFunPars te n ++ ts) (Neut n)
    TyCaseFun_ s [m, t, f] n -> foldl appTy (nType s) [m, t, Neut n, f]
    Fun' s _ _ a _ -> foldlrev appTy (nType s) a

neutType' te = \case
    App_ f x        -> appTy (neutType' te f) x
    Var_ i          -> varType' i te
    CaseFun_ s ts n -> appTy (foldl appTy (nType s) $ makeCaseFunPars' te n ++ ts) (Neut n)
    TyCaseFun_ s [m, t, f] n -> foldl appTy (nType s) [m, t, Neut n, f]
    Fun' s _ _ a _     -> foldlrev appTy (nType s) a

mkExpTypes t [] = []
mkExpTypes t@(Pi _ a _) (x: xs) = (x, t): mkExpTypes (appTy t x) xs

appTy (Pi _ a b) x = subst 0 x b
appTy t x = error $ "appTy: " ++ show t

-------------------------------------------------------------------------------- error messages

data ErrorMsg
    = ErrorMsg String
    | ECantFind SName SI
    | ETypeError String SI
    | ERedefined SName SI SI

instance NFData ErrorMsg where
    rnf = \case
        ErrorMsg m -> rnf m
        ECantFind a b -> rnf (a, b)
        ETypeError a b -> rnf (a, b)
        ERedefined a b c -> rnf (a, b, c)

errorRange_ = \case
    ErrorMsg s -> []
    ECantFind s si -> [si]
    ETypeError msg si -> [si]
    ERedefined s si si' -> [si, si']

instance Show ErrorMsg where
    show = \case
        ErrorMsg s -> s
        ECantFind s si -> "can't find: " ++ s ++ " in " ++ showSI si
        ETypeError msg si -> "type error: " ++ msg ++ "\nin " ++ showSI si ++ "\n"
        ERedefined s si si' -> "already defined " ++ s ++ " at " ++ showSI si ++ "\n and at " ++ showSI si'


-------------------------------------------------------------------------------- inference

-- inference monad
type IM m = ExceptT ErrorMsg (ReaderT (Extensions, GlobalEnv) (WriterT Infos m))

expAndType s (e, t, si) = (e, t)

-- todo: do only if NoTypeNamespace extension is not on
lookupName s@('\'':s') m = expAndType s <$> (Map.lookup s m `mplus` Map.lookup s' m)
lookupName s m           = expAndType s <$> Map.lookup s m

getDef te si s = do
    nv <- asks snd
    maybe (throwError' $ ECantFind s si) return (lookupName s nv)

type ExpType' = CEnv ExpType

inferN :: forall m . Monad m => Env -> SExp2 -> IM m ExpType'
inferN e s = do
    b <- asks $ (TraceTypeCheck `elem`) . fst
    mapExceptT (mapReaderT $ mapWriterT $ fmap filt) $ inferN_ (if b then \s x m -> tell [ITrace s x] >> m else \_ _ m -> m) e s
  where
    filt (e@Right{}, is) = (e, filter f is)
    filt x = x

    f ITrace{} = False
    f _ = True

substTo i x = subst i x . up1_ (i+1)

inferN_ :: forall m . Monad m => (forall a . String -> String -> IM m a -> IM m a) -> Env -> SExp2 -> IM m ExpType'
inferN_ tellTrace = infer  where

    infer :: Env -> SExp2 -> IM m ExpType'
    infer te exp = tellTrace "infer" (showEnvSExp te exp) $ (if debug then fmap (fmap{-todo-} $ recheck' "infer" te) else id) $ case exp of
        Parens x        -> infer te x
        SAnn x t        -> checkN (CheckIType x te) t TType
        SRHS x     -> infer (ELabelEnd te) x
        SVar (si, _) i  -> focus_' te exp (Var i, snd $ varType "C2" i te)
        SLit si l       -> focus_' te exp (ELit l, litType l)
        STyped et       -> focus_' te exp et
        SGlobal (si, s) -> focus_' te exp =<< getDef te si s
        SLet le a b     -> infer (ELet1 le te b{-in-}) a{-let-} -- infer te SLamV b `SAppV` a)
        SApp_ si h a b  -> infer (EApp1 (si `validate` [sourceInfo a, sourceInfo b]) h te b) a
        SBind_ si h _ a b -> infer ((if h /= BMeta then CheckType_ (sourceInfo exp) TType else id) $ EBind1 si h te $ (if isPi h then TyType else id) b) a

    checkN :: Env -> SExp2 -> Type -> IM m ExpType'
    checkN te x t = tellTrace "check" (showEnvSExpType te x t) $ checkN_ te x t

    checkN_ te (Parens e) t = checkN_ te e t
    checkN_ te e t
        | x@(SGlobal (si, MatchName n)) `SAppV` SLamV (Wildcard _) `SAppV` a `SAppV` SVar siv v `SAppV` b <- e
            = infer te $ x `SAppV` SLam Visible SType (STyped (subst (v+1) (Var 0) $ up 1 t, TType)) `SAppV` a `SAppV` SVar siv v `SAppV` b
            -- temporal hack
        | x@(SGlobal (si, CaseName "'Nat")) `SAppV` SLamV (Wildcard _) `SAppV` a `SAppV` b `SAppV` SVar siv v <- e
            = infer te $ x `SAppV` SLamV (STyped (substTo (v+1) (Var 0) $ up 1 t, TType)) `SAppV` a `SAppV` b `SAppV` SVar siv v
            -- temporal hack
        | x@(SGlobal (si, CaseName "'VecS")) `SAppV` SLamV (SLamV (Wildcard _)) `SAppV` a `SAppV` b `SAppV` c `SAppV` SVar siv v <- e
        , TyConN FVecS [_, Var n'] <- snd $ varType "xx" v te
            = infer te $ x `SAppV` SLamV (SLamV (STyped (substTo (n'+2) (Var 1) $ up 2 t, TType))) `SAppV` a `SAppV` b `SAppV` c `SAppV` SVar siv v

{-
            -- temporal hack
        | x@(SGlobal (si, "'HListCase")) `SAppV` SLamV (SLamV (Wildcard _)) `SAppV` a `SAppV` b `SAppV` SVar siv v <- e
        , TVec (Var n') _ <- snd $ varType "xx" v te
            = infer te $ x `SAppV` SLamV (SLamV (STyped (subst (n'+2) (Var 1) $ up1_ (n'+3) $ up 2 t, TType))) `SAppV` a `SAppV` b `SAppV` SVar siv v
-}
        | SRHS x <- e = checkN (ELabelEnd te) x t
        | SApp_ si h a b <- e = infer (CheckAppType si h t te b) a
        | SLam h a b <- e, Pi h' x y <- t, h == h'  = do
            tellType e t
            let same = checkSame te a x
            if same then checkN (EBind2 (BLam h) x te) b y else error $ "checkSame:\n" ++ show a ++ "\nwith\n" ++ showEnvExp te (x, TType)
        | Pi Hidden a b <- t = do
            bb <- notHiddenLam e
            if bb then checkN (EBind2 (BLam Hidden) a te) (up1 e) b
                 else infer (CheckType_ (sourceInfo e) t te) e
        | otherwise = infer (CheckType_ (sourceInfo e) t te) e
      where
        -- todo
        notHiddenLam = \case
            SLam Visible _ _ -> return True
            SGlobal (si,s) -> do
                nv <- asks snd
                case fromMaybe (error $ "infer: can't find: " ++ s) $ lookupName s nv of
                    (Lam _, Pi Hidden _ _) -> return False
                    _ -> return True
            _ -> return False
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
    checkSame te (SBind_ _ BMeta _ SType (STyped (Var 0, _))) a = True
    checkSame te a b = error $ "checkSame: " ++ show (a, b)

    hArgs (Pi Hidden _ b) = 1 + hArgs b
    hArgs _ = 0

    focus_' env si eet = tellType si (snd eet) >> focus_ env eet

    focus_ :: Env -> ExpType -> IM m ExpType'
    focus_ env eet@(e, et) = tellTrace "focus" (showEnvExp env eet) $ (if debug then fmap (fmap{-todo-} $ recheck' "focus" env) else id) $ case env of
        ELabelEnd te -> focus_ te (LabelEnd e, et)
--        CheckSame x te -> focus_ (EBind2_ (debugSI "focus_ CheckSame") BMeta (cstr x e) te) $ up 1 eet
        CheckAppType si h t te b   -- App1 h (CheckType t te) b
            | Pi h' x (down 0 -> Just y) <- et, h == h' -> case t of
                Pi Hidden t1 t2 | h == Visible -> focus_ (EApp1 si h (CheckType_ (sourceInfo b) t te) b) eet  -- <<e>> b : {t1} -> {t2}
                _ -> focus_ (EBind2_ (sourceInfo b) BMeta (cstr TType t y) $ EApp1 si h te b) $ up 1 eet
            | otherwise -> focus_ (EApp1 si h (CheckType_ (sourceInfo b) t te) b) eet
        EApp1 si h te b
            | Pi h' x y <- et, h == h' -> checkN (EApp2 si h eet te) b x
            | Pi Hidden x y  <- et, h == Visible -> focus_ (EApp1 mempty Hidden env $ Wildcard $ Wildcard SType) eet  --  e b --> e _ b
--            | CheckType (Pi Hidden _ _) te' <- te -> error "ok"
--            | CheckAppType Hidden _ te' _ <- te -> error "ok"
            | otherwise -> infer (CheckType_ (sourceInfo b) (Var 2) $ cstr' h (up 2 et) (Pi Visible (Var 1) (Var 1)) (up 2 e) $ EBind2_ (sourceInfo b) BMeta TType $ EBind2_ (sourceInfo b) BMeta TType te) (up 3 b)
          where
            cstr' h x y e = EApp2 mempty h (evalCoe (up 1 x) (up 1 y) (Var 0) (up 1 e), up 1 y) . EBind2_ (sourceInfo b) BMeta (cstr TType x y)
        ELet2 ln (x{-let-}, xt) te -> focus_ te $ subst 0 (mkELet ln x xt){-let-} eet{-in-}
        CheckIType x te -> checkN te x e
        CheckType_ si t te
            | hArgs et > hArgs t
                            -> focus_ (EApp1 mempty Hidden (CheckType_ si t te) $ Wildcard $ Wildcard SType) eet
            | hArgs et < hArgs t, Pi Hidden t1 t2 <- t
                            -> focus_ (CheckType_ si t2 $ EBind2 (BLam Hidden) t1 te) eet
            | otherwise    -> focus_ (EBind2_ si BMeta (cstr TType t et) te) $ up 1 eet
        EApp2 si h (a, at) te    -> focus_' te si (app_ a e, appTy at e)        --  h??
        EBind1 si h te b   -> infer (EBind2_ (sourceInfo b) h e te) b
        EBind2_ si (BLam h) a te -> focus_ te $ lamPi h a eet
        EBind2_ si (BPi h) a te -> focus_' te si (Pi h a e, TType)
        _ -> focus2 env $ MEnd eet

    focus2 :: Env -> CEnv ExpType -> IM m ExpType'
    focus2 env eet = case env of
--        ELabelEnd te ->
        ELet1 le te b{-in-} -> infer (ELet2 le (replaceMetas' eet{-let-}) te) b{-in-}
        EBind2_ si BMeta tt_ te
            | ELabelEnd te'   <- te -> refocus (ELabelEnd $ EBind2_ si BMeta tt_ te') eet
            | Unit <- tt    -> refocus te $ subst 0 TT eet
            | Empty msg <- tt -> throwError' $ ETypeError msg si
            | T2 x y <- tt, let te' = EBind2_ si BMeta (up 1 y) $ EBind2_ si BMeta x te
                            -> refocus te' $ subst 2 (t2C (Var 1) (Var 0)) $ up 2 eet
            | CstrT t a b <- tt, Just r <- cst (a, t) b -> r
            | CstrT t a b <- tt, Just r <- cst (b, t) a -> r
            | isCstr tt, EBind2 h x te' <- te{-, h /= BMeta todo: remove-}, Just x' <- down 0 tt, x == x'
                            -> refocus te $ subst 1 (Var 0) eet
            | EBind2 h x te' <- te, h /= BMeta, Just b' <- down 0 tt
                            -> refocus (EBind2_ si h (up 1 x) $ EBind2_ si BMeta b' te') $ subst 2 (Var 0) $ up 1 eet
            | ELet2 le (x, xt) te' <- te, Just b' <- down 0 tt
                            -> refocus (ELet2 le (up 1 x, up 1 xt) $ EBind2_ si BMeta b' te') $ subst 2 (Var 0) $ up 1 eet
            | EBind1 si h te' x <- te -> refocus (EBind1 si h (EBind2_ si BMeta tt_ te') $ up1_ 1 x) eet
            | ELet1 le te' x     <- te, floatLetMeta $ snd $ replaceMetas' $ Meta tt_ $ eet
                                    -> refocus (ELet1 le (EBind2_ si BMeta tt_ te') $ up1_ 1 x) eet
            | CheckAppType si h t te' x <- te -> refocus (CheckAppType si h (up 1 t) (EBind2_ si BMeta tt_ te') $ up1 x) eet
            | EApp1 si h te' x <- te -> refocus (EApp1 si h (EBind2_ si BMeta tt_ te') $ up1 x) eet
            | EApp2 si h x te' <- te -> refocus (EApp2 si h (up 1 x) $ EBind2_ si BMeta tt_ te') eet
            | CheckType_ si t te' <- te -> refocus (CheckType_ si (up 1 t) $ EBind2_ si BMeta tt_ te') eet
--            | CheckIType x te' <- te -> refocus (CheckType_ si (up 1 t) $ EBind2_ si BMeta tt te') eet
            | otherwise             -> focus2 te $ Meta tt_ eet
          where
            tt = unfixlabel tt_
            refocus = refocus_ focus2
            cst :: ExpType -> Exp -> Maybe (IM m ExpType')
            cst x = \case
                Var i | fst (varType "X" i te) == BMeta
                      , Just y <- down i x
                      -> Just $ join swapAssign (\i x -> refocus $ EAssign i x te) i y $ subst 0 {-ReflCstr y-}TT $ subst (i+1) (fst $ up 1 y) eet
                _ -> Nothing

        EAssign i b te -> case te of
            ELabelEnd te'     -> refocus' (ELabelEnd $ EAssign i b te') eet
            EBind2_ si h x te' | i > 0, Just b' <- down 0 b
                              -> refocus' (EBind2_ si h (subst (i-1) (fst b') x) (EAssign (i-1) b' te')) eet
            ELet2 le (x, xt) te' | i > 0, Just b' <- down 0 b
                              -> refocus' (ELet2 le (subst (i-1) (fst b') x, subst (i-1) (fst b') xt) (EAssign (i-1) b' te')) eet
            ELet1 le te' x    -> refocus' (ELet1 le (EAssign i b te') $ subst (i+1) (up 1 b) x) eet
            EBind1 si h te' x -> refocus' (EBind1 si h (EAssign i b te') $ subst (i+1) (up 1 b) x) eet
            CheckAppType si h t te' x -> refocus' (CheckAppType si h (subst i (fst b) t) (EAssign i b te') $ subst i b x) eet
            EApp1 si h te' x  -> refocus' (EApp1 si h (EAssign i b te') $ subst i b x) eet
            EApp2 si h x te'  -> refocus' (EApp2 si h (subst i (fst b) x) $ EAssign i b te') eet
            CheckType_ si t te'   -> refocus' (CheckType_ si (subst i (fst b) t) $ EAssign i b te') eet
            EAssign j a te' | i < j
                              -> refocus' (EAssign (j-1) (subst i (fst b) a) $ EAssign i (up1_ (j-1) b) te') eet
            t  | Just te' <- pull1 i b te -> refocus' te' eet
               | otherwise -> swapAssign (\i x -> focus2 te . Assign i x) (\i x -> refocus' $ EAssign i x te) i b eet
            -- todo: CheckSame Exp Env
          where
            refocus' = fix refocus_

            pull1 i b = \case
                EBind2_ si h x te | i > 0, Just b' <- down 0 b
                    -> EBind2_ si h (subst (i-1) (fst b') x) <$> pull1 (i-1) b' te
                EAssign j a te
                    | i < j  -> EAssign (j-1) (subst i (fst b) a) <$> pull1 i (up1_ (j-1) b) te
                    | j <= i -> EAssign j (subst i (fst b) a) <$> pull1 (i+1) (up1_ j b) te
                te  -> pull i te

            pull i = \case
                EBind2 BMeta _ te | i == 0 -> Just te
                EBind2_ si h x te | i > 0 -> EBind2_ si h <$> down (i-1) x <*> pull (i-1) te
                EAssign j a te  -> EAssign (if j <= i then j else j-1) <$> down i a <*> pull (if j <= i then i+1 else i) te
                _               -> Nothing

        EGlobal{} -> return eet
        _ -> case eet of
            MEnd x -> throwError' $ ErrorMsg $ "focus todo: " ++ ppShow x
            _ -> throwError' $ ErrorMsg $ "focus checkMetas: " ++ ppShow env ++ "\n" ++ ppShow (fst <$> eet)
      where
        refocus_ :: (Env -> CEnv ExpType -> IM m ExpType') -> Env -> CEnv ExpType -> IM m ExpType'
        refocus_ _ e (MEnd at) = focus_ e at
        refocus_ f e (Meta x at) = f (EBind2 BMeta x e) at
        refocus_ _ e (Assign i x at) = focus2 (EAssign i x e) at

        replaceMetas' = replaceMetas $ lamPi Hidden

lamPi h = (***) <$> const Lam <*> Pi h

replaceMetas bind = \case
    Meta a t -> bind a $ replaceMetas bind t
    Assign i x t | x' <- up1_ i x -> bind (cstr (snd x') (Var i) $ fst x') . up 1 . up1_ i $ replaceMetas bind t
    MEnd t ->  t


isCstr CstrT{} = True
isCstr (UFunN s [_]) = s `elem` [FEq, FOrd, FNum, FSigned, FComponent, FIntegral, FFloating]       -- todo: use Constraint type to decide this
isCstr _ = {- trace_ (ppShow c ++ show c) $ -} False

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
        (Lam_ md b, Pi h a bt) -> Lam_ md $ recheck_ "9" (EBind2 (BLam h) a te) (b, bt)
        (Pi_ md h a b, TType) -> Pi_ md h (checkType te a) $ checkType (EBind2 (BPi h) a te) b
        (ELit l, zt) -> ELit l  -- todo: check literal type
        (TType, TType) -> TType
        (Neut (App__ md a b), zt)
            | (Neut a', at) <- recheck'' "app1" te (Neut a, neutType te a)
            -> checkApps "a" [] zt (Neut . App__ md a' . head) te at [b]
        (Con_ md s n as, zt)      -> checkApps (show s) [] zt (Con_ md s n . drop (conParams s)) te (conType zt s) $ mkConPars n zt ++ as
        (TyCon_ md s as, zt)      -> checkApps (show s) [] zt (TyCon_ md s) te (nType s) as
        (CaseFun s@(CaseFunName _ t pars) as n, zt) -> checkApps (show s) [] zt (\xs -> evalCaseFun s (init $ drop pars xs) (last xs)) te (nType s) (makeCaseFunPars te n ++ as ++ [Neut n])
        (TyCaseFun s [m, t, f] n, zt)  -> checkApps (show s) [] zt (\[m, t, n, f] -> evalTyCaseFun s [m, t, f] n) te (nType s) [m, t, Neut n, f]
        (Neut (Fun_ md f vs@[] i a x), zt) -> checkApps "lab" [] zt (\xs -> Neut $ Fun_ md f vs i (reverse xs) x) te (nType f) $ reverse a   -- TODO: recheck x
        -- TODO
        (r@(Neut (Fun' f vs i a x)), zt) -> r
        (LabelEnd x, zt) -> LabelEnd $ recheck_ msg te (x, zt)
        (Neut d@Delta{}, zt) -> Neut d
      where
        checkApps s acc zt f _ t []
            | t == zt = f $ reverse acc
            | otherwise = 
                     error_ $ "checkApps' " ++ s ++ " " ++ msg ++ "\n" ++ showEnvExp te{-todo-} (t, TType) ++ "\n\n" ++ showEnvExp te (zt, TType)
        checkApps s acc zt f te t@(unfixlabel -> Pi h x y) (b_: xs) = checkApps (s++"+") (b: acc) zt f te (appTy t b) xs where b = recheck_ "checkApps" te (b_, x)
        checkApps s acc zt f te t _ =
             error_ $ "checkApps " ++ s ++ " " ++ msg ++ "\n" ++ showEnvExp te{-todo-} (t, TType) ++ "\n\n" ++ showEnvExp e (x, xt)

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

initEnv :: GlobalEnv
initEnv = Map.fromList
    [ (,) "'Type" (TType, TType, debugSI "source-of-Type")
    ]

-------------------------------------------------------------------------------- infos

data Info
    = Info Range String
    | IType String String
    | ITrace String String
    | IError ErrorMsg

instance NFData Info
 where
    rnf = \case
        Info r s -> rnf (r, s)
        IType a b -> rnf (a, b)
        ITrace i s -> rnf (i, s)
        IError x -> rnf x

instance Show Info where
    show = \case
        Info r s -> ppShow r ++ "  " ++ s
        IType a b -> a ++ " :: " ++ correctEscs b
        ITrace i s -> i ++ ":  " ++ correctEscs s
        IError e -> "!" ++ show e

errorRange is = [r | IError e <- is, RangeSI r <- errorRange_ e ]

type Infos = [Info]

throwError' e = tell [IError e] >> throwError e

mkInfoItem (RangeSI r) i = [Info r i]
mkInfoItem _ _ = mempty

listAllInfos m = h "trace"  (listTraceInfos m)
             ++  h "tooltips" [ ppShow r ++ "  " ++ intercalate " | " is | (r, is) <- listTypeInfos m ]
  where
    h x [] = []
    h x xs = ("------------ " ++ x) : xs

listTraceInfos m = [show i | i <- m, case i of Info{} -> False; _ -> True]
listTypeInfos m = map (second Set.toList) $ Map.toList $ Map.unionsWith (<>) [Map.singleton r $ Set.singleton i | Info r i <- m]

-------------------------------------------------------------------------------- inference for statements

inference :: MonadFix m => [Stmt] -> IM m [GlobalEnv]
inference [] = return []
inference (x:xs) = do
    y <- handleStmt x
    (y:) <$> withEnv y (inference xs)

handleStmt :: MonadFix m => Stmt -> IM m GlobalEnv
handleStmt = \case
  Primitive n t_ -> do
        t <- inferType . trSExp' =<< ($ t_) <$> addF
        tellType (fst n) t
        addToEnv n $ flip (,) t $ lamify t $ Neut . DFun_ (FunName (cFName n) Nothing t)
  Let n mt t_ -> do
        af <- addF
        let t__ = maybe id (flip SAnn . af) mt t_
        (x, t) <- inferTerm (snd n) $ trSExp' $ if usedS n t__ then SBuiltin "primFix" `SAppV` SLamV (substSG0 n t__) else t__
        tellType (fst n) t
        addToEnv n (mkELet n x t, t)
{-        -- hack
        when (snd (getParams t) == TType) $ do
            let ps' = fst $ getParams t
                t'' =   (TType :~> TType)
                  :~> addParams ps' (Var (length ps') `app_` DFun (FunName (snd n) t) (downTo 0 $ length ps'))
                  :~>  TType
                  :~> Var 2 `app_` Var 0
                  :~> Var 3 `app_` Var 1
            addToEnv (fst n, MatchName (snd n)) (lamify t'' $ \[m, tr, n', f] -> evalTyCaseFun (TyCaseFunName (snd n) t) [m, tr, f] n', t'')
-}
  PrecDef{} -> return mempty
  Data s (map (second trSExp') -> ps) (trSExp' -> t_@(UncurryS tl_ _)) addfa cs -> do
    af <- if addfa then asks $ \(exs, ge) -> addForalls exs . (snd s:) . defined' $ ge else return id
    vty <- inferType $ UncurryS ps t_
    tellType (fst s) vty
    let
        sint = cFName s
        pnum' = length $ filter ((== Visible) . fst) ps
        inum = arity vty - length ps

        mkConstr j (cn, trSExp' . af -> ct@(UncurryS ctl (AppsS c (map snd -> xs))))
            | c == SGlobal s && take pnum' xs == downToS "a3" (length ctl) pnum'
            = do
                cty <- removeHiddenUnit <$> inferType (UncurryS [(Hidden, x) | (Visible, x) <- ps] ct)
                tellType (fst cn) cty
                let     pars = zipWith (\x -> second $ STyped . flip (,) TType . up_ (1+j) x) [0..] $ drop (length ps) $ fst $ getParams cty
                        act = length . fst . getParams $ cty
                        acts = map fst . fst . getParams $ cty
                        conn = ConName (cFName cn) j cty
                e <- addToEnv cn (Con conn 0 [], cty)
                return (e, ((conn, cty)
                       , UncurryS pars
                       $ foldl SAppV (SVar (debugSI "22", ".cs") $ j + length pars) $ drop pnum' xs ++ [AppsS (SGlobal cn) (zip acts $ downToS ("a4 " ++ snd cn ++ " " ++ show (length ps)) (j+1+length pars) (length ps) ++ downToS "a5" 0 (act- length ps))]
                       ))
            | otherwise = throwError' $ ErrorMsg "illegal data definition (parameters are not uniform)" -- ++ show (c, cn, take pnum' xs, act)

        motive = UncurryS (replicate inum (Visible, Wildcard SType)) $
           SPi Visible (AppsS (SGlobal s) $ zip (map fst ps) (downToS "a6" inum $ length ps) ++ zip (map fst tl_) (downToS "a7" 0 inum)) SType

    (e1, es, tcn, cfn@(CaseFunName _ ct _), _, _) <- mfix $ \ ~(_, _, _, _, ct', cons') -> do
        let cfn = CaseFunName sint ct' $ length ps
        let tcn = TyConName sint inum vty (map fst cons') cfn
        e1 <- addToEnv s (TyCon tcn [], vty)
        (unzip -> (mconcat -> es, cons)) <- withEnv e1 $ zipWithM mkConstr [0..] cs
        ct <- withEnv (e1 <> es) $ inferType
            ( (\x -> traceD ("type of case-elim before elaboration: " ++ ppShow x) x) $ UncurryS
                ( [(Hidden, x) | (_, x) <- ps]
                ++ (Visible, motive)
                : map ((,) Visible . snd) cons
                ++ replicate inum (Hidden, Wildcard SType)
                ++ [(Visible, AppsS (SGlobal s) $ zip (map fst ps) (downToS "a8" (inum + length cs + 1) $ length ps) ++ zip (map fst tl_) (downToS "a9" 0 inum))]
                )
            $ foldl SAppV (SVar (debugSI "23", ".ct") $ length cs + inum + 1) $ downToS "a10" 1 inum ++ [SVar (debugSI "24", ".24") 0]
            )
        return (e1, es, tcn, cfn, ct, cons)

    e2 <- addToEnv (fst s, caseName (snd s)) (lamify ct $ \xs -> evalCaseFun cfn (init $ drop (length ps) xs) (last xs), ct)
    let ps' = fst $ getParams vty
        t =   (TType :~> TType)
          :~> addParams ps' (Var (length ps') `app_` TyCon tcn (downTo 0 $ length ps'))
          :~>  TType
          :~> Var 2 `app_` Var 0
          :~> Var 3 `app_` Var 1
    e3 <- addToEnv (fst s, MatchName (snd s)) (lamify t $ \[m, tr, n, f] -> evalTyCaseFun (TyCaseFunName sint t) [m, tr, f] n, t)
    return (e1 <> e2 <> e3 <> es)

  stmt -> error $ "handleStmt: " ++ show stmt

withEnv e = local $ second (<> e)

mkELet n x xt = {-(if null vs then id else trace_ $ "mkELet " ++ show (length vs) ++ " " ++ show n)-} term
  where
    vs = [Var i | i <- Set.toList $ free x <> free xt]
    fn = FunName (cFName n) (Just x) xt

    term = pmLabel fn vs 0 [] $ getFix x 0

    getFix (Lam z) i = Lam $ getFix z (i+1)
    getFix (TFun FprimFix _ [t, Lam f]) i = (if null vs then id else trace_ "!local rec") $ subst 0 (foldl app_ term (downTo 0 i)) f
    getFix x _ = x


removeHiddenUnit (Pi Hidden Unit (down 0 -> Just t)) = removeHiddenUnit t
removeHiddenUnit (Pi h a b) = Pi h a $ removeHiddenUnit b
removeHiddenUnit t = t

addParams ps t = foldr (uncurry Pi) t ps

addLams ps t = foldr (const Lam) t ps

lamify t x = addLams (fst $ getParams t) $ x $ downTo 0 $ arity t

{-
getApps' = second reverse . run where
  run (App a b) = second (b:) $ run a
  run x = (x, [])
-}
arity :: Exp -> Int
arity = length . fst . getParams

getParams :: Exp -> ([(Visibility, Exp)], Exp)
getParams (Pi h a b) = first ((h, a):) $ getParams b
getParams x = ([], x)

getLams (Lam b) = getLams b
getLams x = x

inferTerm :: Monad m => String -> SExp2 -> IM m ExpType
inferTerm msg t =
    fmap ((closedExp *** closedExp) . recheck msg EGlobal . replaceMetas (lamPi Hidden)) $ inferN EGlobal t
inferType :: Monad m => SExp2 -> IM m Type
inferType t = fmap (closedExp . fst . recheck "inferType" EGlobal . flip (,) TType . replaceMetas (Pi Hidden) . fmap fst) $ inferN (CheckType_ (debugSI "inferType CheckType_") TType EGlobal) t

addToEnv :: Monad m => SIName -> ExpType -> IM m GlobalEnv
addToEnv (si, s) (x, t) = do
--    maybe (pure ()) throwError_ $ ambiguityCheck s t      -- TODO
--    b <- asks $ (TraceTypeCheck `elem`) . fst
    tell [IType s $ ppShow t]
    v <- asks $ Map.lookup s . snd
    case v of
      Nothing -> return $ Map.singleton s (closedExp x, closedExp t, si)
      Just (_, _, si') -> throwError' $ ERedefined s si si'
{-
joinEnv :: Monad m => GlobalEnv -> GlobalEnv -> IM m GlobalEnv
joinEnv e1 e2 = do
-}

downTo n m = map Var [n+m-1, n+m-2..n]

defined' = Map.keys

-- todo: proper handling of implicit foralls
addF = asks $ \(exs, ge) -> addForalls exs $ defined' ge

tellType si t = tell $ mkInfoItem (sourceInfo si) $ removeEscs $ showDoc $ mkDoc False True (t, TType)


-------------------------------------------------------------------------------- pretty print
-- todo: do this via conversion to SExp

instance PShow Exp where
    pShowPrec _ = showDoc_ . mkDoc False False

instance PShow (CEnv Exp) where
    pShowPrec _ = showDoc_ . mkDoc False False

instance PShow Env where
    pShowPrec _ e = showDoc_ $ envDoc e $ pure $ shAtom $ underlined "<<HERE>>"

showEnvExp :: Env -> ExpType -> String
showEnvExp e c = showDoc $ envDoc e $ epar <$> mkDoc False False c

showEnvSExp :: Up a => Env -> SExp' a -> String
showEnvSExp e c = showDoc $ envDoc e $ epar <$> sExpDoc c

showEnvSExpType :: Up a => Env -> SExp' a -> Exp -> String
showEnvSExpType e c t = showDoc $ envDoc e $ epar <$> (shAnn "::" False <$> sExpDoc c <**> mkDoc False False (t, TType))
  where
    infixl 4 <**>
    (<**>) :: NameDB (a -> b) -> NameDB a -> NameDB b
    a <**> b = get >>= \s -> lift $ evalStateT a s <*> evalStateT b s

{-
expToSExp :: Exp -> SExp
expToSExp = \case
    Fun x _     -> expToSExp x
--    Var k           -> shAtom <$> shVar k
    App a b         -> SApp Visible{-todo-} (expToSExp a) (expToSExp b)
{-
    Lam h a b       -> join $ shLam (usedVar 0 b) (BLam h) <$> f a <*> pure (f b)
    Bind h a b      -> join $ shLam (usedVar 0 b) h <$> f a <*> pure (f b)
    Cstr a b        -> shCstr <$> f a <*> f b
    MT s xs       -> foldl (shApp Visible) (shAtom s) <$> mapM f xs
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
    STyped_ (e, _)  -> nameSExp $ expToSExp e  -- todo: mark boundary
    SVar i          -> SGlobal <$> shVar i
-}
envDoc :: Env -> Doc -> Doc
envDoc x m = case x of
    EGlobal{}           -> m
    EBind1 _ h ts b     -> envDoc ts $ join $ shLam (usedVar 0 b) h <$> m <*> pure (sExpDoc b)
    EBind2 h a ts       -> envDoc ts $ join $ shLam True h <$> mkDoc False ts' (a, TType) <*> pure m
    EApp1 _ h ts b      -> envDoc ts $ shApp h <$> m <*> sExpDoc b
    EApp2 _ h (Lam (Var 0), Pi Visible TType _) ts -> envDoc ts $ shApp h (shAtom "tyType") <$> m
    EApp2 _ h a ts      -> envDoc ts $ shApp h <$> mkDoc False ts' a <*> m
    ELet1 _ ts b        -> envDoc ts $ shLet_ m (sExpDoc b)
    ELet2 _ x ts        -> envDoc ts $ shLet_ (mkDoc False ts' x) m
    EAssign i x ts      -> envDoc ts $ shLet i (mkDoc False ts' x) m
    CheckType t ts      -> envDoc ts $ shAnn ":" False <$> m <*> mkDoc False ts' (t, TType)
    CheckIType t ts     -> envDoc ts $ shAnn ":" False <$> m <*> pure (shAtom "??") -- mkDoc ts' t
--    CheckSame t ts      -> envDoc ts $ shCstr <$> m <*> mkDoc ts' t
    CheckAppType si h t te b -> envDoc (EApp1 si h (CheckType_ (sourceInfo b) t te) b) m
    ELabelEnd ts        -> envDoc ts $ shApp Visible (shAtom "labEnd") <$> m
    x   -> error $ "envDoc: " ++ show x
  where
    ts' = False

class MkDoc a where
    mkDoc :: Bool {-print reduced-} -> Bool -> a -> Doc

instance MkDoc ExpType where
    mkDoc pr ts e = mkDoc pr ts $ fst e

instance MkDoc Exp where
    mkDoc pr ts e = fmap inGreen <$> f e
      where
        f = \case
--            Lam h a b       -> join $ shLam (usedVar 0 b) (BLam h) <$> f a <*> pure (f b)
            Lam b           -> join $ shLam True (BLam Visible) <$> f TType{-todo!-} <*> pure (f b)
            Pi h a b        -> join $ shLam (usedVar 0 b) (BPi h) <$> f a <*> pure (f b)
            ENat' n         -> pure $ shAtom $ show n
            (getTTup -> Just xs) -> shTuple <$> mapM f xs
            (getTup -> Just xs) -> shTuple <$> mapM f xs
            Con s _ xs      -> foldl (shApp Visible) (shAtom_ $ show s) <$> mapM f xs
            TyConN s xs     -> foldl (shApp Visible) (shAtom_ $ show s) <$> mapM f xs
            TType           -> pure $ shAtom "Type"
            ELit l          -> pure $ shAtom $ show l
            Neut x          -> mkDoc pr ts x

        shAtom_ = shAtom . if ts then switchTick else id

instance MkDoc Neutral where
    mkDoc pr ts e = fmap inGreen <$> f e
      where
        g = mkDoc pr ts
        f = \case
            CstrT' t a b     -> shCstr <$> g (a, t) <*> g (b, t)
            FL' a | pr -> g a
            Fun' s vs i (mkExpTypes (nType s) . reverse -> xs) _ -> foldl (shApp Visible) (shAtom_ $ show s) <$> mapM g xs
            Var_ k           -> shAtom <$> shVar k
            App_ a b         -> shApp Visible <$> g a <*> g b
            CaseFun_ s xs n  -> foldl (shApp Visible) (shAtom_ $ show s) <$> mapM g ({-mkExpTypes (nType s) $ makeCaseFunPars te n ++ -} xs ++ [Neut n])
            TyCaseFun_ s [m, t, f] n  -> foldl (shApp Visible) (shAtom_ $ show s) <$> mapM g (mkExpTypes (nType s) [m, t, Neut n, f])
            TyCaseFun_ s _ n  -> error $ "mkDoc TyCaseFun"
            LabelEnd_ x      -> shApp Visible (shAtom $ "labend") <$> g x
            Delta{} -> return $ shAtom "^delta"

        shAtom_ = shAtom . if ts then switchTick else id

instance MkDoc (CEnv Exp) where
    mkDoc pr ts e = fmap inGreen <$> f e
      where
        f :: CEnv Exp -> Doc
        f = \case
            MEnd a          -> mkDoc pr ts a
            Meta a b        -> join $ shLam True BMeta <$> mkDoc pr ts a <*> pure (f b)
            Assign i (x, _) e -> shLet i (mkDoc pr ts x) (f e)

getTup (unfixlabel -> ConN FHCons [_, _, x, xs]) = (x:) <$> getTup xs
getTup (unfixlabel -> ConN FHNil []) = Just []
getTup _ = Nothing

getTTup (unfixlabel -> TyConN FHList [xs]) = getList xs
getTTup _ = Nothing

getList (unfixlabel -> ConN FCons [x, xs]) = (x:) <$> getList xs
getList (unfixlabel -> ConN FNil []) = Just []
getList _ = Nothing

-------------------------------------------------------------------------------- tools

mfix' f = ExceptT (mfix (runExceptT . f . either bomb id))
  where bomb e = error $ "mfix (ExceptT): inner computation returned Left value:\n" ++ show e

foldlrev f = foldr (flip f)

