{-# LANGUAGE OverloadedStrings #-}
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
module LambdaCube.Compiler.Core where

import Data.Monoid
import Data.Maybe
import qualified Data.Set as Set
import Control.Arrow hiding ((<+>))

import LambdaCube.Compiler.Utils
import LambdaCube.Compiler.DeBruijn
import LambdaCube.Compiler.Pretty hiding (braces, parens)
import LambdaCube.Compiler.DesugaredSource hiding (getList)

-------------------------------------------------------------------------------- De-Bruijn limit

newtype MaxDB = MaxDB {getMaxDB :: Int} -- True: closed

instance Monoid MaxDB where
    mempty = MaxDB 0
    MaxDB a  `mappend` MaxDB a'  = MaxDB $ max a a'
      where
        max 0 x = x
        max _ _ = 1 --

--instance Show MaxDB where show _ = "MaxDB"

varDB i = MaxDB 1 --

lowerDB = id --

cmpDB _ (maxDB_ -> MaxDB x) = x == 0

upDB _ (MaxDB 0) = MaxDB 0
upDB x (MaxDB i) = MaxDB $ x + i

--upDB_ _ _ (MaxDB 0) = MaxDB 0
upDB_ g l (MaxDB i) | i - 1 < l = MaxDB i
upDB_ g l (MaxDB i) = MaxDB $ g (i-1-l) + 1 + l

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


-------------------------------------------------------------------------------- names

data FName
    = CFName !Int (SData SIName)
    | FEqCT | FT2 | Fcoe | FparEval | Ft2C | FprimFix
    | FType | FUnit | FInt | FWord | FNat | FBool | FFloat | FString | FChar | FOrdering | FVecS | FEmpty | FHList | FOutput
    | FHCons | FHNil | FZero | FSucc | FFalse | FTrue | FLT | FGT | FEQ | FTT | FNil | FCons
    | FSplit | FVecScalar
    -- todo: elim
    | FEq | FOrd | FNum | FSigned | FComponent | FIntegral | FFloating
    deriving (Eq, Ord)

mkFName :: SIName -> FName
mkFName sn@(SIName (RangeSI (Range fn p _)) s) = fromMaybe (CFName (hashPos fn p) $ SData sn) $ lookup s fntable
mkFName (SIName _ s) = error $ "mkFName: " ++ show s

fntable :: [(String, FName)]
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
    , (,) ":"  FCons
    , (,) "'Split"  FSplit
    ]

instance Show FName where
  show (CFName _ (SData s)) = sName s
  show s = maybe (error "show") id $ lookup s $ map (\(a, b) -> (b, a)) fntable
instance PShow FName where
  pShow (CFName _ (SData s)) = text (sName s) --shortForm (pShow s)
  pShow s = maybe (error "show") text $ lookup s $ map (\(a, b) -> (b, a)) fntable

-------------------------------------------------------------------------------- names with infos

data ConName       = ConName       FName Int{-ordinal number, e.g. Zero:0, Succ:1-} Type

data TyConName     = TyConName     FName Int{-num of indices-} Type [(ConName, Type)]{-constructors-} CaseFunName

data FunName       = FunName       FName (Maybe Exp) Type

data CaseFunName   = CaseFunName   FName Type Int{-num of parameters-}

data TyCaseFunName = TyCaseFunName FName Type

instance Show  ConName       where show  (ConName n _ _) = show n
instance PShow ConName       where pShow (ConName n _ _) = pShow n
instance Eq    ConName       where ConName _ n _ == ConName _ n' _ = n == n'
instance Show  TyConName     where show  (TyConName n _ _ _ _) = show n
instance PShow TyConName     where pShow (TyConName n _ _ _ _) = pShow n
instance Eq    TyConName     where TyConName n _ _ _ _ == TyConName n' _ _ _ _ = n == n'
instance Show  FunName       where show  (FunName n _ _) = show n
instance PShow FunName       where pShow (FunName n _ _) = pShow n
instance Eq    FunName       where FunName n _ _ == FunName n' _ _ = n == n'
instance Show  CaseFunName   where show  (CaseFunName n _ _) = CaseName $ show n
instance PShow CaseFunName   where pShow (CaseFunName n _ _) = text $ CaseName $ ppShow n
instance Eq    CaseFunName   where CaseFunName n _ _ == CaseFunName n' _ _ = n == n'
instance Show  TyCaseFunName where show  (TyCaseFunName n _) = MatchName $ show n
instance PShow TyCaseFunName where pShow (TyCaseFunName n _) = text $ MatchName $ ppShow n
instance Eq    TyCaseFunName where TyCaseFunName n _ == TyCaseFunName n' _ = n == n'

-------------------------------------------------------------------------------- core expression representation

data Freq = CompileTime | RunTime       -- TODO
  deriving (Eq)

data Exp
    = ELit_  Lit
    | TType_ Freq
    | Lam_   !MaxDB Exp
    | Con_   !MaxDB ConName !Int{-number of ereased arguments applied-} [Exp]
    | TyCon_ !MaxDB TyConName [Exp]
    | Pi_    !MaxDB Visibility Exp Exp
    | Neut   Neutral

data Neutral
    = Var_        !Int{-De Bruijn index-}
    | App__       !MaxDB Neutral Exp
    | CaseFun__   !MaxDB CaseFunName   [Exp] Neutral
    | TyCaseFun__ !MaxDB TyCaseFunName [Exp] Neutral
    | Fun_        !MaxDB FunName [Exp]{-local vars-} [Exp]{-given parameters, reversed-} Exp{-unfolded expression-}
    | RHS_ Exp                 -- not neut?
    | Delta (SData ([Exp] -> Exp))  -- not neut?

-------------------------------------------------------------------------------- auxiliary functions and patterns

type Type = Exp
type ExpType = (Exp, Type)
type SExp2 = SExp' ExpType

pattern TType = TType_ CompileTime

pattern ELit a <- (unfixlabel -> ELit_ a) where ELit = ELit_

infixl 2 `App`, `app_`
infixr 1 :~>

pattern NoLE <- (isNoRHS -> True)

isNoRHS (Neut (RHS_ _)) = False
isNoRHS _ = True

getLams' (Lam e) = first (+1) $ getLams' e
getLams' e = (0, e)

pattern Fun' f vs xs n <- Fun_ _ f vs xs n where Fun' f vs xs n = Fun_ (foldMap maxDB_ vs <> foldMap maxDB_ xs {- <> iterateN i lowerDB (maxDB_ n)-}) f vs xs n
pattern Fun f xs n = Fun' f [] xs n
pattern UTFun a t b <- (unfixlabel -> Neut (Fun (FunName a _ t) (reverse -> b) NoLE))
pattern UFunN a b <- UTFun a _ b
pattern DFun_ fn xs <- Fun fn (reverse -> xs) (Neut (Delta _)) where
    DFun_ fn@(FunName n _ _) xs = Fun fn (reverse xs) d where
        d = Neut $ Delta $ SData $ getFunDef n $ \xs -> Neut $ Fun fn (reverse xs) d
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

pattern Unit        <- TTyCon0 FUnit      where Unit        = tTyCon0 FUnit [Unit]
pattern TInt        <- TTyCon0 FInt       where TInt        = tTyCon0 FInt $ error "cs 1"
pattern TNat        <- TTyCon0 FNat       where TNat        = tTyCon0 FNat $ error "cs 3"
pattern TBool       <- TTyCon0 FBool      where TBool       = tTyCon0 FBool $ error "cs 4"
pattern TFloat      <- TTyCon0 FFloat     where TFloat      = tTyCon0 FFloat $ error "cs 5"
pattern TString     <- TTyCon0 FString    where TString     = tTyCon0 FString $ error "cs 6"
pattern TChar       <- TTyCon0 FChar      where TChar       = tTyCon0 FChar $ error "cs 7"
pattern TOrdering   <- TTyCon0 FOrdering  where TOrdering   = tTyCon0 FOrdering $ error "cs 8"
pattern TVec a b    <- TyConN FVecS [b, a]

pattern Empty s   <- TyCon (TyConName FEmpty _ _ _ _) [EString s] where
        Empty s    = TyCon (TyConName FEmpty (error "todo: inum2_") (TString :~> TType) (error "todo: tcn cons 3_") $ error "Empty") [EString s]

pattern TT          <- ConN' _ _ where TT = Closed (tCon FTT 0 Unit [])
pattern Zero        <- ConN FZero _ where Zero = Closed (tCon FZero 0 TNat [])
pattern Succ n      <- ConN FSucc (n:_) where Succ n = tCon FSucc 1 (TNat :~> TNat) [n]

pattern CstrT t a b     = Neut (CstrT' t a b)
pattern CstrT' t a b    = TFun' FEqCT (TType :~> Var 0 :~> Var 1 :~> TType) [t, a, b]
pattern Coe a b w x     = TFun Fcoe (TType :~> TType :~> CstrT TType (Var 1) (Var 0) :~> Var 2 :~> Var 2) [a,b,w,x]
pattern ParEval t a b   = TFun FparEval (TType :~> Var 0 :~> Var 1 :~> Var 2) [t, a, b]
pattern T2 a b          = TFun FT2 (TType :~> TType :~> TType) [a, b]
pattern CSplit a b c    <- UFunN FSplit [a, b, c]

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

pattern RHS x = Neut (RHS_ x)

--pmLabel' :: FunName -> [Exp] -> Int -> [Exp] -> Exp -> Exp
pmLabel' _ (FunName _ _ _) _ as (Neut (Delta (SData f))) = f $ reverse as
pmLabel' md f vs xs (unfixlabel -> y) = Neut $ Fun_ md f vs xs y

pmLabel :: FunName -> [Exp] -> [Exp] -> Exp -> Exp
pmLabel f vs xs e = pmLabel' (foldMap maxDB_ vs <> foldMap maxDB_ xs) f vs xs e

dropLams (unfixlabel -> Lam x) = dropLams x
dropLams (unfixlabel -> Neut x) = x

numLams (unfixlabel -> Lam x) = 1 + numLams x
numLams x = 0

pattern FL' y <- Fun' f _ xs (Neut (RHS_ y))
pattern FL y <- Neut (FL' y)

pattern Func n def ty xs <- (mkFunc -> Just (n, def, ty, xs))

mkFunc (Neut (Fun (FunName n (Just def) ty) xs (Neut RHS_{}))) | Just def' <- removeLams (length xs) def = Just (n, def', ty, xs)
mkFunc _ = Nothing

removeLams 0 (RHS x) = Just x
removeLams n (Lam x) | n > 0 = Lam <$> removeLams (n-1) x
removeLams _ _ = Nothing

pattern UFL y <- (unFunc -> Just y)

unFunc (Neut (Fun' (FunName _ (Just def) _) _ xs y)) = Just y
unFunc _ = Nothing

unFunc_ (Neut (Fun' _ _ xs y)) = Just y
unFunc_ _ = Nothing

unfixlabel (FL y) = unfixlabel y
unfixlabel a = a

-------------------------------------------------------------------------------- low-level toolbox

class Subst b a where
    subst_ :: Int -> MaxDB -> b -> a -> a

--subst :: Subst b a => Int -> MaxDB -> b -> a -> a
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
    TType_ f == TType_ f' = f == f'
    ELit l == ELit l' = l == l'
    Neut a == Neut a' = a == a'
    _ == _ = False

instance Eq Neutral where
    Fun' f vs a _ == Fun' f' vs' a' _ = (f, vs, a) == (f', vs', a')
    FL' a == a' = a == Neut a'
    a == FL' a' = Neut a == a'
    RHS_ a == RHS_ a' = a == a'
    CaseFun_ a b c == CaseFun_ a' b' c' = (a, b, c) == (a', b', c')
    TyCaseFun_ a b c == TyCaseFun_ a' b' c' = (a, b, c) == (a', b', c')
    App_ a b == App_ a' b' = (a, b) == (a', b')
    Var_ a == Var_ a' = a == a'
    _ == _ = False

free x | cmpDB 0 x = mempty
free x = foldVar (\i k -> Set.fromList [k - i | k >= i]) 0 x

instance Up Exp where
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
                Fun_ md fn vs xs v -> pmLabel' (md <> upDB i dx) fn (f i <$> vs) (f i <$> xs) $ f i v
                RHS_ a -> RHS $ f i a
                d@Delta{} -> Neut d
        f i e | cmpDB i e = e
        f i e = case e of
            Lam_ md b -> Lam_ (md <> upDB i dx) (f (i+1) b)
            Con_ md s n as  -> Con_ (md <> upDB i dx) s n $ f i <$> as
            Pi_ md h a b  -> Pi_ (md <> upDB i dx) h (f i a) (f (i+1) b)
            TyCon_ md s as -> TyCon_ (md <> upDB i dx) s $ f i <$> as

instance Rearrange Exp where
    rearrange i g = f i where
        f i e | cmpDB i e = e
        f i e = case e of
            Lam_ md b -> Lam_ (upDB_ g i md) (f (i+1) b)
            Pi_ md h a b -> Pi_ (upDB_ g i md) h (f i a) (f (i+1) b)
            Con_ md s pn as  -> Con_ (upDB_ g i md) s pn $ map (f i) as
            TyCon_ md s as -> TyCon_ (upDB_ g i md) s $ map (f i) as
            Neut x -> Neut $ rearrange i g x

instance Rearrange Neutral where
    rearrange i g = f i where
        f i e | cmpDB i e = e
        f i e = case e of
            Var_ k -> Var_ $ if k >= i then g (k-i) + i else k
            CaseFun__ md s as ne -> CaseFun__ (upDB_ g i md) s (rearrange i g <$> as) (rearrange i g ne)
            TyCaseFun__ md s as ne -> TyCaseFun__ (upDB_ g i md) s (rearrange i g <$> as) (rearrange i g ne)
            App__ md a b -> App__ (upDB_ g i md) (rearrange i g a) (rearrange i g b)
            Fun_ md fn vs x y -> Fun_ (upDB_ g i md) fn (rearrange i g <$> vs) (rearrange i g <$> x) $ rearrange i g y
            RHS_ x -> RHS_ $ rearrange i g x
            d@Delta{} -> d

instance Up Neutral where
    usedVar i e
        | cmpDB i e = False
        | otherwise = ((getAny .) . foldVar ((Any .) . (==))) i e

    foldVar f i = \case
        Var_ k -> f i k
        CaseFun_ _ as n -> foldMap (foldVar f i) as <> foldVar f i n
        TyCaseFun_ _ as n -> foldMap (foldVar f i) as <> foldVar f i n
        App_ a b -> foldVar f i a <> foldVar f i b
        Fun' _ vs x d -> foldMap (foldVar f i) vs <> foldMap (foldVar f i) x -- <> foldVar f i d
        RHS_ x -> foldVar f i x
        Delta{} -> mempty

instance HasMaxDB Neutral where
    maxDB_ = \case
        Var_ k -> varDB k
        CaseFun__ c _ _ _ -> c
        TyCaseFun__ c _ _ _ -> c
        App__ c a b -> c
        Fun_ c _ _ _ _ -> c
        RHS_ x -> maxDB_ x
        Delta{} -> mempty

instance (Subst x a, Subst x b) => Subst x (a, b) where
    subst_ i dx x (a, b) = (subst_ i dx x a, subst_ i dx x b)

varType' :: Int -> [Exp] -> Exp
varType' i vs = vs !! i

pattern Closed :: () => ClosedExp a => a -> a
pattern Closed a <- a where Closed a = closedExp a

-- TODO: remove?
class ClosedExp a where
    closedExp :: a -> a

instance (ClosedExp a, ClosedExp b) => ClosedExp (a, b) where
    closedExp (a, b) = (closedExp a, closedExp b)

instance ClosedExp Exp where
    closedExp = \case
        Lam_ _ c -> Lam_ mempty c
        Pi_ _ a b c -> Pi_ mempty a (closedExp b) c
        Con_ _ a b c -> Con_ mempty a b (closedExp <$> c)
        TyCon_ _ a b -> TyCon_ mempty a (closedExp <$> b)
        e@TType{} -> e
        e@ELit{} -> e
        Neut a -> Neut $ closedExp a

instance ClosedExp Neutral where
    closedExp = \case
        x@Var_{} -> error "impossible"
        CaseFun__ _ a as n -> CaseFun__ mempty a (closedExp <$> as) (closedExp n)
        TyCaseFun__ _ a as n -> TyCaseFun__ mempty a (closedExp <$> as) (closedExp n)
        App__ _ a b -> App__ mempty (closedExp a) (closedExp b)
        Fun_ _ f l x y -> Fun_ mempty f l (closedExp <$> x) y
        RHS_ a -> RHS_ (closedExp a)
        d@Delta{} -> d

-------------------------------------------------------------------------------- pretty print
-- todo: do this via conversion to SExp?

instance PShow Exp where
    pShow = mkDoc False


class MkDoc a where
    mkDoc :: Bool {-print reduced-} -> a -> Doc

instance MkDoc ExpType where
    mkDoc pr e = mkDoc pr $ fst e

instance MkDoc Exp where
    mkDoc pr e = green $ f e
      where
        f = \case
--            Lam h a b       -> join $ shLam (usedVar 0 b) (BLam h) <$> f a <*> pure (f b)
            Lam b           -> shLam True (BLam Visible) (f TType{-todo!-}) (f b)
            Pi h TType b    -> shLam_ (usedVar 0 b) (BPi h) Nothing (f b)
            Pi h a b        -> shLam (usedVar 0 b) (BPi h) (f a) (f b)
            ENat' n         -> text $ ppShow n
            (getTTup -> Just xs) -> shTuple $ f <$> xs
            (getTup -> Just xs)  -> shTuple $ f <$> xs
            Con s _ xs      -> foldl (shApp Visible) (pShow s) (f <$> xs)
            TyConN s xs     -> foldl (shApp Visible) (pShow s) (f <$> xs)
            TType           -> text "Type"
            ELit l          -> pShow l
            Neut x          -> mkDoc pr x

instance MkDoc Neutral where
    mkDoc pr e = green $ f e
      where
        g = mkDoc pr
        f = \case
            CstrT' t a b     -> shCstr (g (a, t)) (g (b, t))
            FL' a | pr -> g a
            Fun' s vs (mkExpTypes (nType s) . reverse -> xs) _ -> foldl (shApp Visible) (pShow s) (g <$> xs)
            Var_ k           -> shVar k
            App_ a b         -> shApp Visible (g a) (g b)
            CaseFun_ s xs n  -> foldl (shApp Visible) (pShow s) (map g $ {-mkExpTypes (nType s) $ makeCaseFunPars te n ++ -} xs ++ [Neut n])
            TyCaseFun_ s [m, t, f] n  -> foldl (shApp Visible) (pShow s) (g <$> mkExpTypes (nType s) [m, t, Neut n, f])
            TyCaseFun_ s _ n -> error $ "mkDoc TyCaseFun"
            RHS_ x      -> shApp Visible (text "labend") (g x)
            Delta{}          -> text "^delta"

getTup (unfixlabel -> ConN FHCons [_, _, x, xs]) = (x:) <$> getTup xs
getTup (unfixlabel -> ConN FHNil []) = Just []
getTup _ = Nothing

getTTup (unfixlabel -> TyConN FHList [xs]) = getList xs
getTTup _ = Nothing

getList (unfixlabel -> ConN FCons [x, xs]) = (x:) <$> getList xs
getList (unfixlabel -> ConN FNil []) = Just []
getList _ = Nothing

-------------------------------------------------------------------------------- reduction
evalCaseFun a ps (Con n@(ConName _ i _) _ vs)
    | i /= (-1) = foldl app_ (ps !!! (i + 1)) vs
    | otherwise = error "evcf"
  where
    xs !!! i | i >= length xs = error $ "!!! " ++ ppShow a ++ " " ++ show i ++ " " ++ ppShow n ++ "\n" ++ ppShow ps
    xs !!! i = xs !! i
evalCaseFun a b (FL c) = evalCaseFun a b c
evalCaseFun a b (Neut c) = CaseFun a b c
evalCaseFun a b x = error $ "evalCaseFun: " ++ ppShow (a, x)

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
        parEval _ (RHS x) _ = RHS x
        parEval _ _ (RHS x) = RHS x
        parEval t a b = ParEval t a b
  _ -> case show s of
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
    f_ ns typ (RHS a) (RHS a') = f ns typ a a'
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
    neutApp (Fun' f vs xs (Lam e)) a = pmLabel f vs (a: xs) (subst 0 a e)
    neutApp f a = Neut $ App_ f a


class NType a where nType :: a -> Type

instance NType FunName where nType (FunName _ _ t) = t
instance NType TyConName where nType (TyConName _ _ t _ _) = t
instance NType CaseFunName where nType (CaseFunName _ t _) = t
instance NType TyCaseFunName where nType (TyCaseFunName _ t) = t

conType (snd . getParams . unfixlabel -> TyCon (TyConName _ _ _ cs _) _) (ConName _ n t) = t --snd $ cs !! n

mkExpTypes t [] = []
mkExpTypes t@(Pi _ a _) (x: xs) = (x, t): mkExpTypes (appTy t x) xs

appTy (Pi _ a b) x = subst 0 x b
appTy t x = error $ "appTy: " ++ ppShow t

arity :: Exp -> Int
arity = length . fst . getParams

getParams :: Exp -> ([(Visibility, Exp)], Exp)
getParams (Pi h a b) = first ((h, a):) $ getParams b
getParams x = ([], x)

getLams (Lam b) = getLams b
getLams x = x

