{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
--{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}  -- TODO: remove
--{-# OPTIONS_GHC -fno-warn-unused-binds #-}  -- TODO: remove
module LambdaCube.Compiler.Core where

import Data.Monoid
import Data.Function
--import Data.Maybe
import qualified Data.Set as Set
import Control.Arrow hiding ((<+>))

--import LambdaCube.Compiler.Utils
import LambdaCube.Compiler.DeBruijn
import LambdaCube.Compiler.Pretty hiding (braces, parens)
import LambdaCube.Compiler.DesugaredSource

-------------------------------------------------------------------------------- De-Bruijn limit

newtype MaxDB = MaxDB {getMaxDB :: Int} -- True: closed

instance Monoid MaxDB where
    mempty = MaxDB 0
    MaxDB a  `mappend` MaxDB a'  = MaxDB $ max a a'
      where
        max 0 x = x
        max _ _ = 1 -- TODO

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

instance HasMaxDB ExpType where
    maxDB_ (ET a b) = maxDB_ a <> maxDB_ b


-------------------------------------------------------------------------------- names with infos

data ConName       = ConName       FName Int{-ordinal number, e.g. Zero:0, Succ:1-} Type

data TyConName     = TyConName     FName Int{-num of indices-} Type [(ConName, Type)]{-constructors-} CaseFunName

data FunName       = FunName       FName Int{-num of global vars-} FunDef Type

data CaseFunName   = CaseFunName   FName Type Int{-num of parameters-}

data TyCaseFunName = TyCaseFunName FName Type

data FunDef
    = DeltaDef ([Exp] -> Exp)
    | ExpDef Exp

class HasFName a where getFName :: a -> FName

instance HasFName ConName       where getFName (ConName n _ _) = n
instance HasFName TyConName     where getFName (TyConName n _ _ _ _) = n
instance HasFName FunName       where getFName (FunName n _ _ _) = n
instance HasFName CaseFunName   where getFName (CaseFunName n _ _) = n
instance HasFName TyCaseFunName where getFName (TyCaseFunName n _) = n

instance Eq ConName       where (==) = (==) `on` getFName
instance Eq TyConName     where (==) = (==) `on` getFName
instance Eq FunName       where (==) = (==) `on` getFName
instance Eq CaseFunName   where (==) = (==) `on` getFName
instance Eq TyCaseFunName where (==) = (==) `on` getFName

instance Show  ConName       where show  (ConName n _ _) = show n
instance PShow ConName       where pShow (ConName n _ _) = pShow n
instance Show  TyConName     where show  (TyConName n _ _ _ _) = show n
instance PShow TyConName     where pShow (TyConName n _ _ _ _) = pShow n
instance Show  FunName       where show  (FunName n _ _ _) = show n
instance PShow FunName       where pShow (FunName n _ _ _) = pShow n
instance Show  CaseFunName   where show  (CaseFunName n _ _) = CaseName $ show n
instance PShow CaseFunName   where pShow (CaseFunName n _ _) = text $ CaseName $ show n
instance Show  TyCaseFunName where show  (TyCaseFunName n _) = MatchName $ show n
instance PShow TyCaseFunName where pShow (TyCaseFunName n _) = text $ MatchName $ show n

-------------------------------------------------------------------------------- core expression representation

data Freq = CompileTime | RunTime       -- TODO
  deriving (Eq)

data Exp
    = ELit   Lit
    | TType_ Freq
    | Lam_   !MaxDB Exp
    | Con_   !MaxDB ConName !Int{-number of ereased arguments applied-} [Exp]
    | TyCon_ !MaxDB TyConName [Exp]
    | Pi_    !MaxDB Visibility Exp Exp
    | Neut   Neutral
    | Delta
    | RHS    Exp

data Neutral
    = Var_        !Int{-De Bruijn index-}
    | App__       !MaxDB Neutral Exp
    | CaseFun__   !MaxDB CaseFunName   [Exp] Neutral
    | TyCaseFun__ !MaxDB TyCaseFunName [Exp] Neutral
    | Fun_        !MaxDB FunName [Exp]{-given parameters, reversed-} Exp{-unfolded expression-}

-------------------------------------------------------------------------------- auxiliary functions and patterns

type Type = Exp

data ExpType = ET {expr :: Exp, ty :: Type}
    deriving (Eq)

instance Rearrange ExpType where
    rearrange l f (ET e t) = ET (rearrange l f e) (rearrange l f t)

instance PShow ExpType where pShow = mkDoc False

type SExp2 = SExp' ExpType

pattern TType = TType_ CompileTime

infixl 2 `App`, `app_`
infixr 1 :~>

pattern NoRHS <- (isRHS -> False)

isRHS RHS{} = True
isRHS _ = False

-- TODO: elim
pattern Reverse xs <- (reverse -> xs)
  where Reverse = reverse

pattern Fun f xs n          <- Fun_ _ f xs n
  where Fun f xs n          =  Fun_ (foldMap maxDB_ xs) f xs n
pattern CaseFun_ a b c      <- CaseFun__ _ a b c
  where CaseFun_ a b c      =  CaseFun__ (maxDB_ c <> foldMap maxDB_ b) a b c
pattern TyCaseFun_ a b c    <- TyCaseFun__ _ a b c
  where TyCaseFun_ a b c    =  TyCaseFun__ (foldMap maxDB_ b <> maxDB_ c) a b c
pattern App_ a b            <- App__ _ a b
  where App_ a b            =  App__ (maxDB_ a <> maxDB_ b) a b
pattern Con x n y           <- Con_ _ x n y
  where Con x n y           =  Con_ (foldMap maxDB_ y) x n y
pattern TyCon x y           <- TyCon_ _ x y
  where TyCon x y           =  TyCon_ (foldMap maxDB_ y) x y
pattern Lam y               <- Lam_ _ y
  where Lam y               =  Lam_ (lowerDB (maxDB_ y)) y
pattern Pi v x y            <- Pi_ _ v x y
  where Pi v x y            =  Pi_ (maxDB_ x <> lowerDB (maxDB_ y)) v x y

pattern CaseFun a b c   = Neut (CaseFun_ a b c)
pattern TyCaseFun a b c = Neut (TyCaseFun_ a b c)
pattern Var a           = Neut (Var_ a)
pattern App a b        <- Neut (App_ (Neut -> a) b)
pattern DFun a t b      = Neut (DFunN a t b)

-- unreducable function application
pattern UFun a b <- Neut (Fun (FunName a _ _ t) (reverse -> b) NoRHS)

-- saturated delta function application
pattern DFunN a t xs = Fun (FunName' a t) (Reverse xs) Delta

conParams (conTypeName -> TyConName _ _ _ _ (CaseFunName _ _ pars)) = pars
mkConPars n (snd . getParams . hnf -> TyCon (TyConName _ _ _ _ (CaseFunName _ _ pars)) xs) = take (min n pars) xs
--mkConPars 0 TType = []  -- ?
mkConPars n x@Neut{} = error $ "mkConPars!: " ++ ppShow x
mkConPars n x = error $ "mkConPars: " ++ ppShow (n, x)

pattern ConN s a   <- Con (ConName s _ _) _ a
tCon s i t a        = Con (ConName s i t) 0 a
tCon_ k s i t a     = Con (ConName s i t) k a
pattern TyConN s a <- TyCon (TyConName s _ _ _ _) a
pattern TTyCon s t a <- TyCon (TyConName s _ t _ _) a

pattern TTyCon0 s  <- TyCon (TyConName s _ _ _ _) []

tTyCon s t a cs = TyCon (TyConName s (error "todo: inum") t (map ((,) (error "tTyCon")) cs) $ CaseFunName (error "TTyCon-A") (error "TTyCon-B") $ length a) a
tTyCon0 s cs = Closed $ TyCon (TyConName s 0 TType (map ((,) (error "tTyCon0")) cs) $ CaseFunName (error "TTyCon0-A") (error "TTyCon0-B") 0) []

pattern a :~> b = Pi Visible a b

pattern TConstraint <- TTyCon0 FConstraint where TConstraint = tTyCon0 FConstraint $ error "cs 1"
pattern Unit        <- TTyCon0 FUnit      where Unit        = tTyCon0 FUnit [Unit]
pattern TInt        <- TTyCon0 FInt       where TInt        = tTyCon0 FInt $ error "cs 1"
pattern TNat        <- TTyCon0 FNat       where TNat        = tTyCon0 FNat $ error "cs 3"
pattern TBool       <- TTyCon0 FBool      where TBool       = tTyCon0 FBool $ error "cs 4"
pattern TFloat      <- TTyCon0 FFloat     where TFloat      = tTyCon0 FFloat $ error "cs 5"
pattern TString     <- TTyCon0 FString    where TString     = tTyCon0 FString $ error "cs 6"
pattern TChar       <- TTyCon0 FChar      where TChar       = tTyCon0 FChar $ error "cs 7"
pattern TOrdering   <- TTyCon0 FOrdering  where TOrdering   = tTyCon0 FOrdering $ error "cs 8"
pattern TVec a b    <- TyConN FVecS [b, a]

pattern Empty s    <- TyCon (TyConName FEmpty _ _ _ _) [HString{-hnf?-} s]
  where Empty s     = TyCon (TyConName FEmpty (error "todo: inum2_") (TString :~> TType) (error "todo: tcn cons 3_") $ error "Empty") [HString s]

pattern TT          <- ConN _ _
  where TT          =  Closed (tCon FTT 0 Unit [])

pattern CUnit       <- ConN FCUnit _
  where CUnit       =  tCon FCUnit 0 TConstraint []
pattern CEmpty s    <- ConN FCEmpty (HString s: _)
  where CEmpty s    =  tCon FCEmpty 1 (TString :~> TConstraint) [HString s]

pattern CstrT t a b     = Neut (CstrT' t a b)
pattern CstrT' t a b    = DFunN FEqCT (TType :~> Var 0 :~> Var 1 :~> TConstraint) [t, a, b]
pattern Coe a b w x     = DFun Fcoe (TType :~> TType :~> CW (CstrT TType (Var 1) (Var 0)) :~> Var 2 :~> Var 2) [a,b,w,x]
pattern ParEval t a b   = DFun FparEval (TType :~> Var 0 :~> Var 1 :~> Var 2) [t, a, b]
pattern T2 a b          = DFun FT2 (TConstraint :~> TConstraint :~> TConstraint) [a, b]
pattern CW a            = DFun FCW (TConstraint :~> TType) [a]
pattern CSplit a b c   <- UFun FSplit [a, b, c]

pattern HLit a <- (hnf -> ELit a)
  where HLit = ELit
pattern HInt a      = HLit (LInt a)
pattern HFloat a    = HLit (LFloat a)
pattern HChar a     = HLit (LChar a)
pattern HString a   = HLit (LString a)

pattern EBool a <- (getEBool -> Just a)
  where EBool = \case
            False -> Closed $ tCon FFalse 0 TBool []
            True  -> Closed $ tCon FTrue  1 TBool []

getEBool (hnf -> ConN FFalse _) = Just False
getEBool (hnf -> ConN FTrue _) = Just True
getEBool _ = Nothing

pattern ENat n <- (fromNatE -> Just n)
  where ENat 0         = Closed $ tCon FZero 0 TNat []
        ENat n | n > 0 = Closed $ tCon FSucc 1 (TNat :~> TNat) [ENat (n-1)]

fromNatE :: Exp -> Maybe Int
fromNatE (hnf -> ConN FZero _) = Just 0
fromNatE (hnf -> ConN FSucc (n:_)) = succ <$> fromNatE n
fromNatE _ = Nothing

mkOrdering x = Closed $ case x of
    LT -> tCon FLT 0 TOrdering []
    EQ -> tCon FEQ 1 TOrdering []
    GT -> tCon FGT 2 TOrdering []

conTypeName :: ConName -> TyConName
conTypeName (ConName _ _ t) = case snd $ getParams t of TyCon n _ -> n

mkFun_ _ (FunName _ _ ~(DeltaDef f) _) as Delta = f $ reverse as
mkFun_ md f xs (hnf -> y) = Neut $ Fun_ md f xs y

mkFun :: FunName -> [Exp] -> Exp -> Exp
mkFun f xs e = mkFun_ (foldMap maxDB_ xs) f xs e

pattern ReducedN y <- Fun f _ (RHS y)
pattern Reduced y <- Neut (ReducedN y)

hnf (Reduced y) = hnf y
hnf a = a

outputType = tTyCon0 FOutput $ error "cs 9"

-- TODO: remove
boolType = TBool
-- TODO: remove
trueExp = EBool True

-------------------------------------------------------------------------------- low-level toolbox

class Subst b a where
    subst_ :: Int -> MaxDB -> b -> a -> a

--subst :: Subst b a => Int -> MaxDB -> b -> a -> a
subst i x a = subst_ i (maxDB_ x) x a

instance Subst Exp ExpType where
    subst_ i dx x (ET a b) = ET (subst_ i dx x a) (subst_ i dx x b)

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
    Reduced a == a' = a == a'
    a == Reduced a' = a == a'
    Lam a == Lam a' = a == a'
    Pi a b c == Pi a' b' c' = (a, b, c) == (a', b', c')
    Con a n b == Con a' n' b' = (a, n, b) == (a', n', b')
    TyCon a b == TyCon a' b' = (a, b) == (a', b')
    TType_ f == TType_ f' = f == f'
    ELit l == ELit l' = l == l'
    Neut a == Neut a' = a == a'
    RHS a == RHS a' = a == a'
    _ == _ = False

instance Eq Neutral where
    Fun f a _ == Fun f' a' _ = (f, a) == (f', a')
    ReducedN a == a' = a == Neut a'
    a == ReducedN a' = Neut a == a'
    CaseFun_ a b c == CaseFun_ a' b' c' = (a, b, c) == (a', b', c')
    TyCaseFun_ a b c == TyCaseFun_ a' b' c' = (a, b, c) == (a', b', c')
    App_ a b == App_ a' b' = (a, b) == (a', b')
    Var_ a == Var_ a' = a == a'
    _ == _ = False

free x | cmpDB 0 x = mempty
free x = foldVar (\i k -> Set.fromList [k - i | k >= i]) 0 x

instance Subst Exp Exp where
    subst_ i0 dx x = f i0
      where
        f i (Neut n) = substNeut n
          where
            substNeut e | cmpDB i e = Neut e
            substNeut e = case e of
                Var_ k              -> case compare k i of GT -> Var $ k - 1; LT -> Var k; EQ -> up (i - i0) x
                CaseFun_ s as n     -> evalCaseFun s (f i <$> as) (substNeut n)
                TyCaseFun_ s as n   -> evalTyCaseFun s (f i <$> as) (substNeut n)
                App_ a b            -> app_ (substNeut a) (f i b)
                Fun_ md fn xs v     -> mkFun_ (md <> upDB i dx) fn (f i <$> xs) $ f i v
        f i e | cmpDB i e = e
        f i e = case e of
            Lam_ md b       -> Lam_ (md <> upDB i dx) (f (i+1) b)
            Con_ md s n as  -> Con_ (md <> upDB i dx) s n $ f i <$> as
            Pi_ md h a b    -> Pi_ (md <> upDB i dx) h (f i a) (f (i+1) b)
            TyCon_ md s as  -> TyCon_ (md <> upDB i dx) s $ f i <$> as
            Delta           -> Delta
            RHS a           -> RHS $ f i a

instance Rearrange Exp where
    rearrange i g = f i where
        f i e | cmpDB i e = e
        f i e = case e of
            Lam_ md b       -> Lam_ (upDB_ g i md) (f (i+1) b)
            Pi_ md h a b    -> Pi_ (upDB_ g i md) h (f i a) (f (i+1) b)
            Con_ md s pn as -> Con_ (upDB_ g i md) s pn $ map (f i) as
            TyCon_ md s as  -> TyCon_ (upDB_ g i md) s $ map (f i) as
            Neut x          -> Neut $ rearrange i g x
            Delta           -> Delta
            RHS x           -> RHS $ rearrange i g x

instance Rearrange Neutral where
    rearrange i g = f i where
        f i e | cmpDB i e = e
        f i e = case e of
            Var_ k -> Var_ $ if k >= i then g (k-i) + i else k
            CaseFun__ md s as ne -> CaseFun__ (upDB_ g i md) s (rearrange i g <$> as) (rearrange i g ne)
            TyCaseFun__ md s as ne -> TyCaseFun__ (upDB_ g i md) s (rearrange i g <$> as) (rearrange i g ne)
            App__ md a b -> App__ (upDB_ g i md) (rearrange i g a) (rearrange i g b)
            Fun_ md fn x y -> Fun_ (upDB_ g i md) fn (rearrange i g <$> x) $ rearrange i g y

instance Up Exp where
    usedVar i e
        | cmpDB i e = False
        | otherwise = ((getAny .) . foldVar ((Any .) . (==))) i e

    foldVar f i = \case
        Lam b -> foldVar f (i+1) b
        Pi _ a b -> foldVar f i a <> foldVar f (i+1) b
        Con _ _ as -> foldMap (foldVar f i) as
        TyCon _ as -> foldMap (foldVar f i) as
        TType_ _ -> mempty
        ELit{} -> mempty
        Neut x -> foldVar f i x
        Delta -> mempty
        RHS x -> foldVar f i x

instance Up Neutral where
    usedVar i e
        | cmpDB i e = False
        | otherwise = ((getAny .) . foldVar ((Any .) . (==))) i e

    foldVar f i = \case
        Var_ k -> f i k
        CaseFun_ _ as n -> foldMap (foldVar f i) as <> foldVar f i n
        TyCaseFun_ _ as n -> foldMap (foldVar f i) as <> foldVar f i n
        App_ a b -> foldVar f i a <> foldVar f i b
        Fun _ x d -> foldMap (foldVar f i) x -- <> foldVar f i d

instance Up ExpType where
    usedVar i (ET a b) = usedVar i a || usedVar i b
    foldVar f i (ET a b) = foldVar f i a <> foldVar f i b

instance HasMaxDB Exp where
    maxDB_ = \case
        Lam_ c _ -> c
        Pi_ c _ _ _ -> c
        Con_ c _ _ _ -> c
        TyCon_ c _ _ -> c

        TType_ _ -> mempty
        ELit{} -> mempty
        Neut x -> maxDB_ x
        Delta -> mempty
        RHS x -> maxDB_ x

instance HasMaxDB Neutral where
    maxDB_ = \case
        Var_ k -> varDB k
        CaseFun__ c _ _ _ -> c
        TyCaseFun__ c _ _ _ -> c
        App__ c a b -> c
        Fun_ c _ _ _ -> c

varType' :: Int -> [Exp] -> Exp
varType' i vs = vs !! i

pattern Closed :: () => ClosedExp a => a -> a
pattern Closed a <- a where Closed a = closedExp a

-- TODO: remove?
class ClosedExp a where
    closedExp :: a -> a

instance ClosedExp ExpType where
    closedExp (ET a b) = ET (closedExp a) (closedExp b)

instance ClosedExp Exp where
    closedExp = \case
        Lam_ _ c -> Lam_ mempty c
        Pi_ _ a b c -> Pi_ mempty a (closedExp b) c
        Con_ _ a b c -> Con_ mempty a b (closedExp <$> c)
        TyCon_ _ a b -> TyCon_ mempty a (closedExp <$> b)
        e@TType_{} -> e
        e@ELit{} -> e
        Neut a -> Neut $ closedExp a
        Delta -> Delta
        RHS a -> RHS (closedExp a)

instance ClosedExp Neutral where
    closedExp = \case
        x@Var_{} -> error "impossible"
        CaseFun__ _ a as n -> CaseFun__ mempty a (closedExp <$> as) (closedExp n)
        TyCaseFun__ _ a as n -> TyCaseFun__ mempty a (closedExp <$> as) (closedExp n)
        App__ _ a b -> App__ mempty (closedExp a) (closedExp b)
        Fun_ _ f x y -> Fun_ mempty f (closedExp <$> x) y

-------------------------------------------------------------------------------- pretty print
-- todo: do this via conversion to SExp?

instance PShow Exp where
    pShow = mkDoc False

class MkDoc a where
    mkDoc :: Bool {-print reduced-} -> a -> Doc

instance MkDoc ExpType where
    mkDoc pr (ET e TType) = mkDoc pr e
    mkDoc pr (ET e t) = DAnn (mkDoc pr e) (mkDoc pr t)

instance MkDoc Exp where
    mkDoc pr e = f e
      where
        f = \case
            Lam b           -> shLam_ (usedVar 0 b) (BLam Visible) Nothing (f b)
            Pi h TType b    -> shLam_ (usedVar 0 b) (BPi h) Nothing (f b)
            Pi h a b        -> shLam (usedVar 0 b) (BPi h) (f a) (f b)
            ENat n          -> pShow n
            ConN FHCons [_, _, x, xs] -> foldl DApp (text "HCons") (f <$> [x, xs])
            Con s _ xs      -> foldl DApp (pShow s) (f <$> xs)
            TyConN s xs     -> foldl DApp (pShow s) (f <$> xs)
            TType           -> text "Type"
            ELit l          -> pShow l
            Neut x          -> mkDoc pr x
            Delta           -> text "^delta"
            RHS x           -> text "_rhs" `DApp` f x

instance MkDoc Neutral where
    mkDoc pr e = f e
      where
        g = mkDoc pr
        f = \case
            CstrT' t a b        -> shCstr (g a) (g (ET b t))
            ReducedN a | pr     -> g a
            Fun s xs _         -> foldl DApp (pShow s) (g <$> reverse xs)
            Var_ k              -> shVar k
            App_ a b            -> f a `DApp` g b
            CaseFun_ s xs n     -> foldl DApp (pShow s) (map g $ xs ++ [Neut n])
            TyCaseFun_ s [m, t, f] n  -> foldl DApp (pShow s) (g <$> [m, t, Neut n, f])
            TyCaseFun_ s _ n -> error $ "mkDoc TyCaseFun"

-------------------------------------------------------------------------------- reduction

{- todo: generate
    DFun n@(FunName "natElim" _) [a, z, s, Succ x] -> let      -- todo: replace let with better abstraction
                sx = s `app_` x
            in sx `app_` eval (DFun n [a, z, s, x])
    MT "natElim" [_, z, s, Zero] -> z
    DFun na@(FunName "finElim" _) [m, z, s, n, ConN "FSucc" [i, x]] -> let six = s `app_` i `app_` x-- todo: replace let with better abstraction
        in six `app_` eval (DFun na [m, z, s, i, x])
    MT "finElim" [m, z, s, n, ConN "FZero" [i]] -> z `app_` i
-}

pattern FunName' a t <- FunName a _ _ t
  where FunName' a t = fn
          where
            fn = FunName a 0 (DeltaDef $ getFunDef a $ \xs -> Neut $ Fun fn (reverse xs) Delta) t

getFunDef s f = case show s of
    "'EqCT"             -> \case (t: a: b: _)   -> cstr t a b
    "'T2"               -> \case (a: b: _)      -> t2 a b
    "'CW"               -> \case (a: _)         -> cw a
    "t2C"               -> \case (a: b: _)      -> t2C a b
    "coe"               -> \case (a: b: t: d: _) -> evalCoe a b t d
    "parEval"           -> \case (t: a: b: _)   -> parEval t a b
      where
        parEval _ (RHS x) _ = RHS x
        parEval _ _ (RHS x) = RHS x
        parEval t a b       = ParEval t a b

    "unsafeCoerce"      -> \case xs@(_: _: x@NonNeut: _) -> x; xs -> f xs
    "reflCstr"          -> \case (a: _) -> TT
    "hlistNilCase"      -> \case (_: x: (hnf -> Con n@(ConName _ 0 _) _ _): _) -> x; xs -> f xs
    "hlistConsCase"     -> \case (_: _: _: x: (hnf -> Con n@(ConName _ 1 _) _ (_: _: a: b: _)): _) -> x `app_` a `app_` b; xs -> f xs

    -- general compiler primitives
    "primAddInt"        -> \case (HInt i: HInt j: _)    -> HInt (i + j); xs -> f xs
    "primSubInt"        -> \case (HInt i: HInt j: _)    -> HInt (i - j); xs -> f xs
    "primModInt"        -> \case (HInt i: HInt j: _)    -> HInt (i `mod` j); xs -> f xs
    "primSqrtFloat"     -> \case (HFloat i: _)          -> HFloat $ sqrt i; xs -> f xs
    "primRound"         -> \case (HFloat i: _)          -> HInt $ round i; xs -> f xs
    "primIntToFloat"    -> \case (HInt i: _)            -> HFloat $ fromIntegral i; xs -> f xs
    "primIntToNat"      -> \case (HInt i: _)            -> ENat $ fromIntegral i; xs -> f xs
    "primCompareInt"    -> \case (HInt x: HInt y: _)    -> mkOrdering $ x `compare` y; xs -> f xs
    "primCompareFloat"  -> \case (HFloat x: HFloat y: _) -> mkOrdering $ x `compare` y; xs -> f xs
    "primCompareChar"   -> \case (HChar x: HChar y: _)  -> mkOrdering $ x `compare` y; xs -> f xs
    "primCompareString" -> \case (HString x: HString y: _) -> mkOrdering $ x `compare` y; xs -> f xs

    -- LambdaCube 3D specific primitives
    "PrimGreaterThan"   -> \case (t: _: _: _: _: _: _: x: y: _) | Just r <- twoOpBool (>) t x y -> r; xs -> f xs
    "PrimGreaterThanEqual" -> \case (t: _: _: _: _: _: _: x: y: _) | Just r <- twoOpBool (>=) t x y -> r; xs -> f xs
    "PrimLessThan"      -> \case (t: _: _: _: _: _: _: x: y: _) | Just r <- twoOpBool (<) t x y -> r; xs -> f xs
    "PrimLessThanEqual" -> \case (t: _: _: _: _: _: _: x: y: _) | Just r <- twoOpBool (<=) t x y -> r; xs -> f xs
    "PrimEqualV"        -> \case (t: _: _: _: _: _: _: x: y: _) | Just r <- twoOpBool (==) t x y -> r; xs -> f xs
    "PrimNotEqualV"     -> \case (t: _: _: _: _: _: _: x: y: _) | Just r <- twoOpBool (/=) t x y -> r; xs -> f xs
    "PrimEqual"         -> \case (t: _: _: x: y: _) | Just r <- twoOpBool (==) t x y -> r; xs -> f xs
    "PrimNotEqual"      -> \case (t: _: _: x: y: _) | Just r <- twoOpBool (/=) t x y -> r; xs -> f xs
    "PrimSubS"          -> \case (_: _: _: _: x: y: _) | Just r <- twoOp (-) x y -> r; xs -> f xs
    "PrimSub"           -> \case (_: _: x: y: _) | Just r <- twoOp (-) x y -> r; xs -> f xs
    "PrimAddS"          -> \case (_: _: _: _: x: y: _) | Just r <- twoOp (+) x y -> r; xs -> f xs
    "PrimAdd"           -> \case (_: _: x: y: _) | Just r <- twoOp (+) x y -> r; xs -> f xs
    "PrimMulS"          -> \case (_: _: _: _: x: y: _) | Just r <- twoOp (*) x y -> r; xs -> f xs
    "PrimMul"           -> \case (_: _: x: y: _) | Just r <- twoOp (*) x y -> r; xs -> f xs
    "PrimDivS"          -> \case (_: _: _: _: _: x: y: _) | Just r <- twoOp_ (/) div x y -> r; xs -> f xs
    "PrimDiv"           -> \case (_: _: _: _: _: x: y: _) | Just r <- twoOp_ (/) div x y -> r; xs -> f xs
    "PrimModS"          -> \case (_: _: _: _: _: x: y: _) | Just r <- twoOp_ modF mod x y -> r; xs -> f xs
    "PrimMod"           -> \case (_: _: _: _: _: x: y: _) | Just r <- twoOp_ modF mod x y -> r; xs -> f xs
    "PrimNeg"           -> \case (_: x: _) | Just r <- oneOp negate x -> r; xs -> f xs
    "PrimAnd"           -> \case (EBool x: EBool y: _) -> EBool (x && y); xs -> f xs
    "PrimOr"            -> \case (EBool x: EBool y: _) -> EBool (x || y); xs -> f xs
    "PrimXor"           -> \case (EBool x: EBool y: _) -> EBool (x /= y); xs -> f xs
    "PrimNot"           -> \case ((hnf -> TNat): _: _: EBool x: _) -> EBool $ not x; xs -> f xs

    _ -> f
  where
    twoOpBool :: (forall a . Ord a => a -> a -> Bool) -> Exp -> Exp -> Exp -> Maybe Exp
    twoOpBool f t (HFloat x)  (HFloat y)  = Just $ EBool $ f x y
    twoOpBool f t (HInt x)    (HInt y)    = Just $ EBool $ f x y
    twoOpBool f t (HString x) (HString y) = Just $ EBool $ f x y
    twoOpBool f t (HChar x)   (HChar y)   = Just $ EBool $ f x y
    twoOpBool f t (ENat x)    (ENat y)    = Just $ EBool $ f x y
    twoOpBool _ _ _ _ = Nothing

    oneOp :: (forall a . Num a => a -> a) -> Exp -> Maybe Exp
    oneOp f = oneOp_ f f

    oneOp_ f _ (HFloat x) = Just $ HFloat $ f x
    oneOp_ _ f (HInt x) = Just $ HInt $ f x
    oneOp_ _ _ _ = Nothing

    twoOp :: (forall a . Num a => a -> a -> a) -> Exp -> Exp -> Maybe Exp
    twoOp f = twoOp_ f f

    twoOp_ f _ (HFloat x) (HFloat y) = Just $ HFloat $ f x y
    twoOp_ _ f (HInt x) (HInt y) = Just $ HInt $ f x y
    twoOp_ _ _ _ _ = Nothing

    modF x y = x - fromIntegral (floor (x / y)) * y

evalCaseFun a ps (Con n@(ConName _ i _) _ vs)
    | i /= (-1) = foldl app_ (ps !!! (i + 1)) vs
    | otherwise = error "evcf"
  where
    xs !!! i | i >= length xs = error $ "!!! " ++ ppShow a ++ " " ++ show i ++ " " ++ ppShow n ++ "\n" ++ ppShow ps
    xs !!! i = xs !! i
evalCaseFun a b (Reduced c) = evalCaseFun a b c
evalCaseFun a b (Neut c) = CaseFun a b c
evalCaseFun a b x = error $ "evalCaseFun: " ++ ppShow (a, x)

evalTyCaseFun a b (Reduced c) = evalTyCaseFun a b c
evalTyCaseFun a b (Neut c) = TyCaseFun a b c
evalTyCaseFun (TyCaseFunName FType ty) (_: t: f: _) TType = t
evalTyCaseFun (TyCaseFunName n ty) (_: t: f: _) (TyCon (TyConName n' _ _ _ _) vs) | n == n' = foldl app_ t vs
--evalTyCaseFun (TyCaseFunName n ty) [_, t, f] (DFun (FunName n' _) vs) | n == n' = foldl app_ t vs  -- hack
evalTyCaseFun (TyCaseFunName n ty) (_: t: f: _) _ = f

evalCoe a b (Reduced x) d = evalCoe a b x d
evalCoe a b TT d = d
evalCoe a b t d = Coe a b t d

cstr_ t a b = cw $ cstr t a b

cstr = f []
  where
    f z ty a a' = f_ z (hnf ty) (hnf a) (hnf a')

    f_ _ _ a a' | a == a' = CUnit
    f_ ns typ (RHS a) (RHS a') = f ns typ a a'
    f_ ns typ (Con a n xs) (Con a' n' xs') | a == a' && n == n' && length xs == length xs' = 
        ff ns (foldl appTy (conType typ a) $ mkConPars n typ) $ zip xs xs'
    f_ ns typ (TyCon a xs) (TyCon a' xs') | a == a' && length xs == length xs' = 
        ff ns (nType a) $ zip xs xs'
    f_ (_: ns) typ{-down?-} (down 0 -> Just a) (down 0 -> Just a') = f ns typ a a'
    f_ ns TType (Pi h a b) (Pi h' a' b') | h == h' = t2 (f ns TType a a') (f ((a, a'): ns) TType b b')

    f_ [] TType (UFun FVecScalar [a, b]) (UFun FVecScalar [a', b']) = t2 (f [] TNat a a') (f [] TType b b')
    f_ [] TType (UFun FVecScalar [a, b]) (TVec a' b') = t2 (f [] TNat a a') (f [] TType b b')
    f_ [] TType (UFun FVecScalar [a, b]) t@NonNeut = t2 (f [] TNat a (ENat 1)) (f [] TType b t)
    f_ [] TType (TVec a' b') (UFun FVecScalar [a, b]) = t2 (f [] TNat a' a) (f [] TType b' b)
    f_ [] TType t@NonNeut (UFun FVecScalar [a, b]) = t2 (f [] TNat a (ENat 1)) (f [] TType b t)

    f_ [] typ a@Neut{} a' = CstrT typ a a'
    f_ [] typ a a'@Neut{} = CstrT typ a a'
    f_ ns typ a a' = CEmpty $ simpleShow $ nest 2 ("can not unify" <$$> DTypeNamespace True (pShow a)) <$$> nest 2 ("with" <$$> DTypeNamespace True (pShow a'))

    ff _ _ [] = CUnit
    ff ns tt@(Pi v t _) ((t1, t2'): ts) = t2 (f ns t t1 t2') $ ff ns (appTy tt t1) ts
    ff ns t zs = error $ "ff: " -- ++ show (a, n, length xs', length $ mkConPars n typ) ++ "\n" ++ ppShow (nType a) ++ "\n" ++ ppShow (foldl appTy (nType a) $ mkConPars n typ) ++ "\n" ++ ppShow (zip xs xs') ++ "\n" ++ ppShow zs ++ "\n" ++ ppShow t

pattern NonNeut <- (nonNeut -> True)

nonNeut Reduced{} = True
nonNeut Neut{} = False
nonNeut _ = True

t2C (hnf -> TT) (hnf -> TT) = TT
t2C a b = DFun Ft2C (Unit :~> Unit :~> Unit) [a, b]

cw (hnf -> CUnit) = Unit
cw (hnf -> CEmpty a) = Empty a
cw a = CW a

t2 (hnf -> CUnit) a = a
t2 a (hnf -> CUnit) = a
t2 (hnf -> CEmpty a) (hnf -> CEmpty b) = CEmpty (a <> b)
t2 (hnf -> CEmpty s) _ = CEmpty s
t2 _ (hnf -> CEmpty s) = CEmpty s
t2 a b = T2 a b

app_ :: Exp -> Exp -> Exp
app_ (Lam x) a = subst 0 a x
app_ (Con s n xs) a = if n < conParams s then Con s (n+1) xs else Con s n (xs ++ [a])
app_ (TyCon s xs) a = TyCon s (xs ++ [a])
app_ (Neut f) a = neutApp f a
  where
    neutApp (ReducedN x) a = app_ x a    -- ???
    neutApp (Fun f xs (Lam e)) a = mkFun f (a: xs) (subst 0 a e)
    neutApp f a = Neut $ App_ f a

conType (snd . getParams . hnf -> TyCon (TyConName _ _ _ cs _) _) (ConName _ n t) = t --snd $ cs !! n

appTy (Pi _ a b) x = subst 0 x b
appTy t x = error $ "appTy: " ++ ppShow t

getParams :: Exp -> ([(Visibility, Exp)], Exp)
getParams (Pi h a b) = first ((h, a):) $ getParams b
getParams x = ([], x)

--------------------------------------------------------- evident types

class NType a where nType :: a -> Type

instance NType FunName       where nType (FunName _ _ _ t) = t
instance NType TyConName     where nType (TyConName _ _ t _ _) = t
instance NType CaseFunName   where nType (CaseFunName _ t _) = t
instance NType TyCaseFunName where nType (TyCaseFunName _ t) = t

instance NType Lit where
    nType = \case
        LInt _    -> TInt
        LFloat _  -> TFloat
        LString _ -> TString
        LChar _   -> TChar


