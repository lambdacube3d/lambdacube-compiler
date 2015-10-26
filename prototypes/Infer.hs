{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}

import Data.Monoid
import Data.Maybe
import Data.List
import Data.Char
import qualified Data.Map as Map

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Identity
import Control.Comonad
import Control.Arrow

import Text.ParserCombinators.Parsec hiding (parse)
import qualified Text.ParserCombinators.Parsec as P
import Text.ParserCombinators.Parsec.Token
import Text.ParserCombinators.Parsec.Language
import Text.Show.Pretty (ppShow)

import System.Console.Readline
import System.Environment
import Debug.Trace

-------------------------------------------------------------------------------- source data

type SName = String

data Stmt
    = Let SName SExp
    | Data SName [(Visibility, SExp)]{-parameters-} SExp{-type-} [(SName, SExp)]{-constructor names and types-}
    | Primitive SName SExp{-type-}
    deriving Show

data SExp
    = SLit Lit
    | SVar !Int                     -- De Bruijn variable
    | SGlobal SName
    | SBind Binder SExp SExp
    | SApp Visibility SExp SExp
    | STyped Exp
  deriving (Eq, Show)

data Lit
    = LInt !Int
    | LChar Char
  deriving (Eq, Show)

data Binder
    = BPi  Visibility
    | BLam Visibility
    | BMeta      -- a metavariable is like a floating hidden lambda -- TODO: formalize its typing
  deriving (Eq, Show)

data Visibility = Hidden | Visible    | {-not used-} Irr
  deriving (Eq, Show)

pattern SPi  h a b = SBind (BPi  h) a b
pattern SLam h a b = SBind (BLam h) a b
pattern SType = SGlobal "Type"
pattern Wildcard t = SBind BMeta t (SVar 0)
pattern SInt i = SLit (LInt i)
pattern SAnn a b = SApp Visible (SApp Visible (SGlobal "typeAnn") b) a

-------------------------------------------------------------------------------- destination data

data Exp
    = Bind Binder Exp Exp
    | Prim PrimName [Exp]
    | Var  !Int                 -- De Bruijn variable
    | CLet !Int Exp Exp         -- De Bruijn index decreasing let only for metavariables (non-recursive)
  deriving (Eq, Show)

data PrimName
    = ConName SName Int{-free arity-} (Additional Exp){-type before argument application-}
    | CLit Lit
    | FunName SName (Additional Exp)
    | FApp      -- todo: elim
    | FCstr     -- todo: elim
  deriving (Eq, Show)

pattern Lam h a b = Bind (BLam h) a b
pattern Pi  h a b = Bind (BPi h) a b
pattern Meta  a b = Bind BMeta a b

pattern App a b     = Prim FApp [a, b]
--pattern FApp <- FunName "app" _ where FApp = FunName "app" $ Additional $ pi_ Type $ pi_ Type 
pattern Cstr a b    = Prim FCstr [a, b]
pattern Coe a b w x = Prim FCoe [a,b,w,x]
pattern FCoe <- FunName "coe" _ where FCoe = FunName "coe" $ Additional $ pi_ Type $ pi_ Type $ pi_ (Cstr (Var 1) (Var 0)) $ pi_ (Var 2) (Var 2)  -- forall a b . (a ~ b) => a -> b
pattern PrimName a <- FunName a _
pattern PrimName' a b = FunName a (Additional b)

pattern PInt a      = CLit (LInt a)
pattern Con a i b   = ConName a i (Additional b)
pattern Type        = Prim CType []
pattern Sigma a b <- Prim BSigma [a, Lam _ _ b] where Sigma a b = Prim BSigma [a, Lam Visible a{-todo: don't duplicate-} b]
pattern BSigma <- ConName "Sigma" 0 _ where BSigma = ConName "Sigma" 0 $ Additional $ pi_ Type $ pi_ (pi_ (Var 0) Type) $ Type
pattern CType <- ConName "Type" 0 _ where CType = ConName "Type" 0 $ Additional Type
pattern Unit        = Prim CUnit []
pattern CUnit <- ConName "Unit" 0 _ where CUnit = ConName "Unit" 0 $ Additional Type
pattern TT          = Prim CTT []
pattern CTT <- ConName "TT" 0 _ where CTT = ConName "TT" 0 $ Additional Unit
pattern T2T a b     = Prim CT2T [a, b]
pattern CT2T <- ConName "T2" 0 _ where CT2T = ConName "T2" 0 $ Additional $ pi_ Type $ pi_ Type Type
pattern T2 a b <- Prim CT2 [_, _, a, b] where T2 a b = Prim CT2 [error "t21", error "t22", a, b]   -- TODO
pattern CT2 <- ConName "T2C" 0 _ where CT2 = ConName "T2C" 0 $ Additional $ pi_ Type $ pi_ Type $ pi_ (Var 1) $ pi_ (Var 1) $ T2T (Var 1) (Var 0)
pattern Empty       = Prim CEmpty []
pattern CEmpty <- ConName "Empty" 0 _ where CEmpty = ConName "Empty" 0 $ Additional Type

newtype Additional a = Additional a
instance Eq (Additional a) where _ == _ = True
instance Ord (Additional a) where _ `compare` _ = EQ
instance Show (Additional a) where show a = ""

-------------------------------------------------------------------------------- environments

-- SExp zippers
data Env_ b
    = EBind Binder Exp (Env_ b)     -- zoom into second parameter of SBind
    | ELet Int Exp (Env_ b)     -- why exactly needed?
    | CheckType Exp (Env_ b)
    | EEnd b        -- TODO: remove

    -- todo: use
    | EBind1 Binder (Env_ b) SExp           -- zoom into first parameter of SBind
    | EApp1 Visibility (Env_ b) SExp
    | EApp2 Visibility Exp (Env_ b)
--    | EGlobal GlobalEnv [Stmt]

    deriving (Show, Functor)

type GlobalEnv = Map.Map SName Exp

type Env = Env_ GlobalEnv
type EnvEnv = Env_ Env

instance Applicative Env_ where
    pure = EEnd
    a <*> b = a >>= \av -> b >>= \bv -> pure (av bv)
instance Monad Env_ where
    return = pure
    EEnd a >>= f = f a
    ELet i a x >>= f = ELet i a (x >>= f)
    EBind b a x >>= f = EBind b a (x >>= f)
    EBind1 b x a >>= f = EBind1 b (x >>= f) a
    EApp2 b a x >>= f = EApp2 b a (x >>= f)
    EApp1 b x a >>= f = EApp1 b (x >>= f) a
    CheckType x a >>= f = CheckType x (a >>= f)
instance Monoid a => Monoid (Env_ a) where
    mempty = EEnd mempty
    EEnd a `mappend` b = b
    ELet i a x `mappend` b = ELet i a (x `mappend` b)
    EBind b a x `mappend` f = EBind b a (x `mappend` f)
    EBind1 b x a `mappend` f = EBind1 b (x `mappend` f) a
    EApp2 b a x `mappend` f = EApp2 b a (x `mappend` f)
    EApp1 b x a `mappend` f = EApp1 b (x `mappend` f) a
    CheckType x a `mappend` f = CheckType x (a `mappend` f)
instance Comonad Env_ where
    extract (ELet _ _ x) = extract x
    extract (EEnd x) = x
    extract (EBind _ _ x) = extract x
    extract (EBind1 _ x _) = extract x
    extract (EApp2 _ _ x) = extract x
    extract (EApp1 _ x _) = extract x
    extract (CheckType _ x) = extract x
    extend = error "extend env"

-- zipper for binders; same as (,)
data Z_ b a = Z b a
    deriving (Show, Functor)

type Z = Z_ Env

instance Monoid a => Applicative (Z_ a) where
    pure = Z mempty
    Z e a <*> Z e' b = Z (e `mappend` e') (a b)
instance Monoid a => Monad (Z_ a) where
    return = pure
    Z e a >>= f = Z (e `mappend` e') b  where Z e' b = f a
instance Comonad (Z_ a) where
    extract (Z _ x) = x
    duplicate (Z a x) = (Z a (Z a x))

-----------------------

type AddM m = StateT (GlobalEnv, Int) (ExceptT String m)

-------------------------------------------------------------------------------- low-level toolbox

handleLet i j f
    | i >  j = f (i-1) j
    | i <= j = f i (j+1)

mergeLets meta clet g1 g2 i x j a
    | j > i, Just a' <- downE i a = clet (j-1) a' (g2 i (g1 (j-1) a' x))
    | j > i, Just x' <- downE (j-1) x = clet (j-1) (g1 i x' a) (g2 i x')
    | j < i, Just a' <- downE (i-1) a = clet j a' (g2 (i-1) (g1 j a' x))
    | j < i, Just x' <- downE j x = clet j (g1 (i-1) x' a) (g2 (i-1) x')
    | j == i = meta
    -- otherwise: Empty?

elet 0 _ (EBind _ _ xs) = xs
--elet i (downE 0 -> Just e) (EBind b x xs) = EBind b (substE (i-1) e x) (elet (i-1) e xs)
--elet i e (ELet j x xs) = mergeLets (error "ml") ELet substE (\i e -> elet i e xs) i e j x
elet i e xs = ELet i e xs

foldS f i = \case
    SVar k -> f i k
    SApp _ a b -> foldS f i a <> foldS f i b
    SBind _ a b -> foldS f i a <> foldS f (i+1) b
    STyped e -> foldE f i e
    x@SGlobal{} -> mempty
    x@SLit{} -> mempty

foldE f i = \case
    Var k -> f i k
    Bind _ a b -> foldE f i a <> foldE f (i+1) b
    Prim _ as -> foldMap (foldE f i) as
    CLet j x a -> handleLet i j $ \i' j' -> foldE f i' x <> foldE f i' a

usedS = (getAny .) . foldS ((Any .) . (==))
usedE = (getAny .) . foldE ((Any .) . (==))

mapS ff h e f = g e where
    g i = \case
        SVar k -> f i k
        SApp v a b -> SApp v (g i a) (g i b)
        SBind k a b -> SBind k (g i a) (g (h i) b)
        STyped x -> STyped $ ff i x
        x@SGlobal{} -> x
        x@SLit{} -> x

upS__ i n = mapS (\i e -> iterate (up1E i) e !! n) (+1) i $ \i k -> SVar $ if k >= i then k+n else k
upS_ i = upS__ i 1
upS = upS_ 0
transportS = upS__ 0

up1E = g where
    g i = \case
        Var k -> Var $ if k >= i then k+1 else k
        Bind h a b -> Bind h (g i a) (g (i+1) b)
        Prim s as  -> Prim s $ map (g i) as
        CLet j a b -> handleLet i j $ \i' j' -> CLet j' (g i' a) (g i' b)

up1E0 = up1E 0
upE0 n e = iterate up1E0 e !! n

substS j x = mapS (uncurry substE) ((+1) *** up1E 0) (j, x)
            (\(i, x) k -> case compare k i of GT -> SVar (k-1); LT -> SVar k; EQ -> STyped x)

substE i x = \case
    Var k -> case compare k i of GT -> Var $ k - 1; LT -> Var k; EQ -> x
    Bind h a b -> Bind h (substE i x a) (substE (i+1) (up1E0 x) b)
    Prim s as  -> eval . Prim s $ map (substE i x) as
    CLet j a b -> mergeLets (Meta (cstr x a) $ up1E0 b) CLet substE (\i j -> substE i j b) i x j a

unVar (Var i) = i

varType :: String -> Int -> Env -> (Binder, Exp)
varType err n_ env = f n_ env where
    f n (ELet i x es)  = id *** substE i x $ f (if n < i then n else n+1) es
    f 0 (EBind b t _)  = (b, up1E0 t)
    f n (EBind _ _ es) = id *** up1E0 $ f (n-1) es
    f n (EBind1 _ es _) = f n es
    f n (EApp2 _ _ es) = f n es
    f n (EApp1 _ es _) = f n es
    f n (CheckType _ es) = f n es
    f n xx = error $ "varType: " ++ err ++ "\n" ++ show n_ ++ "\n" ++ show env ++ "\n" ++ show xx

-----------xabcdQ
-----------abcdQ
downE t x | usedE t x = Nothing
          | otherwise = Just $ substE t (error "downE") x

-------------------------------------------------------------------------------- reduction

infixl 1 `app_`

app_ :: Exp -> Exp -> Exp
app_ (Lam _ _ x) a = substE 0 a x
app_ (Prim (Con s n t) xs) a = Prim (Con s (n-1) t) (xs ++ [a])
app_ f a = App f a

eval (App a b) = app_ a b
eval (Cstr a b) = cstr a b
eval (Coe a b c d) = coe a b c d
--eval x@(Prim (PrimName "primFix") [_, _, f]) = app_ f x
eval (Prim p@(PrimName "natElim") [a, z, s, Prim (Con "Succ" _ _) [x]]) = s `app_` x `app_` (eval (Prim p [a, z, s, x]))
eval (Prim (PrimName "natElim") [_, z, s, Prim (Con "Zero" _ _) []]) = z
eval (Prim p@(PrimName "finElim") [m, z, s, n, Prim (Con "FSucc" _ _) [i, x]]) = s `app_` i `app_` x `app_` (eval (Prim p [m, z, s, i, x]))
eval (Prim (PrimName "finElim") [m, z, s, n, Prim (Con "FZero" _ _) [i]]) = z `app_` i
eval (Prim (PrimName "eqCase") [_, _, f, _, _, Prim (Con "Refl" 0 _) _]) = error "eqC"
eval (Prim p@(PrimName "Eq") [Prim (Con "List" _ _) [a]]) = eval $ Prim p [a]
eval (Prim (PrimName "Eq") [Prim (Con "Int" 0 _) _]) = Unit
eval (Prim (PrimName "Monad") [(Prim (Con "IO" 1 _) [])]) = Unit
eval x = x

-- todo
coe _ _ TT x = x
coe a b c d = Coe a b c d

cstr a b | a == b = Unit
--cstr (App x@(Var j) y) b@(Var i) | j /= i, Nothing <- downE i y = cstr x (Lam (expType' y) $ up1E0 b)
cstr a@Var{} b = Cstr a b
cstr a b@Var{} = Cstr a b
--cstr (App x@Var{} y) b@Prim{} = cstr x (Lam (expType' y) $ up1E0 b)
--cstr b@Prim{} (App x@Var{} y) = cstr (Lam (expType' y) $ up1E0 b) x
cstr (Pi h a (downE 0 -> Just b)) (Pi h' a' (downE 0 -> Just b')) | h == h' = T2T (cstr a a') (cstr b b') 
cstr (Bind h a b) (Bind h' a' b') | h == h' = Sigma (cstr a a') (Pi Visible a (cstr b (coe a a' (Var 0) b'))) 
--cstr (Lam a b) (Lam a' b') = T2T (cstr a a') (cstr b b') 
cstr (Prim (Con a _ _) [x]) (Prim (Con a' _ _) [x']) | a == a' = cstr x x'
--cstr a@(Prim aa [_]) b@(App x@Var{} _) | constr' aa = Cstr a b
cstr (Prim (Con a n t) xs) (App b@Var{} y) = T2T (cstr (Prim (Con a (n+1) t) (init xs)) b) (cstr (last xs) y)
cstr (App b@Var{} y) (Prim (Con a n t) xs) = T2T (cstr b (Prim (Con a (n+1) t) (init xs))) (cstr y (last xs))
cstr (App b@Var{} a) (App b'@Var{} a') = T2T (cstr b b') (cstr a a')     -- TODO: injectivity check
cstr (Prim a@Con{} xs) (Prim a' ys) | a == a' = foldl1 T2T $ zipWith cstr xs ys
--cstr a b = Cstr a b
cstr a b = error ("!----------------------------! type error: \n" ++ show a ++ "\n" ++ show b) Empty

-------------------------------------------------------------------------------- simple typing

pi_ = Pi Visible

tInt = Prim (Con "Int" 0 Type) []

primitiveType = \case
    PInt _  -> tInt
    PrimName' _ t  -> t
    FCstr   -> pi_ (error "cstrT0") $ pi_ (error "cstrT1") Type       -- todo
    Con _ _ t -> t

expType_ te = \case
    Meta t x -> error "meta type" --Pi Hidden t <$> withItem (EBind BMeta t) (expType x)     -- todo
    Lam h t x -> Pi h t $ expType_ (EBind (BLam h) t te) x
    App f x -> app (expType_ te f) x
    Var i -> snd $ varType "C" i te
    Pi{} -> Type
    Prim t ts -> foldl app (primitiveType t) ts
    x -> error $ "expType: " ++ show x 
  where
    app (Pi _ a b) x = substE 0 x b

-------------------------------------------------------------------------------- inference

check env x t = checkN $ Z (EEnd env) (x, t)
infer env x = inferN__' $ Z (EEnd env) x

checkN x@(Z _ (SLam Hidden _ _, Pi Hidden _ _)) = checkN_ x
checkN (Z te (e, Pi Hidden a b)) = checkN $ Z (EBind (BLam Hidden) a te) (upS e, b)
checkN x = checkN_ x

checkN_ (Z te (SLam h a b, Pi h' x y))
    | h /= h' = error "check lam"
    | True <- checkSame' te a x     -- TODO
    = checkN $ Z (EBind (BLam h) x $ te) (b, y)
checkN_ (Z te (e, t))
    = inferN__' $ Z (CheckType t te) e

inferN__' x@(Z e s) = (if tr then trace ("infer: " ++ ppshowS'' e s) else id) $ recheck_ e inf
  where
    inf = inferN__ x

pushMeta :: Exp -> Exp -> Env -> Maybe (Env, Exp)
pushMeta _ _ (EBind BMeta _ _) = Nothing
--  \(:x) -> <:b> -> a    -->  <:b[kill V0]> -> \(:x[up 1]) -> a[swap V0 V1]
pushMeta a (downE 0 -> Just b) (EBind h x e) = Just (EBind h (up1E0 x) (EBind BMeta b e), substE 2 (Var 0) $ up1E0 a)
--  \(:<:b> -> a) -> x    -->  <:b> -> \(:a) ->  x[up 1 1]
pushMeta a b (EBind1 h e x)  = Just (EBind1 h (EBind BMeta b e) $ upS_ 1 x, a)
--  (<:b> -> a) @ x   -->  <:b> -> a @ (up 1 x)
pushMeta a b (EApp1 h e x)   = Just (EApp1 h (EBind BMeta b e) $ upS_ 0 x, a)
--  x @ (<:b> -> a)  -->  <:b> -> up 1 x @ a
pushMeta a b (EApp2 h x e)   = Just (EApp2 h (up1E0 x) (EBind BMeta b e), a)
pushMeta a b (CheckType t e) = Just (CheckType (up1E0 t) (EBind BMeta b e), a)
pushMeta a b e@(EEnd _)      = Nothing
pushMeta _ b x = (if debug then trace ("pushMeta: " ++ show x ++ "\n" ++ show b) else id) Nothing

--  \(:x) -> <i := (kill 0 -> b)> -> a  -->  <i-1 := b> -> \(:x[i-1 := b]) -> a
pushLet a i@((>0) -> True) (downE 0 -> Just b) (EBind h x e)    = Just (EBind h (substE (i-1) b x) (ELet (i-1) b e), a)
--  \(:<i:=b> -> a) -> x     -->  <i:=b> -> \(:a) ->  x[i+1:=up 1 b]
pushLet a i b (EBind1 h e x)    = Just (EBind1 h (ELet i b e) $ substS (i+1) (up1E0 b) x, a)
--  (<i:=b> -> a) @ x   -->  <i:=b> -> a @ x[i:=b]
pushLet a i b (EApp1 h e x)    = Just (EApp1 h (ELet i b e) $ substS i b x, a)
--  x @ (<i := b> -> a)   -->  <i := b> -> x[i:=b] @ a
pushLet a i b (EApp2 h x e)    = Just (EApp2 h (substE i b x) (ELet i b e), a)
pushLet a i b (CheckType t e)    = Just (CheckType (substE i b t) (ELet i b e), a)
pushLet a i b te = flip (,) a <$> pull i te
--pushLet _ i b x = {-trace ("pushLet: " ++ show i ++ "\n" ++ show x ++ "\n" ++ show b) $ -}Nothing

pull 0 (EBind BMeta _ te) = Just te
pull i (EBind h (downE (i-1) -> Just x) te)
    | Just te' <- pull (i-1) te
    = Just (EBind h x te')
pull i (ELet j b te)
    | j <= i
    , Just b' <- downE i b
    , Just te' <- pull (i+1) te
    = Just (ELet j b' te')
    | j > i
    , Just b' <- downE i b
    , Just te' <- pull i te
    = Just (ELet (j-1) b' te')
pull _ _ = Nothing

focus e x = (if tr then trace $ "focus: " ++ ppshow'' e x else id) $ focus_ e x

focuss e (Bind BMeta x a) = focus (EBind BMeta x e) a
focuss e (CLet i x a) = focus (ELet i x e) a
focuss e a = focus e a

focusss e (Bind BMeta x a) = focusss (EBind BMeta x e) a
focusss e (CLet i x a) = focus (ELet i x e) a
focusss e a = focus e a

focus_ :: Env -> Exp -> Exp
focus_ te@(EApp1 h e b) a
    | Pi Visible x y <- expType_ te a
    = checkN $ Z (EApp2 h a e) (b, x)
    | ta <- expType_ te a
    = inferN__' $ Z (CheckType (Var 2) $ EApp2 h (coe (upE0 3 ta) (Pi Visible (Var 2) (Var 2)) (Var 0) $ upE0 3 a) $ EBind BMeta (cstr (upE0 2 ta) (Pi Visible (Var 1) (Var 1))) $ EBind BMeta Type $ EBind BMeta Type e) (upS $ upS $ upS b)
focus_ (CheckType t te) e
    = focus (EBind BMeta (cstr t (expType_ te e)) te) $ up1E0 e
focus_ (EApp2 Visible a e) b = focus e $ app_ a b
focus_ (EBind1 h e b) a = inferN__' $ Z (EBind h a e) b
focus_ (EBind BMeta Unit te) y = focus te $ substE 0 TT y
focus_ (EBind BMeta (T2T x y) te) e = focus (EBind BMeta (up1E0 y) $ EBind BMeta x te) $ substE 2 (T2 (Var 1) (Var 0)) $ upE0 2 e
focus_ (EBind BMeta (Cstr a b) te) y
    | Just i <- cst a, Just j <- cst b, i < j, Just e <- downE i b, x <- substE i e $ substE 0 TT y = focus (ELet i e te) x
    | Just i <- cst b, Just e <- downE i a, x <- substE i e $ substE 0 TT y = focus (ELet i e te) x
    | Just i <- cst a, Just e <- downE i b, x <- substE i e $ substE 0 TT y = focus (ELet i e te) x
  where
    cst = \case
        Var i | fst (varType "X" i te) == BMeta -> Just i
        _ -> Nothing
focus_ (EBind BMeta b e) a
    | Just (e', a') <- pushMeta a b e = focuss e' a'
focus_ (ELet i b e) a
    | Just (e', a') <- pushLet a i b e = focusss e' a'
focus_ (EBind h a e) b = focus e $ Bind h a b
focus_ (EEnd _) a = a
focus_ (ELet i x te) a = focus te $ CLet i x a                -- todo?
focus_ e x = error $ "focus: " ++ show e

zoomMeta' :: Z Exp -> Z Exp
zoomMeta' (Z e t) = add e t
  where
    add env = \case
        Meta t e -> add (EBind BMeta t env) e
        CLet i t e -> add (ELet i t env) e
        e -> Z env e

unZ f (Z a b) = f a b

expand' te e
    | Pi Hidden a b <- expType_ te e
    = expand' (EBind BMeta a te) (app_ (up1E0 e) $ Var 0)
expand' te e = focus te e

inferN__ :: Z SExp -> Exp
inferN__ (Z te exp) = case exp of
    SInt i  -> focus te $ Prim (PInt i) []
    STyped e -> expand' te e
    SVar i -> expand' te $ Var i
    SGlobal s -> unZ focus $ zoomMeta' $ Z te $ fromMaybe (error "can't found") $ Map.lookup s $ extract te
    SApp  h a b -> inferN__' $ Z (EApp1 h te b) a
    SBind h a b -> inferN__' $ Z ((if h /= BMeta then CheckType Type else id) $ EBind1 h te $ (if isPi h then tyType else id) b) a
    x -> error $ "inferN: " ++ show x
  where
    isPi (BPi _) = True
    isPi _ = False
    tyType = SApp Visible $ STyped $ Lam Visible Type $ Var 0

-- todo
checkSame' te (Wildcard (Wildcard SType)) a = True
checkSame' te (Wildcard SType) a = case expType_ te a of
    Type -> True
checkSame' te a b = error $ "checkSame: " ++ show (a, b)

-------------------------------------------------------------------------------- debug support

add (Meta t e) env = add e (EBind BMeta t env)
add (CLet i t e) env = add e (ELet i t env)
add e env = (env, e)
{-
evv (env, e) y = sum [case t of Type -> 1; _ -> error $ "evv: " ++ ppshow'' e x ++ "\n"  ++ ppshow'' e t | (e, x, t) <- checkEnv env] `seq` 
    (length $ show $ checkInfer env e) `seq` y

checkEnv ENil = []
checkEnv (EBind _ t e) = (e, t, checkInfer e t): checkEnv e
checkEnv (ELet i t e) = (e, t', checkInfer e (checkInfer e t')): checkEnv e  where t' = up1E i t
-}
recheck :: Exp -> Exp
recheck e = length (show $ checkInfer te e') `seq` e  where (te, e') = add e (EEnd (error "global env"))

recheck_ e' x = if debug then length (show $ checkInfer e'' x') `seq` x else x
  where
    (Z e'' x') = zoomMeta' $ Z e' x

checkInfer lu x = flip runReader [] (infer x)  where
    infer = \case
        Pi _ a b -> ch Type a !>> local (a:) (ch Type b) !>> return Type
        Type -> return Type
        Var k -> asks $ \env -> ([upE0 (k + 1) e | (k, e) <- zip [0..] env] ++ [upE0 (length env) $ snd $ varType "?" i lu | i<- [0..]]) !! k
        Lam h a b -> ch Type a !>> Pi h a <$> local (a:) (infer b)
        App a b -> ask >>= \env -> appf env <$> infer a <*> infer' b
        Prim s as -> ask >>= \env -> foldl (appf env) (primitiveType s) <$> mapM infer' as
        Meta a b -> ch Type a !>> Pi Hidden a <$> local (a:) (infer b) --todo --error $ "checkInfer: meta"
    infer' a = (,) a <$> infer a
    appf _ (Pi h x y) (v, x') | x == x' = substE 0 v y
    appf en a (_, b) = error $ "recheck:\n" ++ show a ++ "\n" ++ show b ++ "\n" ++ show en ++ "\n" ++ ppshow'' lu x
    ch x e = infer e >>= \case
        z | z == x -> return ()
          | otherwise -> error $ "recheck':\n" ++ show z ++ "\n" ++ show x ++ "\n" ++ ppshow'' lu x

infixl 1 !>>
a !>> b = a >>= \x -> x `seq` b

-------------------------------------------------------------------------------- statements

infer' t = gets $ (\env -> (if debug_light then recheck else id) $ infer env t) . fst
checkP t e = gets $ (\env -> check env e t) . fst

expType'' :: Exp -> String
expType'' e = ppshow'' env $ expType_ env e'
  where
    (env, e') = add e (EEnd $ error "global env")

addToEnv :: Monad m => String -> Exp -> AddM m ()
addToEnv s x = trace' (s ++ "     " ++ expType'' x) $ modify $ Map.insert s x *** id

addParams [] t = t
addParams ((h, x): ts) t = SPi h x $ addParams ts t

rels (Meta _ x) = Hidden: rels x
rels x = f x where
    f (Pi r _ x) = r: f x
    f _ = []

arityq = length . rels

handleStmt :: MonadFix m => Stmt -> AddM m ()
handleStmt (Let n t) = infer' t >>= addToEnv n
handleStmt (Primitive s t) = infer' t >>= addToEnv s . mkPrim False s
handleStmt (Data s ps t_ cs) = do
    vty <- checkP Type (addParams ps t_)
    let
      pnum = length ps
      pnum' = length $ filter ((== Visible) . fst) ps
      cnum = length cs
      inum = arityq vty - pnum

      dropArgs' (SPi _ _ x) = dropArgs' x
      dropArgs' x = x
      getApps (SApp h a b) = id *** (b:) $ getApps a
      getApps x = (x, [])

      arity (SPi _ _ x) = 1 + arity x
      arity x = 0
      arityh (SPi Hidden _ x) = 1 + arityh x
      arityh x = 0

      apps a b = foldl sapp (SGlobal a) b
      downTo n m = map SVar [n+m-1, n+m-2..n]

      pis 0 e = e
      pis n e = SPi Visible ws $ pis (n-1) e

      pis' (SPi h a b) e = SPi h a $ pis' b e
      pis' _ e = e

      ws = Wildcard $ Wildcard SType

    addToEnv s $ mkPrim True s vty -- $ (({-pure' $ lams'' (rels vty) $ VCon cn-} error "pvcon", lamsT'' vty $ VCon cn), vty)

    let
      mkCon i (cs, ct_) = do
          ty <- checkP Type (addParams [(Hidden, x) | (Visible, x) <- ps] ct_)
          return (i, cs, ct_, ty, arity ct_, arity ct_ - arityh ct_)

    cons <- zipWithM mkCon [0..] cs

    mapM_ (\(_, s, _, t, _, _) -> addToEnv s $ mkPrim True s t) cons

    let
      cn = lower s ++ "Case"
      lower (c:cs) = toLower c: cs

      addConstr _ [] t = t
      addConstr en ((j, cn, ct, cty, act, acts): cs) t = SPi Visible tt $ addConstr (1 + en) cs t
        where
          tt = pis' (transportS en ct)
             $ foldl sapp (SVar $ j + act) $ mkTT (getApps $ dropArgs' ct) ++ [apps cn (downTo 0 acts)]

          mkTT (c, reverse -> xs)
                | c == SGlobal s && take pnum' xs == downTo (0 + act) pnum' = drop pnum' xs
                | otherwise = error $ "illegal data definition (parameters are not uniform) " ++ show (c, cn, take pnum' xs, act)
                        -- TODO: err


      tt = (pis inum $ SPi Visible (apps s $ [ws | (Visible, _) <- ps] ++ downTo 0 inum) SType)
    caseTy <- checkP Type $ tracee'
            $ addParams [(Hidden, x) | (Visible, x) <- ps]
            $ SPi Visible tt
            $ addConstr 1 cons
            $ pis (1 + inum)
            $ foldl sapp (SVar $ cnum + inum + 1) $ downTo 1 inum ++ [SVar 0]

    addToEnv cn $ mkPrim False cn caseTy

tracee' x = trace (snd $ flip runReader [] $ flip evalStateT vars $ showSExp x) x

toExp' (Meta x e) = Pi Hidden x $ toExp' e
toExp' a = a

mkPrim True n t = f'' 0 t
  where
    f'' i (Meta a t) = Meta a $ f'' (i+1) t
    f'' i t = f' i t
    f' i (Pi Hidden a b) = Meta a $ f' (i+1) b
    f' i x = Prim (Con n (ar x) $ toExp' t) $ map Var [i-1, i-2 .. 0]
    ar (Pi _ _ b) = 1 + ar b
    ar _ = 0
mkPrim c n t = f'' 0 t
  where
    f'' i (Meta a t) = Meta a $ f'' (i+1) t
    f'' i t = f' i t
    f' i (Pi Hidden a b) = Meta a $ f' (i+1) b
    f' i x = f i x
    f i (Pi h a b) = Lam h a $ f (i+1) b
    f i _ = Prim (if c then Con n 0 t' else PrimName' n t') $ map Var [i-1, i-2 .. 0]
    t' = toExp' t

env :: GlobalEnv
env = Map.fromList
        [ (,) "Int" tInt
        , (,) "Type" Type
        ]

-------------------------------------------------------------------------------- parser

slam a = SLam Visible (Wildcard SType) a
sapp = SApp Visible
sPi r = SPi r
sApp = SApp
sLam r = SLam r

lang = makeTokenParser (haskellStyle { identStart = letter <|> P.char '_',
                                       reservedNames = ["forall", "let", "data", "primitive", "fix", "Type"] })

parseType vs = (reserved lang "::" *> parseCTerm 0 vs) <|> return (Wildcard SType)
parseType' vs = (reserved lang "::" *> parseCTerm 0 vs)
typedId vs = (,) <$> identifier lang <*> parseType vs

type Pars = CharParser Int

parseStmt_ :: [String] -> Pars Stmt
parseStmt_ e = do
     do Let <$ reserved lang "let" <*> identifier lang <* reserved lang "=" <*> parseITerm 0 e
 <|> do uncurry Primitive <$ reserved lang "primitive" <*> typedId []
 <|> do
      x <- reserved lang "data" *> identifier lang
      let params vs = option [] $ ((,) Visible <$> parens lang (typedId vs) <|> (,) Hidden <$> braces lang (typedId vs)) >>= \xt -> (xt:) <$> params (fst (snd xt): vs)
      (hs, unzip -> (reverse -> nps, ts)) <- unzip <$> params []
      let parseCons = option [] $ (:) <$> typedId nps <*> option [] (reserved lang ";" *> parseCons)
      Data x (zip hs ts) <$> parseType nps <* reserved lang "=" <*> parseCons

parseITerm :: Int -> [String] -> Pars SExp
parseITerm 0 e =
   do reserved lang "forall"
      (fe,ts) <- rec (e, [])
      reserved lang "."
      t' <- parseCTerm 0 fe
      return $ foldl (\p (r, t) -> sPi r t p) t' ts
 <|> do try $ parseITerm 1 e >>= \t -> option t $ rest t
 <|> do parens lang (parseLam e) >>= rest
 where
    rec b = option b $ (parens lang (xt Visible b) <|> braces lang (braces lang (xt Irr b) <|> xt Hidden b) <|> xt Visible b) >>= \x -> rec x
    xt r (e, ts) = ((:e) *** (:ts) . (,) r) <$> typedId e
    rest t = sPi Visible t <$ reserved lang "->" <*> parseCTerm 0 ([]:e)
parseITerm 1 e =
     do try $ parseITerm 2 e >>= \t -> option t $ rest t
 <|> do parens lang (parseLam e) >>= rest
 <|> do parseLam e
 where
    rest t = SAnn t <$> parseType' e <|> return t
parseITerm 2 e = foldl (sapp) <$> parseITerm 3 e <*> many (optional (P.char '!') >> parseCTerm 3 e)
parseITerm 3 e =
     {-do (ILam Cstr SType $ ILam Cstr (Bound 0) (Bound 0)) <$ reserved lang "_"
 <|> -}do SType <$ reserved lang "Type"
 <|> do SInt . fromIntegral <$ P.char '#' <*> natural lang
 <|> do toNat <$> natural lang
 <|> do reserved lang "fix"
        i <- P.getState
        P.setState (i+1)
        return $ sApp Visible{-Hidden-} (SGlobal "primFix") (SInt i)
 <|> parseLam e
 <|> do identifier lang >>= \case
            "_" -> return $ Wildcard (Wildcard SType)
            x -> return $ maybe (SGlobal x) SVar $ findIndex (== x) e
 <|> parens lang (parseITerm 0 e)
  
parseCTerm :: Int -> [String] -> Pars SExp
parseCTerm 0 e = parseLam e <|> parseITerm 0 e
parseCTerm p e = try (parens lang $ parseLam e) <|> parseITerm p e

parseLam :: [String] -> Pars SExp
parseLam e = do
    reservedOp lang "\\"
    (fe, ts) <- rec (e, []) -- <|> xt Visible (e, [])
    reserved lang "->"
    t' <- parseITerm 0 fe
    return $ foldl (\p (r, t) -> sLam r t p) t' ts
 where
    rec b = (parens lang (xt Visible b) <|> braces lang (braces lang (xt Irr b) <|> xt Hidden b) <|> xt Visible b) >>= \x -> option x $ rec x
    xt r (e, ts) = ((:e) *** (:ts) . (,) r) <$> typedId e

toNat 0 = SGlobal "Zero"
toNat n = sapp (SGlobal "Succ") $ toNat (n-1)

-------------------------------------------------------------------------------- pretty print

newVar = gets head <* modify tail
addVar v = local (v:)

pshow :: Exp -> String
pshow = snd . flip runReader [] . flip evalStateT vars . showExp

vars = flip (:) <$> iterate ('\'':) "" <*> ['a'..'z']

infixl 4 <**>

m <**> n = StateT $ \s -> (\(a, _) (b, _) -> (a b, error "<**>")) <$> flip runStateT s m <*> flip runStateT s n

rails (_, s') = (10, "||" ++ s' ++ "||")

ppshow'' :: Env -> Exp -> String
ppshow'' e c = snd $ flip runReader [] . flip evalStateT vars $ showEnv e $ rails <$> showExp c

ppshowS'' :: Env -> SExp -> String
ppshowS'' e c = snd $ flip runReader [] . flip evalStateT vars $ showEnv e $ rails <$> showSExp c

ppshow' e s t c = snd $ flip runReader [] . flip evalStateT vars $ showEnv e $ (\(_, s) mt me -> (10, "\n    " ++ s ++ maybe "" (\(_, t) -> "   ::  " ++ t) mt ++ maybe "" (\(_, s') -> "\n    " ++ s') me)) <$> showSExp s <**> traverse showExp t <**> traverse showExp c

showEnv :: Env -> StateT [String] (Reader [String]) (Int, String) -> StateT [String] (Reader [String]) (Int, String)
showEnv x m = case x of
        (EEnd _) -> m
        (EBind BMeta Type ts) -> f ts $ newVar >>= \i -> utlam i "" ("->") (cpar True) <$> addVar i m
        (ELet i t ts) -> f ts $ asks (ind' i) >>= \i' -> local (dropNth i) $ lam i' ("", "->", ":=", cpar True) <$> showExp t <*> m
        EBind b t ts -> f ts $ newVar >>= \i -> lam i (ff b) <$> showExp t <*> addVar i m
        EBind1 h ts b -> f ts $ newVar >>= \i -> lam' i (ff h) <$> m <*> addVar i (showSExp b)
        EApp1 Visible ts b -> f ts $ (.$) <$> m <*> showSExp b
        EApp2 Visible b ts -> f ts $ (.$) <$> showExp b <*> m
        CheckType t ts -> f ts $ sann <$> m <*> showExp t
        x -> error $ "showEnv: " ++ show x
  where
--    f :: Env -> StateT [String] (Reader [String]) (Int, String)
    f = showEnv

    utlam i s s' p (_, s2) = (1, s ++ p (i) ++ " " ++ s' ++ " " ++ s2)
    lam i (s, s', s'', p) (_, s1) (_, s2) = (1, s ++ p (i ++ " " ++ s'' ++ " " ++ s1) ++ " " ++ s' ++ " " ++ s2)
    lam' i (s, s', s'', p) (_, s1) (_, s2) = (1, s ++ p (i ++ " " ++ s'' ++ " " ++ s1) ++ " " ++ s' ++ " " ++ s2)
    (i, x) .$ (j, y) = (2, par (i == 1 || i > 2) x ++ " " ++ par (j == 1 || j >= 2) y)
    sann (i, x) (j, y) = (5, par (i == 1 || i >= 5) x ++ " :: " ++ par (j == 1 || j >= 5) y)
    ff = \case
                BMeta -> ("", "->", "::", cpar True)
                BLam h -> ("\\", "->", "::", vpar h)
                BPi h -> ("", "->", "::", vpar h)

showExp :: Exp -> StateT [String] (Reader [String]) (Int, String)
showExp = \case
    Type -> pure $ atom "Type"
    Cstr a b -> cstr <$> f a <*> f b
    Var k -> asks $ \env -> atom $ if k >= length env || k < 0 then "Var" ++ show k else env !! k
    App a b -> (.$) <$> f a <*> f b
    Meta Type e -> newVar >>= \i -> utlam i "" ("->") (cpar True) <$> addVar i (f e)
    Meta t e -> newVar >>= \i -> lam i "" ("->") "::" (cpar True) <$> f t <*> addVar i (f e)
    Lam h t e -> newVar >>= \i -> lam i "\\" ("->") "::" (vpar h) <$> f t <*> addVar i (f e)
    Pi Visible t e | not (usedE 0 e) -> arr ("->") <$> f t <*> addVar "?" (f e)
    Pi h t e -> newVar >>= \i -> lam i "" ("->") "::" (vpar h) <$> f t <*> addVar i (f e)
    Prim s xs -> ff (atom $ sh s) <$> mapM f xs
    CLet i t ts -> asks (ind' i) >>= \i' -> local (dropNth i) $ lam i' "" "->" ":=" (cpar True) <$> f t <*> f ts
    Bind b _ _ -> error $ "showExp: " ++ show b

  where
    f = showExp
    ff x [] = x
    ff x (y:ys) = ff (x .$ y) ys
    atom s = (0, s)
    utlam i s s' p (_, s2) = (1, s ++ p (i) ++ " " ++ s' ++ " " ++ s2)
    lam i s s' s'' p (_, s1) (_, s2) = (1, s ++ p (i ++ " " ++ s'' ++ " " ++ s1) ++ " " ++ s' ++ " " ++ s2)
    (i, x) .$ (j, y) = (2, par (i == 1 || i > 2) x ++ " " ++ par (j == 1 || j >= 2) y)
--        (i, x) ..$ (j, y) = (2, par (i == 1 || i > 2) x ++ " " ++ brace True y)
    arr s (i, x) (j, y) = (3, par (i == 1 || i >= 3) x ++ " " ++ s ++ " " ++ par (j == 1 || j > 3) y)
    (i, x) `cstr` (j, y) = (4, par (i == 1 || i >= 4) x ++ " ~ " ++ par (j == 1 || j >= 4) y)

    sh = \case
        PInt i -> show i
        PrimName s -> s
        Con s _ t -> s
        x -> show x

showSExp :: SExp -> StateT [String] (Reader [String]) (Int, String)
showSExp = \case
    SVar k -> asks $ \env -> atom $ if k >= length env || k < 0 then "Var" ++ show k else env !! k
    SApp h a b -> (.$) <$> f a <*> f b
    SLam h t e -> newVar >>= \i -> lam i "\\" ("->") (vpar h) <$> f t <*> addVar i (f e)
    SPi Visible t e | not (usedS 0 e) -> arr ("->") <$> f t <*> addVar "?" (f e)
    SPi h t e -> newVar >>= \i -> lam i "" ("->") (vpar h) <$> f t <*> addVar i (f e)
    SGlobal s -> pure $ atom s
    SAnn a b -> sann <$> f a <*> f b
    SInt i -> pure $ atom $ show i
    Wildcard SType -> pure $ atom "_"
    Wildcard t -> sann (atom "_") <$> f t
    STyped e -> showExp e
    x -> error $ "showSExp: " ++ show x 
  where
    f = showSExp
    ff x [] = x
    ff x (y:ys) = ff (x .$ y) ys
    atom s = (0, s)
    lam i s s' p (_, s1) (_, s2) = (1, s ++ p (i ++ " :: " ++ s1) ++ " " ++ s' ++ " " ++ s2)
    (i, x) .$ (j, y) = (2, par (i == 1 || i > 2) x ++ " " ++ par (j == 1 || j >= 2) y)
    sann (i, x) (j, y) = (5, par (i == 1 || i >= 5) x ++ " :: " ++ par (j == 1 || j >= 5) y)
    arr s (i, x) (j, y) = (3, par (i == 1 || i >= 3) x ++ " " ++ s ++ " " ++ par (j == 1 || j > 3) y)
    (i, x) `cstr` (j, y) = (4, par (i == 1 || i >= 4) x ++ " ~ " ++ par (j == 1 || j >= 4) y)

ind' i xs | i < length xs && i >= 0 = xs !! i
ind' i _ = "V" ++ show i

vpar Hidden = brace True
vpar Visible = par True
cpar True s = "<" ++ s ++ ">"
cpar False s = s
par True s = "(" ++ s ++ ")"
par False s = s
brace True s = "{" ++ s ++ "}"
brace False s = s
{-
0: atom
1: lam, pi
2: app
3: ->
4: ~
5: ::
-}

-------------------------------------------------------------------------------- main

id_test = slam $ SVar 0
id_test' = slam $ sapp id_test $ SVar 0
id_test'' = sapp id_test id_test
const_test = slam $ slam $ SVar 1

test xx = putStrLn $ length s `seq` ("result:\n" ++ s)
    where x = infer env xx
          s = ppshow'' (EEnd env) x

test' n = test $ iterate (\x -> sapp x (slam $ SVar 0)) (slam $ SVar 0) !! n
test'' n = test $ iterate (\x -> sapp (slam $ SVar 0) x) (slam $ SVar 0) !! n

tr = False
debug = False--False --True--tr
debug2 = False
debug_light = True --False
trace' = trace --const id
traceShow' = const id

parse s = 
    case P.runParser (whiteSpace lang >> {-many (parseStmt_ []-}parseITerm 0 [] >>= \ x -> eof >> return x) 0 "<interactive>" s of
      Left e -> error $ show e
      Right stmts -> do
        test stmts --runExceptT $ flip evalStateT (tenv, 0) $ mapM_ handleStmt stmts >> m

main = do
    let f = "prelude.inf"
    s <- readFile f 
    case P.runParser (whiteSpace lang >> many (parseStmt_ []) >>= \ x -> eof >> return x) 0 f s of
      Left e -> error $ show e
      Right stmts -> do
        x <- runExceptT $ flip evalStateT (env, 0) $ mapM_ handleStmt stmts
        case x of
            Left e -> putStrLn e
            Right x -> print x

-------------------------------------------------------------------------------- utils

dropNth i xs = take i xs ++ drop (i+1) xs


