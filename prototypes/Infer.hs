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

-------------------------------------------------------------------------------- utils

dropNth i xs = take i xs ++ drop (i+1) xs

ind e i xs | i < length xs && i >= 0 = xs !! i
ind e a b = error $ "ind: " ++ e ++ "\n" ++ show (a, b)

-------------------------------------------------------------------------------- source data

type SName = String

data Stmt
    = Let SName SExp
    | Data SName [(Visibility, SExp)]{-parameters-} SExp{-type-} [(SName, SExp)]{-constructor names and types-}
    | Primitive SName SExp{-type-}
    deriving Show

data SExp
    = SLit Lit
    | SVar !Int
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
    | BMeta      -- a metavariable is a floating hidden lambda
    | BSigma
    | BPair
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
    | Var  !Int
    | CLet !Int Exp Exp
  deriving (Eq, Show)

data PrimName
    = PrC ConName
    | PrF FunName
  deriving (Eq, Show)

data ConName
    = ConName SName Int (Additional Exp)
    | CLit Lit
    | CType
    | CUnit | CTT
    | CEmpty
    | CT2T | CT2    -- todo: elim?
  deriving (Eq, Show)

data FunName
    = FunName SName (Additional Exp)
    | FApp
    | FCstr
    | FCoe
  deriving (Eq, Show)

pattern Lam h a b = Bind (BLam h) a b
pattern Pi  h a b = Bind (BPi h) a b
pattern Sigma a b = Bind BSigma a b
pattern Meta  a b = Bind BMeta a b

pattern App a b     = Prim (PrF FApp) [a, b]
pattern Cstr a b    = Prim (PrF FCstr) [a, b]
pattern Coe a b w x = Prim (PrF FCoe) [a,b,w,x]
pattern PrimName a <- PrF (FunName a _)
pattern PrimName' a b = PrF (FunName a (Additional b))

pattern PInt a      = PrC (CLit (LInt a))
pattern Con a i b   = PrC (ConName a i (Additional b))
pattern Prim' a b   = Prim (PrC a) b
pattern Type        = Prim' CType []
pattern Unit        = Prim' CUnit []
pattern TT          = Prim' CTT []
pattern T2T a b     = Prim' CT2T [a, b]
pattern T2 a b      = Prim' CT2 [a, b]
pattern Empty       = Prim' CEmpty []

newtype Additional a = Additional a
instance Eq (Additional a) where _ == _ = True
instance Ord (Additional a) where _ `compare` _ = EQ
instance Show (Additional a) where show a = ""

-------------------------------------------------------------------------------- environments

-- SExp zippers
data Env_ b
    = EBind Binder Exp (Env_ b)     -- zoom into second parameter of SBind
    | ELet Int Exp (Env_ b)     -- why needed?
    | EEnd b        -- TODO: remove

    -- todo: use
    | EBind1 Binder (Env_ b) SExp           -- zoom into first parameter of SBind
    | EApp1 Visibility (Env_ b) SExp
    | EApp2 Visibility Exp (Env_ b)
    | EGlobal GlobalEnv [Stmt]

    deriving (Show, Functor)

type Env = Env_ ()
pattern ENil = EEnd ()

instance Applicative Env_ where
    pure = EEnd
    a <*> b = a >>= \av -> b >>= \bv -> pure (av bv)
instance Monad Env_ where
    return = pure
    EEnd a >>= f = f a
    ELet i a x >>= f = ELet i a (x >>= f)
    EBind b a x >>= f = EBind b a (x >>= f)
instance Monoid a => Monoid (Env_ a) where
    mempty = EEnd mempty
    EEnd a `mappend` b = b
    ELet i a x `mappend` b = ELet i a (x `mappend` b)
    EBind b a x `mappend` f = EBind b a (x `mappend` f)
instance Comonad Env_ where
    extract (EBind _ _ x) = extract x
    extract (ELet _ _ x) = extract x
    extract (EEnd x) = x
    extend = error "extend env"

type EEnv = Env

-- zipper for binders; same as (,)
data Z_ b a = Z b a
    deriving (Show, Functor)

type Z = Z_ EEnv

instance Monoid a => Applicative (Z_ a) where
    pure = Z mempty
    Z e a <*> Z e' b = Z (e `mappend` e') (a b)
instance Monoid a => Monad (Z_ a) where
    return = pure
    Z e a >>= f = Z (e `mappend` e') b  where Z e' b = f a

-----------------------

type GlobalEnv = Map.Map SName Exp

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

class Transport a where
    transport :: Env -> Env -> a -> a

instance Transport SExp where
    transport base = f
      where
        f ENil = id
        f (EBind b t ev) = upS . f ev
        f (ELet j x ev) = mapS (uncurry substE) ((+1) *** up1E 0) (j, x)
            (\(i, x) k -> case compare k i of GT -> SVar (k-1); LT -> SVar k; EQ -> STyped x)
                . f ev

transportS n e = iterate upS e !! n


upS = mapS up1E (+1) 0 $ \i k -> SVar $ if k >= i then k+1 else k
mapS ff h e f = g e where
    g i = \case
        SVar k -> f i k
        SApp v a b -> SApp v (g i a) (g i b)
        SBind k a b -> SBind k (g i a) (g (h i) b)
        STyped x -> STyped $ ff i x
        x@SGlobal{} -> x
        x@SLit{} -> x

instance Transport Exp where
    transport base = f where

        up1E0 = g 0 where
            g i = \case
                Var k -> Var $ if k >= i then k+1 else k
                Bind h a b -> Bind h (g i a) (g (i+1) b)
                Prim s as  -> Prim s $ map (g i) as
                CLet j a b -> handleLet i j $ \i' j' -> CLet j' (g i' a) (g i' b)

        f ENil = id
        f (EBind b t ev) = up1E0 . f ev
        f (ELet t x ev) = g t x . f ev
          where
            g i x z = case z of
                Var k -> case compare k i of GT -> Var $ k - 1; LT -> Var k; EQ -> x
                Bind h a b -> Bind h (g i x a) (g (i+1) (up1E0 x) b)
                Prim s as  -> eval . Prim s $ map (g i x) as
                CLet j a b -> mergeLets (Meta (cstr x a) $ up1E0 b) CLet g (\i j -> g i j b) i x j a

------------abc
------------RST
------------abcRST
instance Transport EEnv where
    transport base es = snd . f where
        f ENil = (es, ENil)
        f (EBind b t ev) = (h es, h ev') where (es, ev') = f ev; h = EBind b (transport base es t)
        f (ELet j x ev)  = (h es, h ev') where (es, ev') = f ev; h = elet (unVar{-TODO-} $ transport base es $ Var j) (transport base es x)

--------abc
--------def
-----------def
transport' :: EnvEnv -> EnvEnv -> EnvEnv
transport' abc def = join abc <$ (z abc (() <$ def))

------------ABC
------------abcDEF
------------ABCDEF
concatEnv :: EEnv -> EEnv -> EEnv -> EEnv
concatEnv base as = f where
    f ENil = as
    f (EBind b t ev) = EBind b t $ f ev
    f (ELet j x ev) = elet j x $ f ev



dropEnv 0 e = e
dropEnv n (EBind _ _ es) = dropEnv (n-1) es
dropEnv n (ELet i x es) =  dropEnv (if n < i then n else n+1) es

takeEnv 0 e = ENil
takeEnv n (EBind a b es) = EBind a b $ takeEnv (n-1) es
takeEnv n (ELet i x es) = ELet i x $ takeEnv (if n < i then n else n+1) es

varType :: String -> Int -> EEnv -> (Binder, Exp)
varType err n_ env = f n_ env where
    f n (ELet i x es)  = id *** substE i x $ f (if n < i then n else n+1) es
    f 0 (EBind b t _)  = (b, upE0 1 t)
    f n (EBind _ _ es) = id *** upE0 1 $ f (n-1) es
    f n _ = error $ "varType: " ++ err ++ "\n" ++ show n_ ++ "\n" ++ show env

-------------------------------------------------------------------------------- composed functions

-----------Q
-----------_____Q
upE0 n = transport (error "base") $ iterate (EBind (error "exch") (error "exch" :: Exp)) ENil !! n

-----------xabcdQ
-----------abcdQ
downE t x | usedE t x = Nothing
          | otherwise = Just $ transport (error "base") (ELet t (error "downE" :: Exp) ENil) x 

substE a b = transport (error "base") $ ELet a b ENil

----------xabcdQ
----------abcdxQ
exch :: Int -> Exp -> Exp
exch n = transport (error "base") $ ELet (n+1) (Var 0) $ EBind (error "exch") (error "exch") ENil

----------abcdQ
----------_abcdQ
up1E n = transport (error "base") $ iterate (ELet (n+1) (Var 0) . EBind (error "exch") (error "exch")) (EBind (error "exch") (error "exch") ENil) !! n

--------------xQ
--------------abcd
--------------abcdxQ
liftS1 b a abcd s = alt
  where
    alt = transport base (ELet (unVar $ lift0 abcd'' $ Var 0) (Var 0) abcd'') s

    x = EBind b a ENil
    abcd' = transport base x abcd
    abcd'' = EBind b (transport base (concatEnv base x abcd') a) abcd'

    base = error "base"

unVar (Var i) = i

lift0 = transport (error "base")

-------------------------------------------------------------------------------- todo: review

cLam' t m te = cLam te t m   where

    cLam te t@(Prim (PrimName "Monad"){-todo-} _) e
        | Just x <- inEnv 0 t te, y <- substE 0 x e = y
--    cLam te t@(Prim (PrimName "Monad"){-todo-} _) (simkill (upE0 1 t) (EBind BMeta t: te) 0 -> Just e) = cLam te t e
    cLam te t (kill (EBind BMeta t te) 0 -> Just e) = e
    cLam te Unit (substE 0 TT -> x) = x
    cLam te (T2T x y) e
        | e' <- substE 0 (T2 (Var 1) (Var 0)) $ upE0 2 e = cLam te x $ cLam (EBind BMeta x te) (upE0 1 y) e'
    cLam te (Sigma x y) e
        | e' <- substE 0 (error "sumelem" :: Exp) $ upE0 2 e = cLam te x $ cLam (EBind BMeta x te) y e'
    cLam te (Cstr a b) y
        | Just i <- cst te a, Just j <- cst te b, i < j, Just e <- downE i b, x <- substE (i+1) (upE0 1 e) y = CLet i e $ cunit x
        | Just i <- cst te b, Just e <- downE i a, x <- substE (i+1) (upE0 1 e) y = CLet i e $ cunit x
        | Just i <- cst te a, Just e <- downE i b, x <- substE (i+1) (upE0 1 e) y --CLet i e $ cunit x
        , (downE i -> Just ta) <- expType_ te a
        , (downE i -> Just tb) <- expType_ te b
        = CLet i e $ cunit $ substE (i+1) (upE0 1 e) y
    cLam te t e = Meta t e

    cst te = \case
        Var i | fst (varType "X" i te) == BMeta -> Just i
        _ -> Nothing

    cunit (substE 0 TT -> x) = x

    inEnv i t (EBind (isLam -> True) (similar t . upE0 (i+1) -> True) _) = Just (Var i)
    inEnv i t (EBind _ t' te) = inEnv (i+1) t te
    -- todo
    inEnv i t _ = Nothing

    isLam (BLam _) = True
    isLam BMeta = True
    isLam _ = False

    kill te i = \case
        Meta t'@(downE i -> Just t) (kill (EBind BMeta t' te) (i+1) -> Just e) -> Just $ Meta t e
        (pull te i -> Just (_, e)) -> Just e
        _ -> Nothing

    similar t@(Prim (PrimName "Monad") _) t' = t == t'
    similar t t' = False

    simkill t_ te i = \case
        Meta t@(similar t_ -> True) (substE 0 (Var i) -> e) -> Just e
        Meta (downE i -> Just t) (simkill (upE0 1 t_) (EBind BMeta t te) (i+1) -> Just e) -> Just (cLam te t e)
        x -> Nothing

    pull te i = \case
        CLet j z y
            | j == i   -> Just (z, y)
            | j > i, Just (x, e) <- pull (ELet j z te) i y   -> Just (up1E (j-1) x,  CLet (j-1) (substE i x z) e)
            | j < i, Just (x, e) <- pull (ELet j z te) (i-1) y   -> Just (up1E j x,  CLet j (substE (i-1) x z) e)     -- todo: review
        -- CLet j (Var i') y | i' == i   -- TODO
        Meta t (pull (EBind BMeta t te) (i+1) -> Just (downE 0 -> Just x, e)) -> Just (x, cLam te (substE i x t) e)
        x -> Nothing

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
--cstr (App x@(Var j) y) b@(Var i) | j /= i, Nothing <- downE i y = cstr x (Lam (expType' y) $ upE0 1 b)
cstr a@Var{} b = Cstr a b
cstr a b@Var{} = Cstr a b
--cstr (App x@Var{} y) b@Prim{} = cstr x (Lam (expType' y) $ upE0 1 b)
--cstr b@Prim{} (App x@Var{} y) = cstr (Lam (expType' y) $ upE0 1 b) x
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
    PrF FCstr   -> pi_ (error "cstrT0") $ pi_ (error "cstrT1") Type       -- todo
    PrF FCoe    -> pi_ Type $ pi_ Type $ pi_ (Cstr (Var 1) (Var 0)) $ pi_ (Var 2) (Var 2)  -- forall a b . (a ~ b) => a -> b
    Con _ _ t -> t
    PrC CUnit   -> Type
    PrC CTT     -> Unit
    PrC CEmpty  -> Type
    PrC CT2T    -> pi_ Type $ pi_ Type Type
    PrC CT2     -> pi_ Type $ pi_ Type $ T2T (Var 1) (Var 0)

expType_ te = \case
    Meta t x -> error "meta type" --Pi Hidden t <$> withItem (EBind BMeta t) (expType x)     -- todo
    Lam h t x -> Pi h t $ expType_ (EBind (BLam h) t te) x
    App f x -> app (expType_ te f) x
    Var i -> snd $ varType "C" i te
    Type -> Type
    Pi{} -> Type
    Prim t ts -> foldl app (primitiveType t) ts
    x -> error $ "expType: " ++ show x 
  where
    app (Pi _ a b) x = substE 0 x b

-------------------------------------------------------------------------------- inference

type EnvEnv = Env_ EEnv
type ZZ = Z_ EnvEnv

-------Q
-------abc
-------abcQ
z :: Transport a => Env_ EEnv -> a -> a
z e t = transport (error "base" {- TODO -}) (const () <$> e) t

--------------x
--------------abcd
---------------abcdy(5 := 0)
ls1p :: Binder -> Exp -> EnvEnv -> EnvEnv
ls1p b a abcd = ELet (unVar $ z abcd'' $ Var 0) (Var 0) abcd''
  where
    x = EBind b a $ EEnd $ extract abcd
    abcd' = transport' x abcd
    abcd'' = EBind b (z abcd' a) abcd'


recheck_ e' x = if debug then length (show $ checkInfer (join e'') x') `seq` x else x
  where
    (Z e'' x') = zoomMeta $ Z e' x

strip (Z _ x) = x

zoomMeta :: Z Exp -> ZZ Exp
zoomMeta (Z e t) = add (EEnd e) t
  where
    add env = \case
        Meta t e -> add (EBind BMeta t env) e
        CLet i t e -> add (ELet i t env) e
        e -> Z env e

--addEnv :: ZZ Exp -> Z Exp
addEnv (Z e q) = addEnv_ e q

addEnv_ :: EnvEnv -> Exp -> Z Exp
addEnv_ oe ox = addEnv oe ox
  where
    addEnv__ = addEnv_

    addEnv (EEnd x) q = Z x q
    addEnv (EBind BMeta Unit x) (downE 0 -> Just q) = addEnv__ x q
    {-
    -----------x
    -----------x((i+1) := up y)(0 := tt)
    addEnv_ te@(EBind BMeta (Cstr (Var i) (downE i -> Just y)) x) q
        | sw <- ELet 0 TT $ ELet (i+1) (upE0 1 y) $ EEnd te
        , Just (Just sw') <- simpC <$> simpC (join sw)
        = addEnv_ sw' $ z (join <$> sw) q
    -}
    addEnv (EBind BMeta t te) q = addEnv__ te $ cLam' t q $ join te
    -----------l mQ
    -----------l mv(2 := 0) Q
    -----------ml Q
    addEnv te@(EBind h@((/= BMeta) -> True) t _) (Meta tm q)
        | sw <- ELet 2 (Var 0) $ EBind h (upE0 2 t) $ EEnd $ EBind BMeta tm te
        , Just sw' <- simpC $ join sw
        = addEnv__ sw' $ z (join <$> sw) q

    addEnv te@(EBind h@((/= BMeta) -> True) _ _) (CLet i tm q)
        | Just sw' <- simpC' $ ELet i tm te
        = addEnv__ sw' q

    addEnv (EBind h t x) q = addEnv__ x $ Bind h t q
    addEnv (ELet i t x) q = addEnv__ x $ CLet i t q

simpC = maybe Nothing (\(b, x) -> if b then Just x else Nothing) . simpC_ id
simpC' = maybe Nothing (\(b, x) -> if b then Just x else Nothing) . simpC_ (const True)

simpC_ ff (ELet i j x) = elet_ i j x
  where
    elet_ i _ x | i < 0 = Nothing
    elet_ 0 _ (EBind _ _ xs) = Just (True, xs)
    elet_ i (downE 0 -> Just e) (EBind b x (elet_ (i-1) e -> Just (bb, xs))) = Just (ff bb, EBind b (substE (i-1) e x) xs)
    --elet_ i e (ELet j x xs) = mergeLets (error "ml") ELet substE (\i e -> elet i e xs) i e j x     -- TODO
    elet_ i _ (edel i -> Just x) = Just (True, x)
    elet_ i e xs = Just (False, ELet i e xs)
    --elet_ i e (EEnd x) = EEnd <$>

    fx i j = if i < j then i else i + 1
    gx i j = if i < j then j - 1 else j

    edel i x | i < 0 = Nothing
    edel 0 (EBind _ _ xs) = Just xs
    edel i (EBind b (downE (i-1) -> Just x) (edel (i-1) -> Just xs)) = Just $ EBind b x xs
    edel i (ELet j (downE i -> Just x) (edel (fx i j) -> Just xs)) = Just $ ELet (gx i j) x xs
    edel i xs = Nothing


ic env x = maybe (inferN__' $ Z ENil x) (\t -> strip $ addEnv $ checkN "orig" $ Z ENil (x, t)) where 

    checkN_' x@(Z _ (SLam Hidden _ _, Pi Hidden _ _)) = checkN_ x
    checkN_' (Z te (e, Pi Hidden a b))
        | te' <- EBind (BLam Hidden) a $ EEnd te
        = zoomMeta $ addEnv_ te' $ strip $ addEnv $ checkN "cn" $ Z (join te') (z te' e, b)
    checkN_' x = checkN_ x

    -- todo
    checkSame :: EEnv -> SExp -> Exp -> ZZ Exp
    checkSame te (Wildcard (Wildcard SType)) a = Z (EEnd te) a
    checkSame te (Wildcard SType) a = case expType_ te a of
        Type -> Z (EEnd te) a
--    checkSame a (SVar i) = clam (cstr a (Var i)) $ return $ EBind BMeta (cstr a (Var i)) (upE0 1 a)
    checkSame te a b = error $ "checkSame: " ++ show (a, b)

    checkN_ :: Z (SExp, Exp) -> ZZ Exp
    checkN_ (Z te (SLam h a b, Pi h' x y))
        | h /= h' = error "check lam"
        | Z te' x' <- checkSame te a x
        , tee <- ls1p (BLam h) x te'
        , te_'' <- EBind (BLam h) x' te'
        = zoomMeta $ addEnv_ te_'' $ strip $ addEnv $ checkN "se" $ Z (join te_'') (z tee b, z tee y)
    checkN_ (Z te (e, t))
        | Z te' (e', t') <- inferN $ Z te e
        , te'' <- EBind BMeta (cstr (z te' t) t') $ EEnd te'
        = zoomMeta $ addEnv_ (join te'') $ z (join <$> te'') e'

    checkN err x@(Z te (e, t)) = (if tr then trace ("check " ++ err ++ " beg: " ++ ppshow' te e (Just t) Nothing) $ trace ("check " ++ err ++ ": " ++ ppshow' te e (Just t) (Just r)) else id) res
      where
        r = strip $ addEnv res
        res@(Z ee xx) = checkN_' x

    inferN :: Z SExp -> ZZ (Exp, Exp)
    inferN (Z te x)
        | Z te' x' <- inferN_ (Z te x)
        = Z te' (x', expType_ (join te') x')

    inferN_ :: Z SExp -> ZZ Exp
    inferN_ x@(Z e s) = zoomMeta $ Z e $ inferN__' x

    inferN__' x@(Z e s) = (if tr then trace ("infer beg: " ++ ppshowS'' e s) $ trace ("infer: " ++ ppshow' e s Nothing (Just inf)) $ recheck_ e else id) $ inf
      where
        inf = inferN__ x

    inferN__ :: Z SExp -> Exp
    inferN__ (Z te exp) = case exp of
        SInt i  -> Prim (PInt i) []
        STyped e -> expand' $ Z te e
        SVar i -> expand' $ Z te $ Var i
        SGlobal s -> fromMaybe (error "can't found") $ Map.lookup s env
        SApp Visible a b
            | Z te' (a', Pi Visible x y) <- inferN $ Z te a
            , Z te'' b' <- checkN "app" $ Z (join te') (z te' b, x)
            -> strip $ addEnv_ te' $ strip $ addEnv_ te'' $ app_ (z te'' a') b'
            | Z te' (a', ta) <- inferN $ Z te a
            , Z te'' (b', tb) <- inferN $ Z (join te') (z te' b)
            , tes <- EBind BMeta Type $ EEnd te''
            , te''' <- EBind BMeta (cstr (z (join tes) ta) (Pi Visible (z (join <$> tes) tb) (Var 1))) tes
            , ap <- app_ (coe (z (join te''') ta) (Pi Visible (z (join <$> te''') tb) (Var 2)) (Var 0) (z (join te''') a')) (z (join <$> te''') b')
            -> strip $ addEnv_ te' $ strip $ addEnv_ (join te''') ap
        SBind h a b
            | Z te' a' <- if inferTy h then inferN_ $ Z te a else checkN "lam" $ Z te (a, Type)
            , te_'' <- EBind h a' te'
            , te'' <- ls1p h (error "a or a'") te'
            -> strip $ addEnv_ te_'' $ (if inferParam h then inferN__ else strip . addEnv . checkN "lam" . fmap (flip (,) Type)) $ Z (join te_'') $ z te'' b
        x -> error $ "inferN: " ++ show x
      where
        inferTy = \case
            BMeta -> True
            _ -> False
        inferParam = \case
            BMeta  -> True -- hard?
            BLam _ -> True
            _ -> False

    expand' (Z te e) = apps 0 e $ expType_ te e where
        apps n e = \case
            Pi Hidden a b -> Meta a $ apps (n+1) (upE0 1 e) b
            -- Var ???
            _ -> foldl app_ e $ map Var [n-1, n-2 .. 0]

-------------------------------------------------------------------------------- debug support

add (Meta t e) env = add e (EBind BMeta t env)
add (CLet i t e) env = add e (ELet i t env)
add e env = (env, e)

evv (env, e) y = sum [case t of Type -> 1; _ -> error $ "evv: " ++ ppshow'' e x ++ "\n"  ++ ppshow'' e t | (e, x, t) <- checkEnv env] `seq` 
    (length $ show $ checkInfer env e) `seq` y

checkEnv ENil = []
checkEnv (EBind _ t e) = (e, t, checkInfer e t): checkEnv e
checkEnv (ELet i t e) = (e, t', checkInfer e (checkInfer e t')): checkEnv e  where t' = up1E i t

recheck :: Exp -> Exp
recheck e = length (show $ checkInfer te e') `seq` e  where (te, e') = add e ENil

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

infer' t = gets $ (\env -> (if debug_light then recheck else id) $ ic env t Nothing) . fst
checkP t e = gets $ (\env -> ic env e (Just t)) . fst

expType'' :: Exp -> String
expType'' e = ppshow'' env $ expType_ env e'
  where
    (env, e') = add e ENil

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

ppshow'' :: EEnv -> Exp -> String
ppshow'' e c = flip runReader [] . flip evalStateT vars $ showEnv e $ (\(_, s') -> "   " ++ s') <$> showExp c

ppshowS'' :: EEnv -> SExp -> String
ppshowS'' e c = flip runReader [] . flip evalStateT vars $ showEnv e $ (\(_, s') -> "   " ++ s') <$> showSExp c

ppshow' e s t c = flip runReader [] . flip evalStateT vars $ showEnv e $ (\(_, s) mt me -> "\n    " ++ s ++ maybe "" (\(_, t) -> "   ::  " ++ t) mt ++ maybe "" (\(_, s') -> "\n    " ++ s') me) <$> showSExp s <**> traverse showExp t <**> traverse showExp c

showEnv :: EEnv -> StateT [String] (Reader [String]) String -> StateT [String] (Reader [String]) String
showEnv = f
  where
    f x m = case x of
        ENil -> m
        (EBind BMeta Type ts) -> f ts $ newVar >>= \i -> ((cpar True i ++ " -> ") ++) <$> addVar i m
        (EBind b t ts) -> f ts $ newVar >>= \i -> lam i (ff b) <$> showExp t <*> addVar i m
        (ELet i t ts) -> f ts $ asks (ind "showEnv" i) >>= \i' -> local (dropNth i) $ lam i' ("", "->", ":=", cpar True) <$> showExp t <*> m

    lam i (s, s', s'', p) (_, s1) s2 = s ++ p (i ++ " " ++ s'' ++ " " ++ s1) ++ " " ++ s' ++ " " ++ s2
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
    Sigma t e -> newVar >>= \i -> lam i "" ("x") "::" (par True) <$> f t <*> addVar i (f e)
    Pi Visible t e | not (usedE 0 e) -> arr ("->") <$> f t <*> addVar "?" (f e)
    Pi h t e -> newVar >>= \i -> lam i "" ("->") "::" (vpar h) <$> f t <*> addVar i (f e)
    Prim s xs -> ff (atom $ sh s) <$> mapM f xs
    CLet i t ts -> asks (ind "showEnv" i) >>= \i' -> local (dropNth i) $ lam i' "" "->" ":=" (cpar True) <$> f t <*> f ts
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

test xx = putStrLn $ "result:\n" ++ ppshow'' ENil x ++ "\n" ++ ppshow'' ENil x 
    where x = ic env xx Nothing

test' n = test $ iterate (\x -> sapp x (slam $ SVar 0)) (slam $ SVar 0) !! n
test'' n = test $ iterate (\x -> sapp (slam $ SVar 0) x) (slam $ SVar 0) !! n

tr = False--False
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

