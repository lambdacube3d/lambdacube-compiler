{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}

import Data.Monoid
import Data.Maybe
import Data.List
import Data.Char
import Data.String
import qualified Data.Map as Map

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Identity
import Control.Arrow
import Control.Applicative hiding ((<|>), many, optional)

import Text.Parsec hiding (parse, label, Empty, State)
import qualified Text.Parsec as P
import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec.Pos as P
import qualified Text.Parsec.Indentation.Char as I
import qualified Text.Parsec.Indentation.Token as I
import Text.Parsec.Indentation as I hiding (Any)
--import Text.Show.Pretty (ppShow)

import System.Console.Readline
import System.Environment
import Debug.Trace

-------------------------------------------------------------------------------- source data

type SName = String

data Stmt
    = Let SName SExp
    | Data SName [(Visibility, SExp)]{-parameters-} SExp{-type-} [(SName, SExp)]{-constructor names and types-}
    | Primitive SName SExp{-type-}
    deriving (Show, Read)

data SExp
    = SGlobal SName
    | SBind Binder SExp SExp
    | SApp Visibility SExp SExp
    | STyped Exp
  deriving (Eq, Show, Read)

data Binder
    = BPi  Visibility
    | BLam Visibility
    | BMeta      -- a metavariable is like a floating hidden lambda
  deriving (Eq, Show, Read)

data Visibility = Hidden | Visible
  deriving (Eq, Show, Read)

pattern SLit a = STyped (ELit a)
pattern SVar a = STyped (Var a)
pattern SPi  h a b = SBind (BPi  h) a b
pattern SLam h a b = SBind (BLam h) a b
pattern SType = SGlobal "Type"
pattern Wildcard t = SBind BMeta t (SVar 0)
pattern SAppV a b = SApp Visible a b
pattern SAnn a b = SAppV (SAppV (STyped (Lam Visible Type (Lam Visible (Var 0) (Var 0)))) b) a
pattern TyType a = SAppV (STyped (Lam Visible Type (Var 0))) a
pattern CheckSame' a b c = SGlobal "checkSame" `SAppV` STyped a `SAppV` STyped b `SAppV` c

isPi (BPi _) = True
isPi _ = False

-------------------------------------------------------------------------------- destination data

data Exp
    = Bind Binder Exp Exp
    | Prim FunName [Exp]
    | Var  !Int                 -- De Bruijn variable
    | CLet !Int Exp Exp         -- De Bruijn index decreasing let only for metavariables (non-recursive)
    | Label SName [Exp] Exp
  deriving (Show, Read)

data FunName
    = ConName SName Int{-free arity-}
    | CLit Lit
    | FunName SName
  deriving (Eq, Show, Read)

data Lit
    = LInt !Int
    | LChar Char
  deriving (Eq, Show, Read)

pattern Lam h a b = Bind (BLam h) a b
pattern Pi  h a b = Bind (BPi h) a b
pattern Meta  a b = Bind BMeta a b

pattern App a b     = Prim (FunName "app") [a, b]
pattern Cstr a b    = Prim (FunName "cstr") [a, b]
pattern Coe a b w x = Prim (FunName "coe") [a,b,w,x]

pattern ConN0 a x  <- (unLabel -> Prim (ConName a 0) x) where ConN0 a x = Prim (ConName a 0) x
pattern ConN n x   <- (unLabel -> Prim (ConName n _) x)
pattern Type        = ConN0 "Type" []
pattern Sigma a b  <- ConN0 "Sigma" [a, Lam _ _ b] where Sigma a b = ConN0 "Sigma" [a, Lam Visible a{-todo: don't duplicate-} b]
pattern Unit        = ConN0 "Unit" []
pattern TT          = ConN0 "TT" []
pattern T2 a b      = ConN0 "T2" [a, b]
pattern T2C a b    <- ConN0 "T2C" [_, _, a, b] where T2C a b = ConN0 "T2C" [error "t21", error "t22", a, b]   -- TODO
pattern Empty       = ConN0 "Empty" []
pattern TInt        = ConN0 "Int" []
pattern ELit a      = Prim (CLit a) []
pattern EInt a     <- (unLabel -> ELit (LInt a)) where EInt a = ELit (LInt a)

eBool True  = ConN0 "True'" []
eBool False = ConN0 "False'" []

-------------------------------------------------------------------------------- environments

-- SExp zippers
data Env
    = EBind2 Binder Exp Env     -- zoom into second parameter of SBind
    | EBind1 Binder Env SExp           -- zoom into first parameter of SBind
    | EApp1 Visibility Env SExp
    | EApp2 Visibility Exp Env
    | EGlobal GlobalEnv [Stmt]
    | ELet Int Exp Env
    | CheckType Exp Env
    | CheckSame Exp Env
  deriving Show

type GlobalEnv = Map.Map SName (Exp, Exp)

extractEnv = \case
    ELet _ _ x    -> extractEnv x
    EBind2 _ _ x  -> extractEnv x
    EBind1 _ x _  -> extractEnv x
    EApp2 _ _ x   -> extractEnv x
    EApp1 _ x _   -> extractEnv x
    CheckType _ x -> extractEnv x
    CheckSame _ x -> extractEnv x
    EGlobal x _   -> x

initEnv :: GlobalEnv
initEnv = Map.fromList
    [ (,) "Int"  (TInt, Type)
    , (,) "Type" (Type, Type)
    ]

type AddM m = StateT (GlobalEnv, ADTs) (ExceptT String m)
type ADTs = Map.Map SName [(SName,SExp)]

-------------------------------------------------------------------------------- low-level toolbox

unLabel (Label _ _ x) = x
unLabel x = x

label a c d = Label a c $ unLabel d

instance Eq Exp where
    Label s xs _ == Label s' xs' _ | (s, xs) == (s', xs') && length xs == length xs' {-TODO: remove check-} = True
    a == a' = unLabel a === unLabel a' where
        Bind a b c === Bind a' b' c' = (a, b, c) == (a', b', c')
        CLet a b c === CLet a' b' c' = (a, b, c) == (a', b', c')
        Prim a b === Prim a' b' = (a, b) == (a', b')
        Var a === Var a' = a == a'
        _ === _ = False

cLet :: (Int -> Exp -> Exp -> Exp) -> (Int -> Exp -> Exp -> Exp) -> Int -> Exp -> Exp -> Exp
cLet _ clet i (Var j) b | i > j = clet j (Var (i-1)) $ substE j (Var (i-1)) $ up1E i b
cLet clet _ i a b = clet i a b

handleLet i j f
    | i >  j = f (i-1) j
    | i <= j = f i (j+1)

foldS f i = \case
    SApp _ a b -> foldS f i a <> foldS f i b
    SBind _ a b -> foldS f i a <> foldS f (i+1) b
    STyped e -> foldE f i e
    x@SGlobal{} -> mempty

foldE f i = \case
    Label _ xs x -> foldE f i x  -- TODO?   -- foldMap (foldE f i) xs
    Var k -> f i k
    Bind _ a b -> foldE f i a <> foldE f (i+1) b
    Prim _ as -> foldMap (foldE f i) as
    CLet j x a -> handleLet i j $ \i' j' -> foldE f i' x <> foldE f i' a

usedS = (getAny .) . foldS ((Any .) . (==))
usedE = (getAny .) . foldE ((Any .) . (==))

mapS ff h e f = g e where
    g i = \case
        SApp v a b -> SApp v (g i a) (g i b)
        SBind k a b -> SBind k (g i a) (g (h i) b)
        STyped x -> STyped $ ff i x
        x@SGlobal{} -> x

upS__ i n = mapS (\i -> upE i n) (+1) i $ \i k -> SVar $ if k >= i then k+n else k
upS = upS__ 0 1

up1E i = \case
    Var k -> Var $ if k >= i then k+1 else k
    Bind h a b -> Bind h (up1E i a) (up1E (i+1) b)
    Prim s as  -> Prim s $ map (up1E i) as
    CLet j a b -> handleLet i j $ \i' j' -> cLet CLet CLet j' (up1E i' a) (up1E i' b)
    Label f xs x -> Label f (map (up1E i) xs) $ up1E i x

upE i n e = iterate (up1E i) e !! n

substS j x = mapS (uncurry substE) ((+1) *** up1E 0) (j, x)
            $ \(i, x) k -> case compare k i of GT -> SVar (k-1); LT -> SVar k; EQ -> STyped x

substE i x = \case
    Label s xs v -> label s (map (substE i x) xs) $ substE i x v
    Var k -> case compare k i of GT -> Var $ k - 1; LT -> Var k; EQ -> x
    Bind h a b -> Bind h (substE i x a) (substE (i+1) (up1E 0 x) b)
    Prim s as  -> eval . Prim s $ map (substE i x) as
    CLet j a b
        | j > i, Just a' <- downE i a       -> cLet CLet CLet (j-1) a' (substE i (substE (j-1) a' x) b)
        | j > i, Just x' <- downE (j-1) x   -> cLet CLet CLet (j-1) (substE i x' a) (substE i x' b)
        | j < i, Just a' <- downE (i-1) a   -> cLet CLet CLet j a' (substE (i-1) (substE j a' x) b)
        | j < i, Just x' <- downE j x       -> cLet CLet CLet j (substE (i-1) x' a) (substE (i-1) x' b)
        | j == i    -> Meta (cstr x a) $ up1E 0 b

downS t x | usedS t x = Nothing
          | otherwise = Just $ substS t (error "downS") x
downE t x | usedE t x = Nothing
          | otherwise = Just $ substE t (error "downE") x

varType :: String -> Int -> Env -> (Binder, Exp)
varType err n_ env = f n_ env where
    f n (ELet i x es)    = id *** substE i x $ f (if n < i then n else n+1) es
    f n (EBind2 b t es)  = if n == 0 then (b, up1E 0 t) else id *** up1E 0 $ f (n-1) es
    f n (EBind1 _ es _)  = f n es
    f n (EApp2 _ _ es)   = f n es
    f n (EApp1 _ es _)   = f n es
    f n (CheckType _ es) = f n es
    f n (CheckSame _ es) = f n es
    f n EGlobal{} = error $ "varType: " ++ err ++ "\n" ++ show n_ ++ "\n" ++ show env

-------------------------------------------------------------------------------- reduction

infixl 1 `app_`

app_ :: Exp -> Exp -> Exp
app_ (Lam _ _ x) a = substE 0 a x
app_ (Prim (ConName s n) xs) a
    | n <= 0 = error $ "app_: " ++ show (s, n)
    | otherwise = Prim (ConName s (n-1)) (xs ++ [a])
app_ (Label f xs e) a = label f (a: xs) $ app_ e a
app_ f a = App f a


eval = \case
    App a b -> app_ a b
    Cstr a b -> cstr a b
    Coe a b c d -> coe a b c d
-- todo: elim
    Prim p@(FunName "fix") [t, f] -> let x = {- label "primFix" [f, t, i] $ -} app_ f x in x
    Prim (FunName "natCase") [_, z, s, ConN "Succ" [x]] -> s `app_` x
    Prim (FunName "natCase") [_, z, s, ConN "Zero" []] -> z
    Prim p@(FunName "natElim") [a, z, s, ConN "Succ" [x]] -> s `app_` x `app_` (eval (Prim p [a, z, s, x]))
    Prim (FunName "natElim") [_, z, s, ConN "Zero" []] -> z
    Prim p@(FunName "finElim") [m, z, s, n, ConN "FSucc" [i, x]] -> s `app_` i `app_` x `app_` (eval (Prim p [m, z, s, i, x]))
    Prim (FunName "finElim") [m, z, s, n, ConN "FZero" [i]] -> z `app_` i
    Prim (FunName "eqCase") [_, _, f, _, _, ConN "Refl" []] -> error "eqC"
    Prim (FunName "bool'Case") [_, xf, xt, ConN "False'" []] -> xf
    Prim (FunName "bool'Case") [_, xf, xt, ConN "True'" []] -> xt
    Prim (FunName "listCase") [_, _, xn, xc, ConN "Nil'" [_]] -> xn
    Prim (FunName "listCase") [_, _, xn, xc, ConN "Cons'" [_, a, b]] -> xc `app_` a `app_` b
    Prim (FunName "primAdd") [EInt i, EInt j] -> EInt (i + j)
    Prim (FunName "primSub") [EInt i, EInt j] -> EInt (i - j)
    Prim (FunName "primMod") [EInt i, EInt j] -> EInt (i `mod` j)
    Prim (FunName "primSqrt") [EInt i] -> EInt $ round $ sqrt $ fromIntegral i
    Prim (FunName "primIntEq") [EInt i, EInt j] -> eBool (i == j)
    Prim (FunName "primIntLess") [EInt i, EInt j] -> eBool (i < j)
    Prim p@(FunName "Eq_") [ConN "List" [a]] -> eval $ Prim p [a]
    Prim (FunName "Eq_") [ConN "Int" []] -> Unit
    Prim (FunName "Monad") [ConN "IO" []] -> Unit
    x -> x

-- todo
coe _ _ TT x = x
coe a b c d = Coe a b c d

cstr = cstr__ []
  where
    cstr__ n a b = cstr_ n (unLabel a) (unLabel b)

    cstr_ _ a a' | a == a' = Unit
    cstr_ (_: ns) (downE 0 -> Just a) (downE 0 -> Just a') = cstr__ ns a a'
--    cstr_ ((t, t'): ns) (downE 0 -> Just a) a' = cstr__ ns a (Lam Visible t' a')
--    cstr_ ((t, t'): ns) a (downE 0 -> Just a') = cstr__ ns (Lam Visible t a) a'
--    cstr_ ((t, t'): ns) (downE 0 -> Just a) (App (downE 0 -> Just a') (Var 0)) = cstr__ ns a a'
--    cstr_ ((t, t'): ns) (App (downE 0 -> Just a) (Var 0)) (downE 0 -> Just a') = cstr__ ns a a'
    cstr_ ((t, t'): ns) (App (downE 0 -> Just a) (Var 0)) (App (downE 0 -> Just a') (Var 0)) = traceInj2 (a, "V0") (a', "V0") $ cstr__ ns a a'
    cstr_ ((t, t'): ns) a (App (downE 0 -> Just a') (Var 0)) = traceInj (a', "V0") a $ cstr__ ns (Lam Visible t a) a'
    cstr_ ((t, t'): ns) (App (downE 0 -> Just a) (Var 0)) a' = traceInj (a, "V0") a' $ cstr__ ns a (Lam Visible t' a')
    cstr_ ns (Bind h a b) (Bind h' a' b') | h == h' = T2 (cstr__ ns a a') (cstr__ ((a, a'): ns) b b')
    cstr_ ns (unApp -> Just (a, b)) (unApp -> Just (a', b')) = traceInj2 (a, show b) (a', show b') $ T2 (cstr__ ns a a') (cstr__ ns b b')
    cstr_ [] a@(isVar -> True) a' = Cstr a a'
    cstr_ [] a a'@(isVar -> True) = Cstr a a'
    cstr_ ns a a' = error ("!----------------------------! type error: " ++ show ns ++ "\n" ++ show a ++ "\n" ++ show a') Empty

    unApp (App a b) = Just (a, b)         -- TODO: injectivity check
    unApp (Prim (ConName a n) xs@(_:_)) = Just (Prim (ConName a (n+1)) (init xs), last xs)
    unApp _ = Nothing

    isVar Var{} = True
    isVar (App a b) = isVar a
    isVar _ = False

    traceInj2 (a, a') (b, b') c | debug && (susp a || susp b) = trace ("  inj'?  " ++ show a ++ " : " ++ a' ++ "   ----   " ++ show b ++ " : " ++ b') c
    traceInj2 _ _ c = c
    traceInj (x, y) z a | debug && susp x = trace ("  inj?  " ++ show x ++ " : " ++ y ++ "    ----    " ++ show z) a
    traceInj _ _ a = a

    susp (Prim ConName{} _) = False
    susp _ = True

cstr' h x y e = EApp2 h (coe (up1E 0 x) (up1E 0 y) (Var 0) (up1E 0 e)) . EBind2 BMeta (cstr x y)

-------------------------------------------------------------------------------- simple typing

primitiveType te = \case
    CLit (LInt _)  -> TInt
    (showPrimN -> s) -> snd $ fromMaybe (error $ "can't find " ++ s) $ Map.lookup s $ extractEnv te

expType_ te = \case
    Lam h t x -> Pi h t $ expType_ (EBind2 (BLam h) t te) x
    App f x -> app (expType_ te f) x
    Var i -> snd $ varType "C" i te
    Pi{} -> Type
    Label s ts _ -> foldl app (primitiveType te $ FunName s) $ reverse ts
    Prim t ts -> foldl app (primitiveType te t) ts
    Meta{} -> error "meta type"
    CLet{} -> error "let type"
  where
    app (Pi _ a b) x = substE 0 x b

-------------------------------------------------------------------------------- inference

inferN :: Env -> SExp -> Exp
inferN te exp = (if tr then trace ("infer: " ++ showEnvSExp te exp) else id) $ (if debug then recheck' te else id) $ case exp of
    STyped e    -> expand focus te e
    SGlobal s   -> expand focus te $ fst $ fromMaybe (error $ "can't find: " ++ s) $ Map.lookup s $ extractEnv te
    SApp  h a b -> inferN (EApp1 h te b) a
    SBind h a b -> inferN ((if h /= BMeta then CheckType Type else id) $ EBind1 h te $ (if isPi h then TyType else id) b) a

expand focus te e
    | Pi Hidden a b <- expType_ te e
    = expand focus (EBind2 BMeta a te) (app_ (up1E 0 e) $ Var 0)
    | otherwise = focus te e

infixl 1 `SAppV`

checkN te x t = (if tr then trace $ "check: " ++ showEnvSExpType te x t else id) $ checkN_ te x t

checkN_ te (SLam h a b) (Pi h' x y)
    | h == h'  = if checkSame te a x then checkN (EBind2 (BLam h) x $ te) b y else error "checkN"
--checkN_ te (SApp Visible a b) t
--    = inferN (CheckType (Pi Visible (Var 3) (App (Var 2) (Var 0))) $ EBind2 BMeta (cstr (App (Var 0) (Var 1)) (upE 0 3 t)) $ EBind2 BMeta (Pi Visible (Var 1) Type) $ EApp1 Visible (EBind2 BMeta (Var 0) $ EBind2 BMeta Type te) (CheckSame' (Var 1) (Var 0) $ upS__ 0 2 b)) (upS__ 0 4 a)
checkN_ te e (Pi Hidden a b) = checkN (EBind2 (BLam Hidden) a te) (upS e) b
checkN_ te e t = inferN (CheckType t te) e

-- todo
checkSame te (Wildcard (Wildcard SType)) a = True
checkSame te (Wildcard SType) a
    | Type <- expType_ te a = True
checkSame te a b = error $ "checkSame: " ++ show (a, b)

getTyped (STyped e) = e

focus :: Env -> Exp -> Exp
focus env e = (if tr then trace $ "focus: " ++ showEnvExp env e else id) $ (if debug then recheck' env else id) $ case env of
    CheckSame x te -> focus (EBind2 BMeta (cstr x e) te) (up1E 0 e)
    EApp1 h@Visible te b
        | CheckSame' i j b' <- b -> inferN (CheckType i $ CheckSame j $ EApp2 h e te) b'
        | Pi Visible x y <- expType_ env e -> checkN (EApp2 h e te) b x
        | Pi Hidden x y  <- expType_ env e -> error "todo"
        | otherwise -> inferN (CheckType (Var 2) $ cstr' h (upE 0 2 $ expType_ env e) (Pi Visible (Var 1) (Var 1)) (upE 0 2 e) $ EBind2 BMeta Type $ EBind2 BMeta Type te) (upS__ 0 3 b)
    CheckType t te      -> expand (\te e -> focus (EBind2 BMeta (cstr t (expType_ te e)) te) $ up1E 0 e) te e
    EApp2 Visible a te  -> focus te $ app_ a e
    EBind1 h te b       -> inferN (EBind2 h e te) b
    EBind2 BMeta tt te
        | Unit <- tt    -> focus te $ substE 0 TT e
        | T2 x y <- tt -> focus (EBind2 BMeta (up1E 0 y) $ EBind2 BMeta x te) $ substE 2 (T2C (Var 1) (Var 0)) $ upE 0 2 e
        | Cstr a b <- tt, Just r <- cst a b -> r
        | Cstr a b <- tt, Just r <- cst b a -> r
        | EBind2 h@((/= BMeta) -> True) x te' <- te, Just b' <- downE 0 tt
                        -> refocus (EBind2 h (up1E 0 x) $ EBind2 BMeta b' te') (substE 2 (Var 0) $ up1E 0 e)
        | EBind1 h te' x  <- te -> refocus (EBind1 h (EBind2 BMeta tt te') $ upS__ 1 1 x) e
        | EApp1 h te' x   <- te -> refocus (EApp1 h (EBind2 BMeta tt te') $ upS x) e
        | EApp2 h x te'   <- te -> refocus (EApp2 h (up1E 0 x) $ EBind2 BMeta tt te') e
        | CheckType t te' <- te -> refocus (CheckType (up1E 0 t) $ EBind2 BMeta tt te') e
      where
        cst x = \case
            Var i | fst (varType "X" i te) == BMeta -> fmap (\x -> cLet' refocus' te i x $ substE i x $ substE 0 TT e) $ downE i x
            _ -> Nothing
    EBind2 h a te -> focus te $ Bind h a e
    ELet i b te -> case te of
        EBind2 h x te' | i > 0, Just b' <- downE 0 b
                          -> refocus' (EBind2 h (substE (i-1) b' x) (ELet (i-1) b' te')) e
        EBind1 h te' x    -> refocus' (EBind1 h (ELet i b te') $ substS (i+1) (up1E 0 b) x) e
        EApp1 h te' x     -> refocus' (EApp1 h (ELet i b te') $ substS i b x) e
        EApp2 h x te'     -> refocus' (EApp2 h (substE i b x) $ ELet i b te') e
        CheckType t te'   -> refocus' (CheckType (substE i b t) $ ELet i b te') e
        te                -> maybe (cLet' focus te i b e) (flip refocus' e) $ pull i te
      where
        pull i = \case
            EBind2 BMeta _ te | i == 0 -> Just te
            EBind2 h x te   -> EBind2 h <$> downE (i-1) x <*> pull (i-1) te
            ELet j b te     -> ELet (if j <= i then j else j-1) <$> downE i b <*> pull (if j <= i then i+1 else i) te
            _               -> Nothing
    EGlobal{} -> e
    _ -> error $ "focus: " ++ show env
  where
    cLet' f te = cLet (\i x e -> f te $ CLet i x e) (\i x e -> refocus' te $ CLet i x e)

    refocus = refocus_ focus
    refocus' = refocus_ refocus'

    refocus_ f e (Bind BMeta x a) = f (EBind2 BMeta x e) a
    refocus_ _ e (CLet i x a) = focus (ELet i x e) a
    refocus_ _ e a = focus e a

-------------------------------------------------------------------------------- debug support

recheck :: Env -> Exp -> Exp
recheck e = if debug_light then recheck' e else id

recheck' :: Env -> Exp -> Exp
recheck' e x = recheck_ (checkEnv e) x
  where
    checkEnv = \case
        e@EGlobal{} -> e
        EBind2 h t e -> EBind2 h (recheck' e t) $ checkEnv e
        EBind1 h e b -> EBind1 h (checkEnv e) b
        EApp1 h e b -> EApp1 h (checkEnv e) b
        EApp2 h a e -> EApp2 h (recheck' e a) $ checkEnv e
        ELet i x e -> ELet i (recheck' e $ up1E i x) $ checkEnv e                -- __ <i := x>
        CheckType x e -> CheckType (recheck' e x) $ checkEnv e
        CheckSame x e -> CheckSame (recheck' e x) $ checkEnv e

    recheck_ te = \case
        Var k -> Var k
        Bind h a b -> Bind h (ch (h /= BMeta) (EBind1 h te (STyped b)) a) $ ch (isPi h) (EBind2 h a te) b
        App a b -> appf (recheck'' (EApp1 Visible te (STyped b)) a) (recheck'' (EApp2 Visible a te) b)
        Label s as x -> Label s (fst $ foldl appf' ([], primitiveType te $ FunName s) $ map (recheck'' te) $ reverse as) x   -- todo: te
        Prim s as -> Prim s $ reverse $ fst $ foldl appf' ([], primitiveType te s) $ map (recheck'' te) as        -- todo: te
      where
        appf' (a, Pi h x y) (b, x')
            | x == x' = (b: a, substE 0 b y)
            | otherwise = error $ "recheck'''':\n" ++ showEnvExp te x ++ "\n" ++ showEnvExp te x' -- todo: te

        appf (a, Pi h x y) (b, x')
            | x == x' = app_ a b
            | otherwise = error $ "recheck':\n" ++ showEnvExp te (App a b)

        recheck'' te a = (b, expType_ te b) where b = recheck_ te a

        ch False te e = recheck_ te e
        ch True te e = case recheck'' te e of
            (e', Type) -> e'
            _ -> error $ "recheck'':\n" ++ showEnvExp te e

-------------------------------------------------------------------------------- statements

mkPrim True n t = Prim (ConName n (arity t)) []
mkPrim False n t = label n [] $ f t
  where
    f (Pi h a b) = Lam h a $ f b
    f _ = Prim (FunName n) $ map Var $ reverse [0..arity t - 1]

addParams ps t = foldr (uncurry SPi) t ps

getParams (SPi h t x) = ((h, t):) *** id $ getParams x
getParams x = ([], x)

getApps (SApp h a b) = id *** (b:) $ getApps a
getApps x = (x, [])

arity :: Exp -> Int
arity (Pi _ _ b) = 1 + arity b
arity _ = 0

apps a b = foldl SAppV (SGlobal a) b

replaceMetas bind = \case
    Meta a t -> bind Hidden a $ replaceMetas bind t
    t -> checkMetas t

checkMetas = \case
    x@Meta{} -> error $ "checkMetas: " ++ show x
    x@CLet{} -> error $ "checkMetas: " ++ show x
    Bind h a b -> Bind h (checkMetas a) (checkMetas b)
    Label s xs v -> Label s (map checkMetas xs) v 
    x@Prim{} -> x
    x@Var{}  -> x

getGEnv f = gets $ f . flip EGlobal mempty . fst
inferTerm t = getGEnv $ \env -> recheck env $ replaceMetas Lam $ inferN env t
inferType t = getGEnv $ \env -> recheck env $ replaceMetas Pi  $ inferN (CheckType Type env) t

addToEnv :: Monad m => String -> (Exp, Exp) -> AddM m ()
addToEnv s (x, t) = (if tr_light then trace (s ++ "  ::  " ++ showExp t) else id) $ modify $ Map.alter (Just . maybe (x, t) (const $ error $ "already defined: " ++ s)) s *** id

addToEnv_ s x = getGEnv (\env -> (x, expType_ env x)) >>= addToEnv s
addToEnv' b s t = addToEnv s (mkPrim b s t, t)

handleStmt :: MonadFix m => Stmt -> AddM m ()
handleStmt (Let n t) = inferTerm t >>= addToEnv_ n
handleStmt (Primitive s t) = inferType t >>= addToEnv' False s
handleStmt (Data s ps t_ cs) = do
    vty <- inferType $ addParams ps t_
    let
        pnum' = length $ filter ((== Visible) . fst) ps
        inum = arity vty - length ps

        downTo n m = map SVar [n+m-1, n+m-2..n]

        mkConstr j (cn, ct)
            | c == SGlobal s && take pnum' xs == downTo (0 + act) pnum'
            = do
                cty <- inferType (addParams [(Hidden, x) | (Visible, x) <- ps] ct)
                addToEnv' True cn cty
                return $ addParams (fst $ getParams $ upS__ 0 (1+j) ct)
                       $ foldl SAppV (SVar $ j + act) $ drop pnum' xs ++ [apps cn (downTo 0 acts)]
            | otherwise = throwError $ "illegal data definition (parameters are not uniform) " ++ show (c, cn, take pnum' xs, act)
          where
            (c, reverse -> xs) = getApps $ snd $ getParams ct
            act = length . fst . getParams $ ct
            acts = length . filter ((/=Hidden) . fst) . fst . getParams $ ct

        motive = addParams (replicate inum (Visible, Wildcard SType)) $
           SPi Visible (apps s $ [Wildcard $ Wildcard SType | (Visible, _) <- ps] ++ downTo 0 inum) SType

    addToEnv' True s vty
    cons <- zipWithM mkConstr [0..] cs
    addToEnv' False (caseName s) =<< inferType
        ( addParams 
            ( [(Hidden, x) | (Visible, x) <- ps]
            ++ (Visible, motive)
            : map ((,) Visible) cons
            ++ replicate (1 + inum) (Visible, Wildcard SType)
            )
        $ foldl SAppV (SVar $ length cs + inum + 1) $ downTo 1 inum ++ [SVar 0]
        )

caseName s = lower s ++ "Case"
 where lower (c:cs) = toLower c: cs

-------------------------------------------------------------------------------- parser

type Pars = ParsecT (I.IndentStream (I.CharIndentStream String)) SourcePos (State ADTs)

lang :: GenTokenParser (I.IndentStream (I.CharIndentStream String)) SourcePos (State ADTs)
lang = I.makeTokenParser $ I.makeIndentLanguageDef style
  where
    style = LanguageDef
        { commentStart   = "{-"
        , commentEnd     = "-}"
        , commentLine    = "--"
        , nestedComments = True
        , identStart     = letter <|> P.char '_'
        , identLetter    = alphaNum <|> oneOf "_'"
        , opStart        = opLetter style
        , opLetter       = oneOf ":!#$%&*+./<=>?@\\^|-~"
        , reservedOpNames= ["->", "\\", "|", "::", "<-"]
        , reservedNames  = ["forall", "data", "primitive", "_", "case", "of"]
        , caseSensitive  = True
        }

parseType mb vs = maybe id option mb $ reserved lang "::" *> parseTerm PrecLam vs
patVar = identifier lang <|> "" <$ reserved lang "_"
typedId mb vs = (,) <$> patVar <*> parseType mb vs

telescope mb vs =
    option (vs, []) $ (parens lang (f Visible) <|> braces lang (f Hidden) <|> maybe empty (\x -> flip (,) (Visible, x) <$> patVar) mb) >>=
        \(x, vt) -> (id *** (vt:)) <$> telescope mb (x: vs)
  where
    f v = (id *** (,) v) <$> typedId mb vs

parseStmt :: Pars Stmt
parseStmt =
     do reserved lang "primitive"
        localIndentation Gt $ do
            uncurry Primitive <$> typedId Nothing []
 <|> do reserved lang "data"
        localIndentation Gt $ do
            x <- identifier lang
            (nps, ts) <- telescope (Just SType) []
            t <- parseType (Just SType) nps
            cs <- reserved lang "=" *> sepBy (typedId (Just $ SGlobal x) nps) (reserved lang ";")
            lift $ modify $ Map.insert x cs
            return $ Data x ts t cs
 <|> do n <- (reserved lang "let" <|> return ()) *> identifier lang
        localIndentation Gt $ do
            (fe, ts) <- telescope (Just $ Wildcard SType) [n]
            t' <- reserved lang "=" *> parseTerm PrecLam fe
            return $ Let n $ maybeFix $ foldr (uncurry SLam) t' ts

maybeFix (downS 0 -> Just e) = e
maybeFix e = SAppV (SGlobal "fix'") $ SLam Visible (Wildcard SType) e

parseTerm :: Prec -> [String] -> Pars SExp
parseTerm PrecLam e =
     do (tok, f) <- (".", SPi) <$ reserved lang "forall" <|> ("->", SLam) <$ reservedOp lang "\\"
        (fe, ts) <- telescope (Just $ Wildcard SType) e
        t' <- reserved lang tok *> parseTerm PrecLam fe
        return $ foldr (uncurry f) t' ts
 <|> do x <- reserved lang "case" *> parseTerm PrecLam e
        cs <- reserved lang "of" *> sepBy1 (parseClause e) (reserved lang ";")
        mkCase x cs <$> lift get
 <|> do gtc <$> lift get <*> (Alts <$> parseSomeGuards (const True) e)
 <|> do parseTerm PrecAnn e >>= \t -> option t $ SPi Visible t <$ reserved lang "->" <*> parseTerm PrecLam ("": e)
parseTerm PrecAnn e = parseTerm PrecApp e >>= \t -> option t $ SAnn t <$> parseType Nothing e
parseTerm PrecApp e = foldl1 SAppV <$> many1 (parseTerm PrecAtom e)
parseTerm PrecAtom e =
     do SLit . LInt . fromIntegral <$ P.char '#' <*> natural lang
 <|> do toNat <$> natural lang
 <|> do Wildcard (Wildcard SType) <$ reserved lang "_"
 <|> do (\x -> maybe (SGlobal x) SVar $ findIndex (== x) e) <$> identifier lang
 <|> parens lang (parseTerm PrecLam e)

parseSomeGuards f e = do
    pos <- sourceColumn <$> getPosition <* reserved lang "|"
    guard $ f pos
    (e', f) <-
         do (e', PCon p vs) <- try $ parsePat e <* reserved lang "<-"
            x <- parseTerm PrecAnn e
            return (e', \gs' gs -> GuardNode x p vs (Alts gs'): gs)
     <|> do x <- parseTerm PrecAnn e
            return (e, \gs' gs -> [GuardNode x "True'" [] $ Alts gs', GuardNode x "False'" [] $ Alts gs])
    f <$> (parseSomeGuards (> pos) e' <|> (:[]) . GuardLeaf <$ reserved lang "->" <*> parseTerm PrecLam e')
      <*> (parseSomeGuards (== pos) e <|> pure [])

parseClause e = do
    (fe, p) <- parsePat e
    (,) p <$ reserved lang "->" <*> parseTerm PrecLam fe

parsePat e = do
    i <- identifier lang
    is <- many patVar
    return (reverse is ++ e, PCon i $ map ((:[]) . const PVar) is)

mkCase :: SExp -> [(Pat, SExp)] -> ADTs -> SExp
mkCase x cs@((PCon cn _, _): _) adts = (\x -> trace (showSExp x) x) $ mkCase' t x [(length vs, e) | (cn, _) <- cns, (PCon c vs, e) <- cs, c == cn]
  where
    (t, cns) = findAdt adts cn

findAdt adts cstr = head $ [x | x@(t, csn) <- Map.toList adts, cstr `elem` map fst csn] ++ error ("mkCase: " ++ cstr ++ "\n" ++ show adts)

mkCase' :: SName -> SExp -> [(Int, SExp)] -> SExp
mkCase' t x cs = (foldl SAppV (SGlobal (caseName t) `SAppV` SLam Visible (Wildcard SType) (upS $ Wildcard SType))
    [iterate (SLam Visible (Wildcard SType)) e !! vs | (vs, e) <- cs]
    `SAppV` x)

toNat 0 = SGlobal "Zero"
toNat n = SAppV (SGlobal "Succ") $ toNat (n-1)

--------------------------------------------------------------------------------

type ParPat = [Pat]     -- parallel patterns like  v@(f -> [])@(Just x)

data Pat
    = PVar -- Int
    | PCon SName [ParPat]
    | ViewPat SExp ParPat
  deriving Show

data GuardTree
    = GuardNode SExp SName [ParPat] GuardTree -- _ <- _
    | Alts [GuardTree]          --      _ | _
    | GuardLeaf SExp            --     _ -> e
  deriving Show

alts (Alts xs) = concatMap alts xs
alts x = [x]

gtc adts t = (\x -> trace ("  !  :" ++ showSExp x) x) $ guardTreeToCases t
  where
    guardTreeToCases :: GuardTree -> SExp
    guardTreeToCases t = case alts t of
        [] -> SGlobal "undefined"
        GuardLeaf e: _ -> e
        ts@(GuardNode f s _ _: _) ->
          mkCase' t f $
            [ (n, guardTreeToCases $ Alts $ map (filterGuardTree f cn n) ts)
            | (cn, ct) <- cns
            , let n = length $ filter ((==Visible) . fst) $ fst $ getParams ct
            ]
          where
            (t, cns) = findAdt adts s

    filterGuardTree :: SExp -> SName -> Int -> GuardTree -> GuardTree
    filterGuardTree f s ns = \case
        GuardLeaf e -> GuardLeaf $ upS__ 0 ns e
        Alts ts -> Alts $ map (filterGuardTree f s ns) ts
        GuardNode f' s' ps gs
            | f /= f'   -> error "todo" --GuardNode f' s' ps $ filterGuardTree f s ns gs
            | s == s'  -> if length ps /= ns then error "fgt" else
                            gs -- todo -- filterGuardTree f s ns $ guardNodes ps gs
            | otherwise -> Alts []
{-
    guardNodes :: [(Exp, ParPat)] -> GuardTree -> GuardTree
    guardNodes [] l = l
    guardNodes ((v, ws): vs) e = guardNode v ws $ guardNodes vs e

    guardNode :: SExp -> ParPat -> GuardTree -> GuardTree
    guardNode v [] e = e
    guardNode v (w: ws) e = case w of
        PVar x -> guardNode v (subst x v ws) $ subst x v e        -- don't use let instead
--        ViewPat f p -> guardNode (ViewApp f v) p $ guardNode v ws e
--        PCon s ps' -> GuardNode v s ps' $ guardNode v ws e
-}

-------------------------------------------------------------------------------- pretty print

showExp :: Exp -> String
showExp = showDoc . expDoc

showSExp :: SExp -> String
showSExp = showDoc . sExpDoc

showEnvExp :: Env -> Exp -> String
showEnvExp e c = showDoc $ envDoc e $ epar <$> expDoc c

showEnvSExp :: Env -> SExp -> String
showEnvSExp e c = showDoc $ envDoc e $ epar <$> sExpDoc c

showEnvSExpType :: Env -> SExp -> Exp -> String
showEnvSExpType e c t = showDoc $ envDoc e $ epar <$> (shAnn False <$> sExpDoc c <**> expDoc t)
  where
    infixl 4 <**>
    (<**>) :: Doc_ (a -> b) -> Doc_ a -> Doc_ b
    a <**> b = get >>= \s -> lift $ evalStateT a s <*> evalStateT b s

showDoc :: Doc -> String
showDoc = str . flip runReader [] . flip evalStateT (flip (:) <$> iterate ('\'':) "" <*> ['a'..'z'])

type Doc_ a = StateT [String] (Reader [String]) a
type Doc = Doc_ PrecString

envDoc :: Env -> Doc -> Doc
envDoc x m = case x of
    EGlobal{}           -> m
    EBind1 h ts b       -> envDoc ts $ shLam (usedS 0 b) h m (sExpDoc b)
    EBind2 h a ts       -> envDoc ts $ shLam True h (expDoc a) m
    EApp1 Visible ts b  -> envDoc ts $ shApp <$> m <*> sExpDoc b
    EApp2 Visible (Lam Visible Type (Var 0)) ts -> envDoc ts $ shApp (shAtom "tyType") <$> m
    EApp2 Visible a ts  -> envDoc ts $ shApp <$> expDoc a <*> m
    ELet i x ts         -> envDoc ts $ shLet i (expDoc x) m
    CheckType t ts      -> envDoc ts $ shAnn False <$> m <*> expDoc t
    CheckSame t ts      -> envDoc ts $ shCstr <$> m <*> expDoc t

expDoc :: Exp -> Doc
expDoc = \case
    Var k           -> shVar k
    App a b         -> shApp <$> expDoc a <*> expDoc b
    Bind h a b      -> shLam (usedE 0 b) h (expDoc a) (expDoc b)
    Cstr a b        -> shCstr <$> expDoc a <*> expDoc b
    Prim s xs       -> foldl shApp (shAtom $ showPrimN s) <$> mapM expDoc xs
    Label s xs _    -> foldl shApp (shAtom s) <$> mapM expDoc (reverse xs)
--    Label s xs x    -> expDoc x
    CLet i x e      -> shLet i (expDoc x) (expDoc e)

sExpDoc :: SExp -> Doc
sExpDoc = \case
    SGlobal s       -> pure $ shAtom s
    SAnn a b        -> shAnn False <$> sExpDoc a <*> sExpDoc b
    TyType a        -> shApp (shAtom "tyType") <$> sExpDoc a
    SApp h a b      -> shApp <$> sExpDoc a <*> sExpDoc b
--    Wildcard t      -> shAnn True (shAtom "_") <$> sExpDoc t
    SBind h a b     -> shLam (usedS 0 b) h (sExpDoc a) (sExpDoc b)
    STyped e        -> expDoc e

showLit = \case
    LInt i -> show i
    LChar c -> show c

showPrimN :: FunName -> String
showPrimN = \case
    CLit i      -> showLit i
    ConName s _ -> s
    FunName s   -> s

shVar i = asks $ shAtom . lookupVarName where
    lookupVarName xs | i < length xs && i >= 0 = xs !! i
    lookupVarName _ = "V" ++ show i

shLet i a b = shVar i >>= \i' -> local (dropNth i) $ shLam' <$> (cpar . shLet' i' <$> a) <*> b
shLam used h a b = (gets head <* modify tail) >>= \i ->
    let lam = case h of
            BPi _ -> shArr
            _ -> shLam'
        p = case h of
            BMeta -> cpar . shAnn True (shAtom i)
            BLam h -> vpar h
            BPi h -> vpar h
        vpar Hidden = brace . shAnn True (shAtom i)
        vpar Visible = ann (shAtom i)
        ann | used = shAnn False
            | otherwise = const id
    in lam <$> (p <$> a) <*> local (i:) b

-----------------------------------------

data PrecString = PS Prec String

prec i s = PS i (s i)
str (PS _ s) = s

data Prec
    = PrecAtom      --  ( _ )  ...
    | PrecApp       --  _ _                 {left}
    | PrecArr       --  _ -> _              {right}
    | PrecEq        --  _ ~ _
    | PrecAnn       --  _ :: _              {right}
    | PrecLet       --  _ := _
    | PrecLam       --  \ _ -> _            {right} {accum}
    deriving (Eq, Ord)

lpar, rpar :: PrecString -> Prec -> String
lpar (PS i s) j = par (i >. j) s  where
    PrecLam >. i = i > PrecAtom
    i >. PrecLam = i >= PrecArr
    PrecApp >. PrecApp = False
    i >. j  = i >= j
rpar (PS i s) j = par (i >. j) s where
    PrecLam >. PrecLam = False
    PrecLam >. i = i > PrecAtom
    PrecArr >. PrecArr = False
    PrecAnn >. PrecAnn = False
    i >. j  = i >= j

par True s = "(" ++ s ++ ")"
par False s = s

shAtom = PS PrecAtom
shAnn True x y | str y == "Type" = x
shAnn simp x y = prec PrecAnn $ lpar x <> " :: " <> rpar y
shApp x y = prec PrecApp $ lpar x <> " " <> rpar y
shArr x y = prec PrecArr $ lpar x <> " -> " <> rpar y
shCstr x y = prec PrecEq $ lpar x <> " ~ " <> rpar y
shLet' x y = prec PrecLet $ lpar x <> " := " <> rpar y
shLam' x y = prec PrecLam $ "\\" <> lpar x <> " -> " <> rpar y
brace s = shAtom $ "{" <> str s <> "}"
cpar s = shAtom $ "<" <> str s <> ">"
epar s = shAtom $ "||" <> str s <> "||"

instance IsString (Prec -> String) where fromString = const

-------------------------------------------------------------------------------- main

-- TODO: te
unLabelRec te x = case unLabel' x of
    Bind a b c -> Bind a (unLabelRec te b) (unLabelRec te c)
    CLet a b c -> CLet a (unLabelRec te b) (unLabelRec te c)
    Prim a b -> Prim a (map (unLabelRec te) b)
    Var a -> Var a
  where
    unLabel' (Label s xs _) = foldl App (f t (length as)) bs
      where
        t = primitiveType te $ FunName s
        (as, bs) = splitAt (arity t) $ reverse $ map (unLabelRec te) xs
        u = arity t - length as

        f (Pi h a b) 0 = Lam h a $ f b 0
        f (Pi h a b) n = f b (n-1)
        f _ 0 = Prim (FunName s) $ map (upE 0 u) as ++ map Var (reverse [0..u - 1])
    unLabel' x = x

test xx = putStrLn $ length s `seq` ("result:\n" ++ s)
    where s = showExp $ inferN (EGlobal initEnv mempty) xx

test' n = test $ foldl1 SAppV $ replicate n $ SLam Visible (Wildcard SType) $ SVar 0
test'' n = test $ foldr1 SAppV $ replicate n $ SLam Visible (Wildcard SType) $ SVar 0

tr = False--True
tr_light = True
debug = False--True--tr
debug_light = True --False

main = do
    s <- readFile f
    case flip evalState mempty $ P.runParserT p (P.newPos "" 0 0) f $ I.mkIndentStream 0 I.infIndentation True I.Ge $ I.mkCharIndentStream s of
      Left e -> error $ show e
      Right stmts -> runExceptT (flip runStateT (initEnv, mempty) $ mapM_ handleStmt stmts) >>= \case
            Left e -> putStrLn e
            Right (x, (s, _)) -> do
                let ev = EGlobal s mempty
                let s_ = (unLabelRec ev *** unLabelRec ev) <$> s
                putStrLn "----------------------"
                s' <- Map.fromList . read <$> readFile f'
                sequence_ $ Map.elems $ Map.mapWithKey (\k -> either (\_ -> putStrLn $ "xxx: " ++ k) id) $ Map.unionWithKey check (Left <$> s') (Left <$> s_)
--                writeFile f' $ show $ Map.toList s_
                putStrLn $ show $ {- unLabelRec -} unLabel $ fst $ s Map.! "int"
  where
    check k (Left (x, t)) (Left (x', t'))
        | t /= t' = Right $ putStrLn $ "!!! type diff: " ++ k ++ "\n  old:   " ++ showExp t ++ "\n  new:   " ++ showExp t'
        | x /= x' = Right $ putStrLn $ "!!! def diff: " ++ k
        | otherwise = Right $ return ()

    f = "prelude.inf"
    f' = "prelude.elab"

    p = do
        getPosition >>= setState
        setPosition =<< flip setSourceName f <$> getPosition
        whiteSpace lang *> many parseStmt <* eof

-------------------------------------------------------------------------------- utils

dropNth i xs = take i xs ++ drop (i+1) xs
iterateN n f e = iterate f e !! n
