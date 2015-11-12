{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor #-}

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
import Control.Exception hiding (try)

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
import System.IO.Unsafe

-------------------------------------------------------------------------------- source data

type SName = String

data Stmt
    = TypeAnn SName SExp            -- intermediate
    | Let SName (Maybe SExp) SExp
    | Data SName [(Visibility, SExp)]{-parameters-} SExp{-type-} [(SName, SExp)]{-constructor names and types-}
    | Primitive Bool{-True: constructor; False: function-} SName SExp{-type-}
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
pattern SType  = STyped Type
pattern SPi  h a b = SBind (BPi  h) a b
pattern SLam h a b = SBind (BLam h) a b
pattern Wildcard t = SBind BMeta t (SVar 0)
pattern SAppV a b = SApp Visible a b
pattern SAnn a t = SAppV (SAppV (STyped (Lam Visible Type (Lam Visible (Var 0) (Var 0)))) t) a      --  a :: t      ~~>   id t a
pattern TyType a = SAppV (STyped (Lam Visible Type (Var 0))) a          -- same as  (a :: Type)     --  a :: Type   ~~>   (\(x :: Type) -> x) a
pattern CheckSame' a b c = SGlobal "checkSame" `SAppV` STyped a `SAppV` STyped b `SAppV` c
pattern SCstr a b = SAppV (SAppV (SGlobal "cstr") a) b          --    a ~ b

isPi (BPi _) = True
isPi _ = False

infixl 1 `SAppV`, `App`

-------------------------------------------------------------------------------- destination data

data Exp
    = Bind Binder Exp Exp
    | Prim PrimName [Exp]
    | Var  !Int                 -- De Bruijn variable
    | Assign !Int Exp Exp       -- De Bruijn index decreasing assign operator, only for metavariables (non-recursive)
    | Label SName{-function name-} [Exp]{-reverse ordered arguments-} Exp{-reduced expression-}
  deriving (Show, Read)

data PrimName
    = ConName SName
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

pattern ConN n x    = Prim (ConName n) x
pattern Type        = ConN "Type" []
pattern Sigma a b  <- ConN "Sigma" [a, Lam _ _ b] where Sigma a b = ConN "Sigma" [a, Lam Visible a{-todo: don't duplicate-} b]
pattern Unit        = ConN "Unit" []
pattern TT          = ConN "TT" []
pattern T2 a b      = ConN "T2" [a, b]
pattern T2C a b    <- ConN "T2C" [_, _, a, b] where T2C a b = ConN "T2C" [error "t21", error "t22", a, b]   -- TODO
pattern Empty       = ConN "Empty" []
pattern TInt        = ConN "Int" []
pattern ELit a      = Prim (CLit a) []
pattern EInt a      = ELit (LInt a)

eBool True  = ConN "True'" []
eBool False = ConN "False'" []

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
    | CheckAppType Visibility Exp Env SExp
  deriving Show

--pattern CheckAppType h t te b = EApp1 h (CheckType t te) b

type GlobalEnv = Map.Map SName (Exp, Exp)

extractEnv :: Env -> GlobalEnv
extractEnv = either id extractEnv . parent

parent = \case
    ELet _ _ x           -> Right x
    EBind2 _ _ x         -> Right x
    EBind1 _ x _         -> Right x
    EApp2 _ _ x          -> Right x
    EApp1 _ x _          -> Right x
    CheckType _ x        -> Right x
    CheckSame _ x        -> Right x
    CheckAppType _ _ x _ -> Right x
    EGlobal x _          -> Left x


initEnv :: GlobalEnv
initEnv = Map.fromList
    [ (,) "Type" (Type, Type)
    ]

-- monad used during elaborating statments -- TODO: use zippers instead
type ElabStmtM m = StateT GlobalEnv (ExceptT String m)

-------------------------------------------------------------------------------- low-level toolbox

--label a@"fix" c d = Label a c d                 -- todo: review
--label a c (Label "fix" _ d) = Label a c d
label a c d | labellable d = Label a c d
label a _ d = {-trace ("lost label: " ++ a ++ "; " ++ show' d) -} d
  where
    show' (Var _) = "v"
    show' (Bind _ _ _) = "b"
    show' (Prim x _) = "p " ++ show x
    show' (Label _ _ _) = "l"

labellable (Lam _ _ _) = True
labellable (Prim (FunName f) _) = labellableName f
labellable _ = False

labellableName (FixName _) = True
labellableName (Case _) = True
labellableName n = n `elem` ["matchInt", "matchList"] --False

unLabel (Label _ _ x) = x
unLabel x = x

pattern UnLabel a <- (unLabel -> a) where UnLabel a = a
--pattern UPrim a b = UnLabel (Prim a b)
pattern UBind a b c = {-UnLabel-} (Bind a b c)      -- todo: review
pattern UApp a b = {-UnLabel-} (App a b)            -- todo: review
pattern UVar n = Var n

instance Eq Exp where
    Label s xs _ == Label s' xs' _ = (s, xs) == (s', xs') && length xs == length xs' {-TODO: remove check-}
    Bind a b c == Bind a' b' c' = (a, b, c) == (a', b', c')
    Assign a b c == Assign a' b' c' = (a, b, c) == (a', b', c')
    Prim a b == Prim a' b' = (a, b) == (a', b')
    Var a == Var a' = a == a'
    _ == _ = False

cLet :: (Int -> Exp -> Exp -> Exp) -> (Int -> Exp -> Exp -> Exp) -> Int -> Exp -> Exp -> Exp
cLet _ clet i (Var j) b | i > j = clet j (Var (i-1)) $ substE j (Var (i-1)) $ up1E i b
cLet clet _ i a b = clet i a b

handleLet i j f
    | i >  j = f (i-1) j
    | i <= j = f i (j+1)

foldS g f i = \case
    SApp _ a b -> foldS g f i a <> foldS g f i b
    SBind _ a b -> foldS g f i a <> foldS g f (i+1) b
    STyped e -> foldE f i e
    SGlobal (FixName _) -> g i "fix"
    SGlobal x -> g i x

foldE f i = \case
    Label _ xs _ -> foldMap (foldE f i) xs
    Var k -> f i k
    Bind _ a b -> foldE f i a <> foldE f (i+1) b
    Prim _ as -> foldMap (foldE f i) as
    Assign j x a -> handleLet i j $ \i' j' -> foldE f i' x <> foldE f i' a

freeS = nub . foldS (\_ s -> [s]) mempty 0
usedS = (getAny .) . foldS mempty ((Any .) . (==))
usedE = (getAny .) . foldE ((Any .) . (==))

mapS = mapS_ (const SGlobal)
mapS_ gg ff h e = g e where
    g i = \case
        SApp v a b -> SApp v (g i a) (g i b)
        SBind k a b -> SBind k (g i a) (g (h i) b)
        STyped x -> STyped $ ff i x
        SGlobal x -> gg i x

upS__ i n = mapS (\i -> upE i n) (+1) i
upS = upS__ 0 1

up1E i = \case
    Var k -> Var $ if k >= i then k+1 else k
    Bind h a b -> Bind h (up1E i a) (up1E (i+1) b)
    Prim s as  -> Prim s $ map (up1E i) as
    Assign j a b -> handleLet i j $ \i' j' -> cLet Assign Assign j' (up1E i' a) (up1E i' b)
    Label f xs x -> Label f (map (up1E i) xs) $ up1E i x

upE i n e = iterate (up1E i) e !! n

substS j x = mapS (uncurry substE) ((+1) *** up1E 0) (j, x)
substSG j x = mapS_ (\x i -> if i == j then STyped x else SGlobal i) (const id) (up1E 0) x

substE i x = \case
    Label s xs v -> label s (map (substE i x) xs) $ substE i x v
    Var k -> case compare k i of GT -> Var $ k - 1; LT -> Var k; EQ -> x
    Bind h a b -> Bind h (substE i x a) (substE (i+1) (up1E 0 x) b)
    Prim s as  -> eval . Prim s $ map (substE i x) as
    Assign j a b
        | j > i, Just a' <- downE i a       -> cLet Assign Assign (j-1) a' (substE i (substE (j-1) a' x) b)
        | j > i, Just x' <- downE (j-1) x   -> cLet Assign Assign (j-1) (substE i x' a) (substE i x' b)
        | j < i, Just a' <- downE (i-1) a   -> cLet Assign Assign j a' (substE (i-1) (substE j a' x) b)
        | j < i, Just x' <- downE j x       -> cLet Assign Assign j (substE (i-1) x' a) (substE (i-1) x' b)
        | j == i    -> Meta (cstr x a) $ up1E 0 b

downS t x | usedS t x = Nothing
          | otherwise = Just $ substS t (error "downS") x
downE t x | usedE t x = Nothing
          | otherwise = Just $ substE t (error "downE") x

varType :: String -> Int -> Env -> (Binder, Exp)
varType err n_ env = f n_ env where
    f n (ELet i x es)    = id *** substE i x $ f (if n < i then n else n+1) es
    f n (EBind2 b t es)  = if n == 0 then (b, up1E 0 t) else id *** up1E 0 $ f (n-1) es
    f n e = either (error $ "varType: " ++ err ++ "\n" ++ show n_ ++ "\n" ++ show env) (f n) $ parent e

-------------------------------------------------------------------------------- reduction

infixl 1 `app_`

app_ :: Exp -> Exp -> Exp
app_ (Lam _ _ x) a = substE 0 a x
app_ (Prim (ConName s) xs) a = Prim (ConName s) (xs ++ [a])
app_ (Label f xs e) a = label f (a: xs) $ app_ e a
app_ f a = App f a

eval = \case
    App a b -> app_ a b
    Cstr a b -> cstr a b
    Coe a b c d -> coe a b c d
-- todo: elim
    Prim p@(FunName (FixName n)) [t, f] -> let x = {- label n [] $ -} app_ f x in {-Label "fix" [f, t]-} x  -- todo: elim
    Prim (FunName (Case "Nat")) [_, z, s, ConN "Succ" [x]] -> s `app_` x
    Prim (FunName (Case "Nat")) [_, z, s, ConN "Zero" []] -> z
    Prim p@(FunName "natElim") [a, z, s, ConN "Succ" [x]] -> s `app_` x `app_` (eval (Prim p [a, z, s, x]))
    Prim (FunName "natElim") [_, z, s, ConN "Zero" []] -> z
    Prim p@(FunName "finElim") [m, z, s, n, ConN "FSucc" [i, x]] -> s `app_` i `app_` x `app_` (eval (Prim p [m, z, s, i, x]))
    Prim (FunName "finElim") [m, z, s, n, ConN "FZero" [i]] -> z `app_` i
    Prim (FunName (Case "Eq")) [_, _, f, _, _, ConN "Refl" []] -> error "eqC"
    Prim (FunName (Case "Bool'")) [_, xf, xt, ConN "False'" []] -> xf
    Prim (FunName (Case "Bool'")) [_, xf, xt, ConN "True'" []] -> xt
    Prim (FunName (Case "List")) [_, _, xn, xc, ConN "Nil'" [_]] -> xn
    Prim (FunName (Case "List")) [_, _, xn, xc, ConN "Cons'" [_, a, b]] -> xc `app_` a `app_` b
    Prim (FunName "primAdd") [EInt i, EInt j] -> EInt (i + j)
    Prim (FunName "primSub") [EInt i, EInt j] -> EInt (i - j)
    Prim (FunName "primMod") [EInt i, EInt j] -> EInt (i `mod` j)
    Prim (FunName "primSqrt") [EInt i] -> EInt $ round $ sqrt $ fromIntegral i
    Prim (FunName "primIntEq") [EInt i, EInt j] -> eBool (i == j)
    Prim (FunName "primIntLess") [EInt i, EInt j] -> eBool (i < j)
    Prim (FunName "matchInt") [t, f, ConN "Int" []] -> t
    Prim (FunName "matchInt") [t, f, c@(ConN _ _)] -> f `app_` c
    Prim (FunName "matchList") [t, f, ConN "List" [a]] -> t `app_` a
    Prim (FunName "matchList") [t, f, c@(ConN _ _)] -> f `app_` c
    Prim p@(FunName "Eq_") [ConN "List" [a]] -> eval $ Prim p [a]
    Prim (FunName "Eq_") [ConN "Int" []] -> Unit
    Prim (FunName "Eq_") [ConN _ _] -> Empty
    Prim (FunName "Monad") [ConN "IO" []] -> Unit
    Prim (FunName "Num") [ConN "Float" []] -> Unit
    x -> x

-- todo
coe _ _ TT x = x
coe a b c d = Coe a b c d

cstr = cstr__ []
  where
    cstr__ = cstr_

    cstr_ _ a a' | a == a' = Unit
    cstr_ (_: ns) (downE 0 -> Just a) (downE 0 -> Just a') = cstr__ ns a a'
--    cstr_ ((t, t'): ns) (downE 0 -> Just a) a' = cstr__ ns a (Lam Visible t' a')
--    cstr_ ((t, t'): ns) a (downE 0 -> Just a') = cstr__ ns (Lam Visible t a) a'
--    cstr_ ((t, t'): ns) (downE 0 -> Just a) (App (downE 0 -> Just a') (Var 0)) = cstr__ ns a a'
--    cstr_ ((t, t'): ns) (App (downE 0 -> Just a) (Var 0)) (downE 0 -> Just a') = cstr__ ns a a'
    cstr_ ((t, t'): ns) (UApp (downE 0 -> Just a) (UVar 0)) (UApp (downE 0 -> Just a') (UVar 0)) = traceInj2 (a, "V0") (a', "V0") $ cstr__ ns a a'
    cstr_ ((t, t'): ns) a (UApp (downE 0 -> Just a') (UVar 0)) = traceInj (a', "V0") a $ cstr__ ns (Lam Visible t a) a'
    cstr_ ((t, t'): ns) (UApp (downE 0 -> Just a) (UVar 0)) a' = traceInj (a, "V0") a' $ cstr__ ns a (Lam Visible t' a')
    cstr_ ns (UBind h a b) (UBind h' a' b') | h == h' = T2 (cstr__ ns a a') (cstr__ ((a, a'): ns) b b')
    cstr_ ns (unApp -> Just (a, b)) (unApp -> Just (a', b')) = traceInj2 (a, show b) (a', show b') $ T2 (cstr__ ns a a') (cstr__ ns b b')
    cstr_ ns (Prim (FunName "VecScalar") [a, b]) (Prim (FunName "VecScalar") [a', b']) = T2 (cstr__ ns a a') (cstr__ ns b b')
    cstr_ ns (Prim (FunName "VecScalar") [a, b]) (Prim (ConName "Vec") [a', b']) = T2 (cstr__ ns a a') (cstr__ ns b b')
    cstr_ ns (Prim (ConName "FrameBuffer") [a, b]) (Prim (FunName "TFFrameBuffer") [Prim (ConName "Image") [a', b']]) = T2 (cstr__ ns a a') (cstr__ ns b b')
    cstr_ [] a@(Prim ConName{} _) a'@(Prim FunName{} _) = Cstr a a'
    cstr_ [] a@(Prim FunName{} _) a'@(Prim ConName{} _) = Cstr a a'
    cstr_ [] a a' | isVar a || isVar a' = Cstr a a'
    cstr_ ns a a' = error ("!----------------------------! type error: " ++ show ns ++ "\n" ++ show a ++ "\n" ++ show a') Empty

    unApp (UApp a b) = Just (a, b)         -- TODO: injectivity check
    unApp (Prim (ConName a) xs@(_:_)) = Just (Prim (ConName a) (init xs), last xs)
    unApp _ = Nothing

    isVar UVar{} = True
    isVar (UApp a b) = isVar a
    isVar _ = False

    traceInj2 (a, a') (b, b') c | debug && (susp a || susp b) = trace_ ("  inj'?  " ++ show a ++ " : " ++ a' ++ "   ----   " ++ show b ++ " : " ++ b') c
    traceInj2 _ _ c = c
    traceInj (x, y) z a | debug && susp x = trace_ ("  inj?  " ++ show x ++ " : " ++ y ++ "    ----    " ++ show z) a
    traceInj _ _ a = a

    susp (Prim ConName{} _) = False
    susp _ = True

cstr' h x y e = EApp2 h (coe (up1E 0 x) (up1E 0 y) (Var 0) (up1E 0 e)) . EBind2 BMeta (cstr x y)

-------------------------------------------------------------------------------- simple typing

primitiveType te = \case
    CLit (LInt _)  -> TInt
    (showPrimN -> s) -> snd $ fromMaybe (error $ "primitiveType: can't find " ++ s) $ Map.lookup s $ extractEnv te

expType_ te = \case
    Lam h t x -> Pi h t $ expType_ (EBind2 (BLam h) t te) x
    App f x -> app (expType_ te f) x
    Var i -> snd $ varType "C" i te
    Pi{} -> Type
    Label s ts _ -> foldl app (primitiveType te $ FunName s) $ reverse ts
    Prim t ts -> foldl app (primitiveType te t) ts
    Meta{} -> error "meta type"
    Assign{} -> error "let type"
  where
    app (Pi _ a b) x = substE 0 x b

-------------------------------------------------------------------------------- inference

fixDef n = Lam Hidden Type $ Lam Visible (Pi Visible (Var 0) (Var 1)) $ Prim (FunName n) [Var 1, Var 0]
fixType = Pi Hidden Type $ Pi Visible (Pi Visible (Var 0) (Var 1)) Type

inferN :: Bool{-trace flag-} -> Env -> SExp -> Exp
inferN traceflag = infer  where

    infer te exp = (if traceflag then trace_ ("infer: " ++ showEnvSExp te exp) else id) $ (if debug then recheck' te else id) $ case exp of
        STyped e    -> focus te e
        SGlobal n@(FixName _)   -> focus te $ fixDef n
    --fst $ fromMaybe (error $ "can't find: " ++ s) $ Map.lookup s $ extractEnv te
    --        where s = "fix"
        SGlobal s   -> focus te $ fst $ fromMaybe (error $ "infer: can't find: " ++ s) $ Map.lookup s $ extractEnv te
        SApp  h a b -> infer (EApp1 h te b) a
        SBind h a b -> infer ((if h /= BMeta then CheckType Type else id) $ EBind1 h te $ (if isPi h then TyType else id) b) a

    checkN te x t = (if traceflag then trace_ $ "check: " ++ showEnvSExpType te x t else id) $ checkN_ te x t

    checkN_ te e t
        | SApp h a b <- e = infer (CheckAppType h t te b) a
        | SLam h a b <- e, Pi h' x y <- t, h == h'  = if checkSame te a x then checkN (EBind2 (BLam h) x te) b y else error "checkN"
        | Pi Hidden a b <- t, notHiddenLam e = checkN (EBind2 (BLam Hidden) a te) (upS e) b
        | otherwise = infer (CheckType t te) e
      where
        -- todo
        notHiddenLam = \case
            SLam Visible _ _ -> True
            e@SGlobal{} | Lam Hidden _ _ <- infer te e -> False
                        | otherwise -> True
            _ -> False

    -- todo
    checkSame te (Wildcard (Wildcard SType)) a = True
    checkSame te (Wildcard SType) a
        | Type <- expType_ te a = True
    checkSame te a b = error $ "checkSame: " ++ show (a, b)

    hArgs (Pi Hidden _ b) = 1 + hArgs b
    hArgs _ = 0

    focus :: Env -> Exp -> Exp
    focus env e = (if traceflag then trace_ $ "focus: " ++ showEnvExp env e else id) $ (if debug then recheck' env else id) $ case env of
        CheckSame x te -> focus (EBind2 BMeta (cstr x e) te) (up1E 0 e)
        CheckAppType h t te b
            | Pi h' x (downE 0 -> Just y) <- expType_ env e, h == h' -> focus (EBind2 BMeta (cstr t y) $ EApp1 h te b) (up1E 0 e)
            | otherwise -> focus (EApp1 h (CheckType t te) b) e
        EApp1 h te b
            | Pi h' x y <- expType_ env e, h == h' -> checkN (EApp2 h e te) b x
            | Pi Hidden x y  <- expType_ env e, h == Visible -> focus (EApp1 Hidden env $ Wildcard $ Wildcard SType) e  --  e b --> e _ b
            | otherwise -> infer (CheckType (Var 2) $ cstr' h (upE 0 2 $ expType_ env e) (Pi Visible (Var 1) (Var 1)) (upE 0 2 e) $ EBind2 BMeta Type $ EBind2 BMeta Type te) (upS__ 0 3 b)
        CheckType t te
            | hArgs (expType_ te e) > hArgs t
                            -> focus (EApp1 Hidden (CheckType t te) $ Wildcard $ Wildcard SType) e
            | otherwise     -> focus (EBind2 BMeta (cstr t (expType_ te e)) te) $ up1E 0 e
        EApp2 h a te        -> focus te $ app_ a e        --  h??
        EBind1 h te b       -> infer (EBind2 h e te) b
        EBind2 BMeta tt te
            | Unit <- tt    -> refocus te $ substE 0 TT e
            | T2 x y <- tt -> focus (EBind2 BMeta (up1E 0 y) $ EBind2 BMeta x te) $ substE 2 (T2C (Var 1) (Var 0)) $ upE 0 2 e
            | Cstr a b <- tt, Just r <- cst a b -> r
            | Cstr a b <- tt, Just r <- cst b a -> r
            | EBind2 h x te' <- te, h /= BMeta, Just b' <- downE 0 tt
                            -> refocus (EBind2 h (up1E 0 x) $ EBind2 BMeta b' te') (substE 2 (Var 0) $ up1E 0 e)
            | EBind1 h te' x  <- te -> refocus (EBind1 h (EBind2 BMeta tt te') $ upS__ 1 1 x) e
            | CheckAppType h t te' x <- te -> refocus (CheckAppType h (up1E 0 t) (EBind2 BMeta tt te') $ upS x) e
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
            CheckAppType h t te' x -> refocus' (CheckAppType h (substE i b t) (ELet i b te') $ substS i b x) e
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
        cLet' f te = cLet (\i x e -> f te $ Assign i x e) (\i x e -> refocus' te $ Assign i x e)

        refocus = refocus_ focus
        refocus' = refocus_ refocus'

        refocus_ f e (Bind BMeta x a) = f (EBind2 BMeta x e) a
        refocus_ _ e (Assign i x a) = focus (ELet i x e) a
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
        CheckAppType h x e y -> CheckAppType h (recheck' e x) (checkEnv e) y

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

mkPrim True n t = Prim (ConName n) []
mkPrim False n t = f t
  where
    f (Pi h a b) = Lam h a $ f b
    f _ = Prim (FunName n) $ map Var $ reverse [0..arity t - 1]

addParams ps t = foldr (uncurry SPi) t ps

getParamsS (SPi h t x) = ((h, t):) *** id $ getParamsS x
getParamsS x = ([], x)

getApps (SApp h a b) = id *** (++ [(h, b)]) $ getApps a -- todo: make it efficient
getApps x = (x, [])

arity :: Exp -> Int
arity = length . arity_
arity_ = map fst . fst . getParams

--getParams :: Exp -> [(Visibility, Exp)]
getParams (Pi h a b) = ((h, a):) *** id $ getParams b
getParams x = ([], x)

apps a b = foldl SAppV (SGlobal a) b
apps' a b = foldl sapp (SGlobal a) b

replaceMetas bind = \case
    Meta a t -> bind Hidden a $ replaceMetas bind t
    Assign i x t -> bind Hidden (cstr (Var i) $ upE i 1 x) $ upE i 1 $ replaceMetas bind t
    t -> checkMetas t
{-
replaceMetas bind x = checkMetas $ splitMetas [] x
  where
    splitMetas ms = \case
        Meta a t
            | Just i <- elemIndex a ms -> splitMetas ms $ substE 0 (Var i) t
            | otherwise -> bind Hidden a $ splitMetas (map (up1E 0) $ a: ms) t
        t -> t
-}

checkMetas = \case
    x@Meta{} -> error $ "checkMetas: " ++ show x
    x@Assign{} -> error $ "checkMetas: " ++ show x
    Bind h a b -> Bind h (checkMetas a) (checkMetas b)
    Label s xs v -> Label s (map checkMetas xs) v 
    x@Prim{} -> x
    x@Var{}  -> x

getGEnv f = gets $ f . flip EGlobal mempty
inferTerm tr f t = getGEnv $ \env -> let env' = f env in recheck env' $ replaceMetas Lam $ smartTrace $ \tr -> 
    (\t -> if tr_light then length (showExp t) `seq` t else t) $ inferN tr env' t
inferType tr t = getGEnv $ \env -> recheck env $ replaceMetas Pi  $ inferN tr (CheckType Type env) t

smartTrace :: (Bool -> a) -> a
smartTrace f = unsafePerformIO $ catch (evaluate $ f False) $ \err -> do
    putStr $ unlines
        [ "---------------------------------"
        , showError err
        , "try again with trace"
        , "---------------------------------"
        ]
    evaluate $ f True
  where
    showError :: ErrorCall -> String
    showError = show

addToEnv :: Monad m => String -> (Exp, Exp) -> ElabStmtM m ()
addToEnv s (x, t) = (if tr_light then trace_ (s ++ "  ::  " ++ showExp t) else id) $ modify $ Map.alter (Just . maybe (x, t) (const $ error $ "already defined: " ++ s)) s


label' a b c | labellableName a = c
label' a b c = {- trace_ a $ -} label a b c

addToEnv_ s x = getGEnv (\env -> (label' s [] x, expType_ env x)) >>= addToEnv s
addToEnv_' s x x' = getGEnv (\env -> (x, traceD ("addToEnv: " ++ s ++ " = " ++ showEnvExp env (x')) $ expType_ env $ x')) >>= addToEnv s
addToEnv' b s t = addToEnv s (label' s [] $ mkPrim b s t, t)

downTo n m = map SVar [n+m-1, n+m-2..n]

--maybeFix n e = SAppV (SGlobal "f_i_x") $ SLam Visible (Wildcard SType) e
pattern FixName n = 'f': 'i': 'x': n

fiix :: SName -> Exp -> Exp
fiix n (Lam Hidden _ e) = par 0 e where
    par i (Lam Hidden k z) = Lam Hidden k $ par (i+1) z
    par i (Var i' `App` t `App` f) | i == i' = x where
        x = label n (map Var [0..i-1]) $ f `app_` x

handleStmt :: Monad m => Stmt -> ElabStmtM m ()
handleStmt (Let n mt (downS 0 -> Just t)) = inferTerm tr id (maybe id (flip SAnn) mt t) >>= addToEnv_ n
handleStmt (Let n mt t) = inferTerm tr (EBind2 BMeta fixType) (SAppV (SVar 0) $ upS $ SLam Visible (Wildcard SType) $ maybe id (flip SAnn) mt t) >>= \x -> addToEnv_' n (fiix n x) (flip app_ (fixDef "f_i_x") x)
handleStmt (Primitive con s t) = inferType tr t >>= addToEnv' con s
handleStmt (Data s ps t_ cs) = do
    vty <- inferType tr $ addParams ps t_
    let
        pnum' = length $ filter ((== Visible) . fst) ps
        inum = arity vty - length ps

        mkConstr j (cn, ct)
            | c == SGlobal s && take pnum' xs == downTo (length . fst . getParamsS $ ct) pnum'
            = do
                cty <- inferType tr (addParams [(Hidden, x) | (Visible, x) <- ps] ct)
                let     pars = zipWith (\x -> id *** STyped . upE x (1+j)) [0..] $ drop (length ps) $ fst $ getParams cty
                        act = length . fst . getParams $ cty
                        acts = map fst . fst . getParams $ cty
                addToEnv' True cn cty
                return $ addParams pars
                       $ foldl SAppV (SVar $ j + length pars) $ drop pnum' xs ++ [apps' cn (zip acts $ downTo (j+1+length pars) (length ps) ++ downTo 0 (act- length ps))]
            | otherwise = throwError $ "illegal data definition (parameters are not uniform) " -- ++ show (c, cn, take pnum' xs, act)
            where
                                        (c, map snd -> xs) = getApps $ snd $ getParamsS ct

        motive = addParams (replicate inum (Visible, Wildcard SType)) $
           SPi Visible (apps' s $ zip (map fst ps) (downTo inum $ length ps) ++ zip (map fst $ fst $ getParamsS t_) (downTo 0 inum)) SType

    addToEnv' True s vty
    cons <- zipWithM mkConstr [0..] cs
    addToEnv' False (Case s) =<< inferType tr
        ( (\x -> traceD ("type of case-elim before elaboration: " ++ showSExp x) x) $ addParams
            ( [(Hidden, x) | (_, x) <- ps]
            ++ (Visible, motive)
            : map ((,) Visible) cons
            ++ replicate inum (Hidden, Wildcard SType)
            ++ [(Visible, apps' s $ zip (map fst ps) (downTo (inum + length cs + 1) $ length ps) ++ zip (map fst $ fst $ getParamsS t_) (downTo 0 inum))]
            )
        $ foldl SAppV (SVar $ length cs + inum + 1) $ downTo 1 inum ++ [SVar 0]
        )

pattern Case s <- (splitCase -> Just s) where Case (c:cs) = toLower c: cs ++ "Case"

splitCase s
    | reverse (take 4 $ reverse s) == "Case"
    , c:cs <- reverse $ drop 4 $ reverse s
    = Just $ toUpper c: cs
    | otherwise = Nothing

-------------------------------------------------------------------------------- parser

addForalls defined x = foldl f x [v | v <- reverse $ freeS x, v `notElem` defined]
  where
    f e v = SPi Hidden (Wildcard SType) $ substSG v (Var 0) $ upS e

defined defs = ("Type":) $ flip foldMap defs $ \case
    TypeAnn x _ -> [x]
    Let x _ _ -> [x]
    Data x _ _ cs -> x: map fst cs
    Primitive _ x _ -> [x]

type Pars = ParsecT (I.IndentStream (I.CharIndentStream String)) SourcePos (State [Stmt])

lang :: GenTokenParser (I.IndentStream (I.CharIndentStream String)) SourcePos (State [Stmt])
lang = I.makeTokenParser $ I.makeIndentLanguageDef style
  where
    style = LanguageDef
        { commentStart   = "{-"
        , commentEnd     = "-}"
        , commentLine    = "--"
        , nestedComments = True
        , identStart     = letter <|> oneOf "_"
        , identLetter    = alphaNum <|> oneOf "_'"
        , opStart        = opLetter style
        , opLetter       = oneOf ":!#$%&*+./<=>?@\\^|-~"
        , reservedOpNames= ["->", "=>", "~", "\\", "|", "::", "<-", "=", "@"]
        , reservedNames  = ["forall", "data", "builtins", "builtincons", "_", "case", "of", "where"]
        , caseSensitive  = True
        }

parseType mb vs = maybe id option mb $ reserved lang "::" *> parseTerm PrecLam vs
patVar = identifier lang <|> "" <$ reserved lang "_"
typedId mb vs = (,) <$> patVar <*> localIndentation Gt {-TODO-} (parseType mb vs)
typedId' mb vs = (,) <$> commaSep1 lang patVar <*> localIndentation Gt {-TODO-} (parseType mb vs)

telescope mb vs = option (vs, []) $ do
    (x, vt) <-
            reservedOp lang "@" *> (maybe empty (\x -> flip (,) (Hidden, x) <$> patVar) mb <|> parens lang (f Hidden))
        <|> try (parens lang $ f Visible)
        <|> maybe ((,) "" . (,) Visible <$> parseTerm PrecAtom vs) (\x -> flip (,) (Visible, x) <$> patVar) mb
    (id *** (vt:)) <$> telescope mb (x: vs)
  where
    f v = (id *** (,) v) <$> typedId mb vs

addStmt x = lift (modify (x:))

parseStmt :: Pars ()
parseStmt =
     do con <- False <$ reserved lang "builtins" <|> True <$ reserved lang "builtincons"
        localIndentation Gt $ localAbsoluteIndentation $ void $ many $ do
            f <- addForalls . defined <$> get
            mapM_ addStmt =<< (\(vs, t) -> Primitive con <$> vs <*> pure t) . (id *** f) <$> typedId' Nothing []
 <|> do reserved lang "data"
        localIndentation Gt $ do
            x <- identifier lang
            (nps, ts) <- telescope (Just SType) []
            t <- parseType (Just SType) nps
            let mkConTy (_, ts') = foldr (uncurry SPi) (foldl SAppV (SGlobal x) $ downTo (length ts') $ length ts) ts'
            cs <-
                 do reserved lang "where" *> localIndentation Ge (localAbsoluteIndentation $ many $ typedId' Nothing nps)
             <|> do reserved lang "=" *> sepBy ((,) <$> (pure <$> identifier lang) <*> (mkConTy <$> telescope Nothing nps)) (reserved lang "|")
            f <- addForalls . (x:) . defined <$> get
            addStmt $ Data x ts t $ map (id *** f) $ concatMap (\(vs, t) -> (,) <$> vs <*> pure t) cs
 <|> do (vs, t) <- try $ typedId' Nothing []
        mapM_ addStmt $ TypeAnn <$> vs <*> pure t
 <|> do n <- identifier lang
        mt <- lift $ state $ \ds -> maybe (Nothing, ds) (Just *** id) $ listToMaybe [(t, as ++ bs) | (as, TypeAnn n' t: bs) <- zip (inits ds) (tails ds), n' == n]
        localIndentation Gt $ do
            (fe, ts) <- telescope (Just $ Wildcard SType) [n]
            t' <- reserved lang "=" *> parseTerm PrecLam fe
            addStmt $ Let n mt $ foldr (uncurry SLam) t' ts

sapp a (v, b) = SApp v a b

parseTerm :: Prec -> [String] -> Pars SExp
parseTerm PrecLam e =
     do tok <- (SPi . const Hidden <$ reserved lang "." <|> SPi . const Visible <$ reserved lang "->") <$ reserved lang "forall"
           <|> (SLam <$ reserved lang "->") <$ reservedOp lang "\\"
        (fe, ts) <- telescope (Just $ Wildcard SType) e
        f <- tok
        t' <- parseTerm PrecLam fe
        return $ foldr (uncurry f) t' ts
 <|> do x <- reserved lang "case" *> parseTerm PrecLam e
        cs <- reserved lang "of" *> sepBy1 (parseClause e) (reserved lang ";")
        mkCase x cs <$> lift get
 <|> do gtc <$> lift get <*> (Alts <$> parseSomeGuards (const True) e)
 <|> do t <- parseTerm PrecEq e
        option t $ SPi <$> (Visible <$ reserved lang "->" <|> Hidden <$ reserved lang "=>") <*> pure t <*> parseTerm PrecLam ("": e)
parseTerm PrecEq e = parseTerm PrecAnn e >>= \t -> option t $ SCstr t <$ reservedOp lang "~" <*> parseTerm PrecAnn e
parseTerm PrecAnn e = parseTerm PrecApp e >>= \t -> option t $ SAnn t <$> parseType Nothing e
parseTerm PrecApp e = foldl sapp <$> parseTerm PrecAtom e <*> many
            (   (,) Visible <$> parseTerm PrecAtom e
            <|> (,) Hidden <$ reservedOp lang "@" <*> parseTerm PrecAtom e)
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
            x <- parseTerm PrecEq e
            return (e', \gs' gs -> GuardNode x p vs (Alts gs'): gs)
     <|> do x <- parseTerm PrecEq e
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

mkCase :: SExp -> [(Pat, SExp)] -> [Stmt] -> SExp
mkCase x cs@((PCon cn _, _): _) adts = (\x -> traceD ("case: " ++ showSExp x) x) $ mkCase' t x [(length vs, e) | (cn, _) <- cns, (PCon c vs, e) <- cs, c == cn]
  where
    (t, cns) = findAdt adts cn

findAdt adts cstr = head $ [(t, csn) | Data t _ _ csn <- adts, cstr `elem` map fst csn] ++ error ("mkCase: " ++ cstr)

pattern SMotive = SLam Visible (Wildcard SType) (Wildcard SType)

mkCase' :: SName -> SExp -> [(Int, SExp)] -> SExp
mkCase' t x cs = foldl SAppV (SGlobal (Case t) `SAppV` SMotive)
    [iterate (SLam Visible (Wildcard SType)) e !! vs | (vs, e) <- cs]
    `SAppV` x

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

gtc adts t = (\x -> traceD ("  !  :" ++ showSExp x) x) $ guardTreeToCases t
  where
    guardTreeToCases :: GuardTree -> SExp
    guardTreeToCases t = case alts t of
        [] -> SGlobal "undefined"
        GuardLeaf e: _ -> e
        ts@(GuardNode f s _ _: _) ->
          mkCase' t f $
            [ (n, guardTreeToCases $ Alts $ map (filterGuardTree f cn n) ts)
            | (cn, ct) <- cns
            , let n = length $ filter ((==Visible) . fst) $ fst $ getParamsS ct
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
showEnvSExpType e c t = showDoc $ envDoc e $ epar <$> (shAnn "::" False <$> sExpDoc c <**> expDoc t)
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
    EBind1 h ts b       -> envDoc ts $ join $ shLam (usedS 0 b) h <$> m <*> pure (sExpDoc b)
    EBind2 h a ts       -> envDoc ts $ join $ shLam True h <$> expDoc a <*> pure m
    EApp1 h ts b        -> envDoc ts $ shApp h <$> m <*> sExpDoc b
    EApp2 h (Lam Visible Type (Var 0)) ts -> envDoc ts $ shApp h (shAtom "tyType") <$> m
    EApp2 h a ts        -> envDoc ts $ shApp h <$> expDoc a <*> m
    ELet i x ts         -> envDoc ts $ shLet i (expDoc x) m
    CheckType t ts      -> envDoc ts $ shAnn ":" False <$> m <*> expDoc t
    CheckSame t ts      -> envDoc ts $ shCstr <$> m <*> expDoc t
    CheckAppType h t te b      -> envDoc (EApp1 h (CheckType t te) b) m

expDoc :: Exp -> Doc
expDoc e = fmap inGreen <$> f e
  where
    f = \case
        Label s xs _    -> foldl (shApp Visible) (shAtom (inRed s)) <$> mapM f (reverse xs)
        Var k           -> shVar k
        App a b         -> shApp Visible <$> f a <*> f b
        Bind h a b      -> join $ shLam (usedE 0 b) h <$> f a <*> pure (f b)
        Cstr a b        -> shCstr <$> f a <*> f b
        Prim s xs       -> foldl (shApp Visible) (shAtom $ showPrimN s) <$> mapM f xs
        Assign i x e      -> shLet i (f x) (f e)

sExpDoc :: SExp -> Doc
sExpDoc = \case
    SGlobal s       -> pure $ shAtom s
    SAnn a b        -> shAnn ":" False <$> sExpDoc a <*> sExpDoc b
    TyType a        -> shApp Visible (shAtom "tyType") <$> sExpDoc a
    SApp h a b      -> shApp h <$> sExpDoc a <*> sExpDoc b
--    Wildcard t      -> shAnn True (shAtom "_") <$> sExpDoc t
    SBind h a b     -> join $ shLam (usedS 0 b) h <$> sExpDoc a <*> pure (sExpDoc b)
    STyped e        -> expDoc e

showLit = \case
    LInt i -> show i
    LChar c -> show c

showPrimN :: PrimName -> String
showPrimN = \case
    CLit i      -> showLit i
    ConName s   -> s
    FunName s   -> s

shVar i = asks $ shAtom . lookupVarName where
    lookupVarName xs | i < length xs && i >= 0 = xs !! i
    lookupVarName _ = "V" ++ show i

shLet i a b = shVar i >>= \i' -> local (dropNth i) $ shLam' <$> (cpar . shLet' (fmap inBlue i') <$> a) <*> b
shLam used h a b = (gets head <* modify tail) >>= \i ->
    let lam = case h of
            BPi _ -> shArr
            _ -> shLam'
        p = case h of
            BMeta -> cpar . shAnn ":" True (shAtom $ inBlue i)
            BLam h -> vpar h
            BPi h -> vpar h
        vpar Hidden = brace . shAnn ":" True (shAtom $ inGreen i)
        vpar Visible = ann (shAtom $ inGreen i)
        ann | used = shAnn ":" False
            | otherwise = const id
    in lam (p a) <$> local (i:) b

-----------------------------------------

data PS a = PS Prec a deriving (Functor)
type PrecString = PS String

getPrec (PS p _) = p
prec i s = PS i (s i)
str (PS _ s) = s

data Prec
    = PrecAtom      --  ( _ )  ...
    | PrecAtom'
    | PrecApp       --  _ _                 {left}
    | PrecArr       --  _ -> _              {right}
    | PrecEq        --  _ ~ _
    | PrecAnn       --  _ :: _              {right}
    | PrecLet       --  _ := _
    | PrecLam       --  \ _ -> _            {right} {accum}
    deriving (Eq, Ord)

lpar, rpar :: PrecString -> Prec -> String
lpar (PS i s) j = par (i >. j) s  where
    PrecLam >. i = i > PrecAtom'
    i >. PrecLam = i >= PrecArr
    PrecApp >. PrecApp = False
    i >. j  = i >= j
rpar (PS i s) j = par (i >. j) s where
    PrecLam >. PrecLam = False
    PrecLam >. i = i > PrecAtom'
    PrecArr >. PrecArr = False
    PrecAnn >. PrecAnn = False
    i >. j  = i >= j

par True s = "(" ++ s ++ ")"
par False s = s

isAtom = (==PrecAtom) . getPrec
isAtom' = (<=PrecAtom') . getPrec

shAtom = PS PrecAtom
shAtom' = PS PrecAtom'
shAnn _ True x y | str y `elem` ["Type", inGreen "Type"] = x
shAnn s simp x y | isAtom x && isAtom y = shAtom' $ str x <> s <> str y
shAnn s simp x y = prec PrecAnn $ lpar x <> " " <> const s <> " " <> rpar y
shApp Hidden x y = prec PrecApp $ lpar x <> " " <> const (str $ brace y)
shApp h x y = prec PrecApp $ lpar x <> " " <> rpar y
shArr x y | isAtom x && isAtom y = shAtom' $ str x <> "->" <> str y
shArr x y = prec PrecArr $ lpar x <> " -> " <> rpar y
shCstr x y | isAtom x && isAtom y = shAtom' $ str x <> "~" <> str y
shCstr x y = prec PrecEq $ lpar x <> " ~ " <> rpar y
shLet' x y | isAtom x && isAtom y = shAtom' $ str x <> ":=" <> str y
shLet' x y = prec PrecLet $ lpar x <> " := " <> rpar y
shLam' x y | PrecLam <- getPrec y = prec PrecLam $ "\\" <> lpar x <> " " <> pure (dropC $ str y)
shLam' x y | isAtom x && isAtom y = shAtom' $ "\\" <> str x <> "->" <> str y
shLam' x y = prec PrecLam $ "\\" <> lpar x <> " -> " <> rpar y
brace s = shAtom $ "{" <> str s <> "}"
cpar s | isAtom' s = s      -- TODO: replace with lpar, rpar
cpar s = shAtom $ par True $ str s
epar s = fmap underlined s

dropC (ESC s (dropC -> x)) = ESC s x
dropC (x: xs) = xs

pattern ESC a b <- (splitESC -> Just (a, b)) where ESC a b | all (/='m') a = "\ESC[" ++ a ++ "m" ++ b

splitESC ('\ESC':'[': (span (/='m') -> (a, ~('m': b)))) = Just (a, b)
splitESC _ = Nothing

instance IsString (Prec -> String) where fromString = const

inGreen = withEsc 32
inBlue = withEsc 34
inRed = withEsc 31
underlined = withEsc 40
withEsc i s = ESC (show i) $ s ++ ESC "" ""

correctEscs = f ["39","49"] where
    f acc (ESC i@(_:_) cs) = ESC i $ f (i:acc) cs
    f (a: acc) (ESC "" cs) = ESC (compOld a acc) $ f acc cs
    f acc (c: cs) = c: f acc cs
    f acc [] = []

    compOld x xs = head $ filter ((== cType x) . cType) xs

    cType n
        | "30" <= n && n <= "39" = 0
        | "40" <= n && n <= "49" = 1
        | otherwise = 2


putStrLn' = putStrLn . correctEscs
trace_ = trace . correctEscs
traceD x = if debug then trace_ x else id

-------------------------------------------------------------------------------- main

-- TODO: te
unLabelRec te x = case unLabel' x of
    Bind a b c -> Bind a (unLabelRec te b) (unLabelRec te c)
    Assign a b c -> Assign a (unLabelRec te b) (unLabelRec te c)
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
    where s = showExp $ inferN tr (EGlobal initEnv mempty) xx

test' n = test $ foldl1 SAppV $ replicate n $ SLam Visible (Wildcard SType) $ SVar 0
test'' n = test $ foldr1 SAppV $ replicate n $ SLam Visible (Wildcard SType) $ SVar 0

tr = False--True
tr_light = True
debug = False--True--tr
debug_light = True--False

main = do
    args <- getArgs
    let name = head $ args ++ ["Prelude"]
        f = name ++ ".lc"
        f' = name ++ ".lci"

        p = do
            getPosition >>= setState
            setPosition =<< flip setSourceName f <$> getPosition
            whiteSpace lang >> void (many parseStmt) >> eof
            gets reverse
    s <- readFile f
    case flip evalState mempty $ P.runParserT p (P.newPos "" 0 0) f $ I.mkIndentStream 0 I.infIndentation True I.Ge $ I.mkCharIndentStream s of
      Left e -> error $ show e
      Right stmts -> runExceptT (flip runStateT initEnv $ mapM_ handleStmt stmts) >>= \case
            Left e -> putStrLn e
            Right (x, s) -> do
                let ev = EGlobal s mempty
                let s_ = (unLabelRec ev *** unLabelRec ev) <$> s
                putStrLn "----------------------"
--                writeFile f' $ show $ Map.toList s_
                s' <- Map.fromList . read <$> readFile f'
                sequence_ $ Map.elems $ Map.mapWithKey (\k -> either (\_ -> putStrLn $ "xxx: " ++ k) id) $ Map.unionWithKey check (Left <$> s') (Left <$> s_)
--                writeFile f' $ show $ Map.toList s_
                putStrLn $ maybe "!main was not found" (show . {- unLabelRec -} unLabel . fst) $ Map.lookup "main" s
  where
    check k (Left (x, t)) (Left (x', t'))
        | t /= t' = Right $ putStrLn' $ "!!! type diff: " ++ k ++ "\n  old:   " ++ showExp t ++ "\n  new:   " ++ showExp t'
        | x /= x' = Right $ putStrLn' $ "!!! def diff: " ++ k
        | otherwise = Right $ return ()

-------------------------------------------------------------------------------- utils

dropNth i xs = take i xs ++ drop (i+1) xs
iterateN n f e = iterate f e !! n
