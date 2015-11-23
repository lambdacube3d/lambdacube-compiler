{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
module Infer where

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
import Control.Applicative hiding (optional)
import Control.Exception hiding (try)

import Text.Parsec hiding (parse, label, Empty, State, (<|>), many, optional)
--import Text.Parsec.Token hiding (makeTokenParser, operator)
import qualified Text.Parsec.Token as Pa
import Text.Parsec.Pos
import Text.Parsec.Indentation hiding (Any)
import Text.Parsec.Indentation.Char
import Text.Parsec.Indentation.Token

import System.Environment
import System.Directory
import Debug.Trace

import qualified Pretty as P

-------------------------------------------------------------------------------- source data

type SName = String

data Stmt
    = TypeAnn SName SExp            -- intermediate
    | Let SName (Maybe SExp) SExp
    | Data SName [(Visibility, SExp)]{-parameters-} SExp{-type-} [(SName, SExp)]{-constructor names and types-}
    | Primitive (Maybe Bool{-Just True: type constructor; Just False: constructor; Nothing: function-}) SName SExp{-type-}
    | PrecDef SName Fixity
    | Wrong [Stmt]
    deriving (Show)

data SExp
    = SGlobal SName
    | SBind Binder SExp SExp
    | SApp Visibility SExp SExp
    | SVar !Int
    | STyped ExpType
    | SPreExp PreExp    -- eliminated at the end of parsing
  deriving (Eq, Show)

newtype PreExp = PreExp ([Stmt] -> SExp)    -- building of expr. needs ADTs

instance Eq PreExp where _ == _ = False
instance Show PreExp where show = undefined

preExp :: ([Stmt] -> SExp) -> SExp
preExp = SPreExp . PreExp

type Fixity = (Maybe FixityDir, Int)
data FixityDir = FDLeft | FDRight deriving (Show)

data Binder
    = BPi  Visibility
    | BLam Visibility
    | BMeta      -- a metavariable is like a floating hidden lambda
  deriving (Eq, Show)

data Visibility = Hidden | Visible
  deriving (Eq, Show)

sLit a = STyped (ELit a, litType a)
pattern SType  = STyped (TType, TType)
pattern SPi  h a b = SBind (BPi  h) a b
pattern SLam h a b = SBind (BLam h) a b
pattern Wildcard t = SBind BMeta t (SVar 0)
pattern SAppV a b = SApp Visible a b
pattern SAnn a t = STyped (Lam Visible TType (Lam Visible (Var 0) (Var 0)), TType :~> Var 0 :~> Var 1) `SAppV` t `SAppV` a  --  a :: t ~~> id t a
pattern TyType a = STyped (Lam Visible TType (Var 0), TType :~> TType) `SAppV` a
    -- same as  (a :: TType)     --  a :: TType   ~~>   (\(x :: TType) -> x) a
--pattern CheckSame' a b c = SGlobal "checkSame" `SAppV` STyped a `SAppV` STyped b `SAppV` c
pattern SCstr a b = SGlobal "cstr" `SAppV` a `SAppV` b          --    a ~ b

isPi (BPi _) = True
isPi _ = False

infixl 1 `SAppV`, `App`

-------------------------------------------------------------------------------- destination data

data Exp
    = Bind Binder Exp Exp   -- TODO: prohibit meta binder here;  BLam is not allowed
    | Lam Visibility Exp Exp
    | Con ConName [Exp]
    | TyCon TyConName [Exp]
    | ELit Lit
    | Assign !Int Exp Exp       -- De Bruijn index decreasing assign operator, only for metavariables (non-recursive) -- TODO: remove
    | Label FunName [Exp]{-reverse ordered arguments-} Exp{-reduced expression-}
    | Neut Neutral
    | TType
  deriving (Show)

data Neutral
    = Fun_ FunName [Exp]
    | CaseFun_ CaseFunName [Exp]
    | App_ Exp{-todo: Neutral-} Exp
    | Var_ !Int                 -- De Bruijn variable
  deriving (Show)

type Type = Exp

data ConName = ConName SName Int Type
instance Show ConName where show (ConName n _ _) = n
instance Eq ConName where ConName n _ _ == ConName n' _ _ = n == n'

data TyConName = TyConName SName Type Type{-case type-}
instance Show TyConName where show (TyConName n _ _) = n
instance Eq TyConName where TyConName n _ _ == TyConName n' _ _ = n == n'

data FunName = FunName SName Type
instance Show FunName where show (FunName n _) = n
instance Eq FunName where FunName n _ == FunName n' _ = n == n'

data CaseFunName = CaseFunName SName Type Int{-num of parameters-}
instance Show CaseFunName where show (CaseFunName n _ _) = n
instance Eq CaseFunName where CaseFunName n _ _ == CaseFunName n' _ _ = n == n'


pattern Case s <- (splitCase -> Just s) where Case (c:cs) = toLower c: cs ++ "Case"

splitCase s
    | reverse (take 4 $ reverse s) == "Case"
    , c:cs <- reverse $ drop 4 $ reverse s
    = Just $ toUpper c: cs
    | otherwise = Nothing

type ExpType = (Exp, Type)

pattern Fun a b = Neut (Fun_ a b)
pattern CaseFun a b = Neut (CaseFun_ a b)
pattern FunN a b <- Fun (FunName a _) b
pattern CaseFunN a b <- CaseFun (CaseFunName a _ _) b
pattern TFun a t b = Fun (FunName a t) b
pattern TCaseFun a t i b = CaseFun (CaseFunName a t i) b
pattern App a b = Neut (App_ a b)
pattern Var a = Neut (Var_ a)

data Lit
    = LInt !Int
    | LChar Char
    | LFloat Double
    | LString String
  deriving (Eq)

instance Show Lit where
    show = \case
        LFloat x  -> show x
        LString x -> show x
        LInt x    -> show x
        LChar x   -> show x

pattern Lam' b  <- Lam _ _ b
pattern Pi  h a b = Bind (BPi h) a b
pattern Meta  a b = Bind BMeta a b

pattern Cstr a b    = TFun "cstr" (TType :~> TType :~> TType){-todo-} [a, b]
pattern ReflCstr x  = TFun "reflCstr" (TType :~> Cstr (Var 0) (Var 0)) [x]
pattern Coe a b w x = TFun "coe" (TType :~> TType :~> Cstr (Var 1) (Var 0) :~> Var 2 :~> Var 2) [a,b,w,x]

pattern ConN s a   <- Con (ConName s _ _) a
pattern TyConN s a <- TyCon (TyConName s _ _) a
pattern TCon s i t a = Con (ConName s i t) a   -- todo: don't match on type
pattern TTyCon s t a <- TyCon (TyConName s t _) a where TTyCon s t a = TyCon (TyConName s t $ error "TTyCon") a
pattern TTyCon0 s  <- TyCon (TyConName s TType _) [] where TTyCon0 s = TyCon (TyConName s TType $ error "TTyCon0") []
pattern Sigma a b  <- TyConN "Sigma" [a, Lam' b] where Sigma a b = TTyCon "Sigma" (error "sigmatype") [a, Lam Visible a{-todo: don't duplicate-} b]
pattern Unit        = TTyCon0 "Unit"
pattern TT          = TCon "TT" 0 Unit []
pattern T2 a b      = TTyCon "T2" (TType :~> TType :~> TType) [a, b]
pattern T2C a b    <- ConN "T2C" [_, _, a, b]
pattern Empty       = TTyCon0 "Empty"
pattern TInt        = TTyCon0 "Int"
pattern TNat        = TTyCon0 "Nat"
pattern TBool       = TTyCon0 "Bool"
pattern TFloat      = TTyCon0 "Float"
pattern TString     = TTyCon0 "String"
pattern Zero        = TCon "Zero" 0 TNat []
pattern Succ n      = TCon "Succ" 1 (TNat :~> TNat) [n]
pattern TVec a b    = TTyCon "'Vec" (TNat :~> TType :~> TType) [a, b]
pattern TFrameBuffer a b = TTyCon "'FrameBuffer" (TNat :~> TType :~> TType) [a, b]

tTuple2 a b = TTyCon "'Tuple2" (TType :~> TType :~> TType) [a, b]
t2C te a b = TCon "T2C" 0 (TType :~> TType :~> Var 1 :~> Var 1 :~> T2 (Var 3) (Var 2)) [expType_ te a, expType_ te b, a, b]

pattern EInt a      = ELit (LInt a)

eBool False = TCon "False" 0 TBool []
eBool True  = TCon "True" 1 TBool []

pattern LCon <- (isCon -> True)
pattern CFun <- (caseFunName -> True)

pattern a :~> b = Bind (BPi Visible) a b

infixr 1 :~>

caseFunName (Fun f _) = True
caseFunName (CaseFun f _) = True
caseFunName _ = False

isCon = \case
    TType   -> True
    Con _ _ -> True
    TyCon _ _ -> True
    ELit _  -> True
    _ -> False

-------------------------------------------------------------------------------- environments

-- SExp + Exp zipper
data Env
    = EBind1 Binder Env SExp            -- zoom into first parameter of SBind
    | EBind2 Binder Exp Env             -- zoom into second parameter of SBind
    | EApp1 Visibility Env SExp
    | EApp2 Visibility Exp Env
    | EGlobal GlobalEnv [Stmt]

    | EBind1' Binder Env Exp            -- todo: move Exp zipper constructor to a separate ADT (if needed)
    | EPrim SName [Exp] Env [Exp]    -- todo: move Exp zipper constructor to a separate ADT (if needed)

    | EAssign Int Exp Env
    | CheckType Exp Env
    | CheckSame Exp Env
    | CheckAppType Visibility Exp Env SExp
  deriving Show

--pattern CheckAppType h t te b = EApp1 h (CheckType t te) b

type GlobalEnv = Map.Map SName (Exp, Exp)

extractEnv :: Env -> GlobalEnv
extractEnv = either id extractEnv . parent

parent = \case
    EAssign _ _ x        -> Right x
    EBind2 _ _ x         -> Right x
    EBind1 _ x _         -> Right x
    EBind1' _ x _        -> Right x
    EApp2 _ _ x          -> Right x
    EApp1 _ x _          -> Right x
    CheckType _ x        -> Right x
    CheckSame _ x        -> Right x
    CheckAppType _ _ x _ -> Right x
    EPrim _ _ x _        -> Right x
    EGlobal x _          -> Left x


initEnv :: GlobalEnv
initEnv = Map.fromList
    [ (,) "Type" (TType, TType)     -- needed?
    ]

-- monad used during elaborating statments -- TODO: use zippers instead
type ElabStmtM m = StateT GlobalEnv (ExceptT String m)

-------------------------------------------------------------------------------- low-level toolbox

label a c d | labellable d = Label a c d
label a _ d = d

labellable (Lam' _) = True
labellable (Fun f _) = labellableName f
labellable (CaseFun f _) = True
labellable _ = False

labellableName (FunName n _) = n `elem` ["matchInt", "matchList"] --False

unLabel (Label _ _ x) = x
unLabel x = x

pattern UnLabel a <- (unLabel -> a) where UnLabel a = a
--pattern UPrim a b = UnLabel (Con a b)
pattern UBind a b c = {-UnLabel-} (Bind a b c)      -- todo: review
pattern UApp a b = {-UnLabel-} (App a b)            -- todo: review
pattern UVar n = Var n

instance Eq Exp where
    Label s xs _ == Label s' xs' _ = (s, xs) == (s', xs') && length xs == length xs' {-TODO: remove check-}
    Lam' a == Lam' a' = a == a'
    Bind a b c == Bind a' b' c' = (a, b, c) == (a', b', c')
    -- Assign a b c == Assign a' b' c' = (a, b, c) == (a', b', c')
    Fun a b == Fun a' b' = (a, b) == (a', b')
    CaseFun a b == CaseFun a' b' = (a, b) == (a', b')
    Con a b == Con a' b' = (a, b) == (a', b')
    TyCon a b == TyCon a' b' = (a, b) == (a', b')
    TType == TType = True
    ELit l == ELit l' = l == l'
    App a b == App a' b' = (a, b) == (a', b')
    Var a == Var a' = a == a'
    _ == _ = False

assign :: (Int -> Exp -> Exp -> a) -> (Int -> Exp -> Exp -> a) -> Int -> Exp -> Exp -> a
assign _ clet i (Var j) b | i > j = clet j (Var (i-1)) $ substE "assign" j (Var (i-1)) $ up1E i b
assign clet _ i a b = clet i a b

handleLet i j f
    | i >  j = f (i-1) j
    | i <= j = f i (j+1)

foldS g f i = \case
    SApp _ a b -> foldS g f i a <> foldS g f i b
    SBind _ a b -> foldS g f i a <> foldS g f (i+1) b
    STyped (e, t) -> foldE f i e <> foldE f i t
    SVar j -> foldE f i (Var j)
    SGlobal x -> g i x

foldE f i = \case
    Label _ xs _ -> foldMap (foldE f i) xs
    Var k -> f i k
    Lam' b -> {-foldE f i t <>  todo: explain why this is not needed -} foldE f (i+1) b
    Bind _ a b -> foldE f i a <> foldE f (i+1) b
    Fun _ as -> foldMap (foldE f i) as
    CaseFun _ as -> foldMap (foldE f i) as
    Con _ as -> foldMap (foldE f i) as
    TyCon _ as -> foldMap (foldE f i) as
    TType -> mempty
    ELit _ -> mempty
    App a b -> foldE f i a <> foldE f i b
    Assign j x a -> handleLet i j $ \i' j' -> foldE f i' x <> foldE f i' a

freeS = nub . foldS (\_ s -> [s]) mempty 0
usedS = (getAny .) . foldS mempty ((Any .) . (==))
usedE = (getAny .) . foldE ((Any .) . (==))

mapS = mapS_ (const SGlobal)
mapS_ gg ff h e = g e where
    g i = \case
        SApp v a b -> SApp v (g i a) (g i b)
        SBind k a b -> SBind k (g i a) (g (h i) b)
        STyped (x, t) -> STyped (ff i x, ff i t)
        SVar j -> case ff i $ Var j of
            Var k -> SVar k
            -- x -> STyped x -- todo
        SGlobal x -> gg i x

upS__ i n = mapS (\i -> upE i n) (+1) i
upS = upS__ 0 1

up1E i = \case
    Var k -> Var $ if k >= i then k+1 else k
    Lam h a b -> Lam h (up1E i a) (up1E (i+1) b)
    Bind h a b -> Bind h (up1E i a) (up1E (i+1) b)
    Fun s as  -> Fun s $ map (up1E i) as
    CaseFun s as  -> CaseFun s $ map (up1E i) as
    Con s as  -> Con s $ map (up1E i) as
    TyCon s as -> TyCon s $ map (up1E i) as
    TType -> TType
    ELit l -> ELit l
    App a b -> App (up1E i a) (up1E i b)
    Assign j a b -> handleLet i j $ \i' j' -> assign Assign Assign j' (up1E i' a) (up1E i' b)
    Label f xs x -> Label f (map (up1E i) xs) $ up1E i x

upE i n e = iterate (up1E i) e !! n

substS j x = mapS (uncurry $ substE "substS") ((+1) *** up1E 0) (j, x)
substSG j x = mapS_ (\x i -> if i == j then x else SGlobal i) (const id) upS x

substE err = substE_ (error $ "substE: todo: environment required in " ++ err)  -- todo: remove

substE_ :: Env -> Int -> Exp -> Exp -> Exp
substE_ te i x = \case
    Label s xs v -> label s (map (substE "slab" i x) xs) $ substE_ te{-todo: label env?-} i x v
    Var k -> case compare k i of GT -> Var $ k - 1; LT -> Var k; EQ -> x
    Lam h a b -> let  -- question: is mutual recursion good here?
            a' = substE_ (EBind1' (BLam h) te b') i x a
            b' = substE_ (EBind2 (BLam h) a' te) (i+1) (up1E 0 x) b
        in Lam h a' b'
    Bind h a b -> let  -- question: is mutual recursion good here?
            a' = substE_ (EBind1' h te b') i x a
            b' = substE_ (EBind2 h a' te) (i+1) (up1E 0 x) b
        in Bind h a' b'
    Fun s as  -> eval te $ Fun s [substE_ te{-todo: precise env?-} i x a | (xs, a, ys) <- holes as]
    CaseFun s as  -> eval te $ CaseFun s [substE_ te{-todo: precise env?-} i x a | (xs, a, ys) <- holes as]
    Con s as  -> Con s [substE_ te{-todo-} i x a | (xs, a, ys) <- holes as]
    TyCon s as -> TyCon s [substE_ te{-todo-} i x a | (xs, a, ys) <- holes as]
    TType -> TType
    ELit l -> ELit l
    App a b  -> app_ (substE_ te i x a) (substE_ te i x b)  -- todo: precise env?
    Assign j a b
        | j > i, Just a' <- downE i a       -> assign Assign Assign (j-1) a' (substE "sa" i (substE "sa" (j-1) a' x) b)
        | j > i, Just x' <- downE (j-1) x   -> assign Assign Assign (j-1) (substE "sa" i x' a) (substE "sa" i x' b)
        | j < i, Just a' <- downE (i-1) a   -> assign Assign Assign j a' (substE "sa" (i-1) (substE "sa" j a' x) b)
        | j < i, Just x' <- downE j x       -> assign Assign Assign j (substE "sa" (i-1) x' a) (substE "sa" (i-1) x' b)
        | j == i    -> Meta (cstr x a) $ up1E 0 b

downS t x | usedS t x = Nothing
          | otherwise = Just $ substS t (error "impossible: downS") x
downE t x | usedE t x = Nothing
          | otherwise = Just $ substE_ (error "impossible") t (error "impossible: downE") x

varType :: String -> Int -> Env -> (Binder, Exp)
varType err n_ env = f n_ env where
    f n (EAssign i x es) = id *** substE "varType" i x $ f (if n < i then n else n+1) es
    f n (EBind2 b t es)  = if n == 0 then (b, up1E 0 t) else id *** up1E 0 $ f (n-1) es
    f n e = either (error $ "varType: " ++ err ++ "\n" ++ show n_ ++ "\n" ++ show env) (f n) $ parent e

-------------------------------------------------------------------------------- reduction

infixl 1 `app_`

app_ :: Exp -> Exp -> Exp
app_ (Lam' x) a = substE "app" 0 a x
app_ (Con s xs) a = Con s (xs ++ [a])
app_ (TyCon s xs) a = TyCon s (xs ++ [a])
app_ (Label f xs e) a = label f (a: xs) $ app_ e a
app_ f a = App f a

eval te = \case
    App a b -> app_ a b
    Cstr a b -> cstr a b
    ReflCstr a -> reflCstr te a
    Coe a b c d -> coe a b c d
-- todo: elim
    Fun n@(FunName "natElim" _) [a, z, s, Succ x] -> let      -- todo: replace let with better abstraction
                sx = s `app_` x
            in sx `app_` eval (EApp2 Visible sx te) (Fun n [a, z, s, x])
    FunN "natElim" [_, z, s, Zero] -> z
    Fun na@(FunName "finElim" _) [m, z, s, n, ConN "FSucc" [i, x]] -> let six = s `app_` i `app_` x-- todo: replace let with better abstraction
        in six `app_` eval (EApp2 Visible six te) (Fun na [m, z, s, i, x])
    FunN "finElim" [m, z, s, n, ConN "FZero" [i]] -> z `app_` i
    CaseFun (CaseFunName n t pars) (drop (pars + 1) -> ps@(last -> Con (ConName _ i _) (drop pars -> vs))) | i /= (-1) -> foldl app_ (ps !! i) vs
    FunN "PrimIfThenElse" [_, xt, xf, ConN "True" []] -> xt
    FunN "PrimIfThenElse" [_, xt, xf, ConN "False" []] -> xf
    FunN "primAdd" [EInt i, EInt j] -> EInt (i + j)
    FunN "primSub" [EInt i, EInt j] -> EInt (i - j)
    FunN "primMod" [EInt i, EInt j] -> EInt (i `mod` j)
    FunN "primSqrt" [EInt i] -> EInt $ round $ sqrt $ fromIntegral i
    FunN "primIntEq" [EInt i, EInt j] -> eBool (i == j)
    FunN "primIntLess" [EInt i, EInt j] -> eBool (i < j)
    FunN "matchInt" [t, f, TyConN "Int" []] -> t
    FunN "matchInt" [t, f, c@LCon] -> f `app_` c
    FunN "matchList" [t, f, TyConN "List" [a]] -> t `app_` a
    FunN "matchList" [t, f, c@LCon] -> f `app_` c
    Fun n@(FunName "Eq_" _) [TyConN "List" [a]] -> eval te $ Fun n [a]
    FunN "VecScalar" [Succ Zero, t] -> t
    FunN "VecScalar" [n@(Succ (Succ _)), t] -> TVec n t
    FunN "TFFrameBuffer" [TyConN "'Image" [n, t]] -> TFrameBuffer n t
    FunN "TFFrameBuffer" [TyConN "'Tuple2" [TyConN "'Image" [i@(fromNat -> Just n), t], TyConN "'Image" [fromNat -> Just n', t']]]
        | n == n' -> TFrameBuffer i $ tTuple2 t t'      -- todo
    FunN "FragOps" [TyConN "'FragmentOperation" [t]] -> t
    FunN "FragOps" [TyConN "'Tuple2" [TyConN "'FragmentOperation" [t], TyConN "'FragmentOperation" [t']]] -> tTuple2 t t'
    FunN "FTRepr'" [TyConN "'Interpolated" [t]] -> t          -- todo
    FunN "ColorRepr" [t] -> TTyCon "'Color" (TType :~> TType) [t] -- todo
    FunN "ValidFrameBuffer" [n] -> Unit -- todo
    FunN "ValidOutput" [n] -> Unit      -- todo
    FunN "AttributeTuple" [n] -> Unit   -- todo
    FunN "Floating" [TVec (Succ (Succ (Succ (Succ Zero)))) TFloat] -> Unit
    FunN "Eq_" [TInt] -> Unit
    FunN "Eq_" [LCon] -> Empty
    FunN "Monad" [TyConN "IO" []] -> Unit
    FunN "Num" [TFloat] -> Unit
    x -> x

fromNat :: Exp -> Maybe Int
fromNat Zero = Just 0
fromNat (Succ n) = (1 +) <$> fromNat n

-- todo
coe a b c d | a == b = d        -- todo
coe a b c d = Coe a b c d

reflCstr te = \case
    Unit -> TT
    TType -> TT  -- ?
    Con n xs -> foldl (t2C te{-todo: more precise env-}) TT $ map (reflCstr te{-todo: more precise env-}) xs
    TyCon n xs -> foldl (t2C te{-todo: more precise env-}) TT $ map (reflCstr te{-todo: more precise env-}) xs
    x -> {-error $ "reflCstr: " ++ show x-} ReflCstr x

cstr = cstr__ []
  where
    cstr__ = cstr_

    cstr_ ns TType TType = Unit
    cstr_ ns (Con a []) (Con a' []) | a == a' = Unit
    cstr_ ns (TyCon a []) (TyCon a' []) | a == a' = Unit
    cstr_ ns (Var i) (Var i') | i == i', i < length ns = Unit
    cstr_ (_: ns) (downE 0 -> Just a) (downE 0 -> Just a') = cstr__ ns a a'
    cstr_ ((t, t'): ns) (UApp (downE 0 -> Just a) (UVar 0)) (UApp (downE 0 -> Just a') (UVar 0)) = traceInj2 (a, "V0") (a', "V0") $ cstr__ ns a a'
    cstr_ ((t, t'): ns) a (UApp (downE 0 -> Just a') (UVar 0)) = traceInj (a', "V0") a $ cstr__ ns (Lam Visible t a) a'
    cstr_ ((t, t'): ns) (UApp (downE 0 -> Just a) (UVar 0)) a' = traceInj (a, "V0") a' $ cstr__ ns a (Lam Visible t' a')
    cstr_ ns (Lam h a b) (Lam h' a' b') | h == h' = T2 (cstr__ ns a a') (cstr__ ((a, a'): ns) b b')
    cstr_ ns (UBind h a b) (UBind h' a' b') | h == h' = T2 (cstr__ ns a a') (cstr__ ((a, a'): ns) b b')
    cstr_ ns (unApp -> Just (a, b)) (unApp -> Just (a', b')) = traceInj2 (a, show b) (a', show b') $ T2 (cstr__ ns a a') (cstr__ ns b b')
--    cstr_ ns (Label f xs _) (Label f' xs' _) | f == f' = foldr1 T2 $ zipWith (cstr__ ns) xs xs'
    cstr_ ns (FunN "VecScalar" [a, b]) (TVec a' b') = T2 (cstr__ ns a a') (cstr__ ns b b')
--    cstr_ ns (TyConN "'FrameBuffer" [a, b]) (FunN "TFFrameBuffer" [TyConN "'Image" [a', b']]) = T2 (cstr__ ns a a') (cstr__ ns b b')
    cstr_ [] a@App{} a'@App{} = Cstr a a'
    cstr_ [] a@CFun a'@CFun = Cstr a a'
    cstr_ [] a@LCon a'@CFun = Cstr a a'
    cstr_ [] a@LCon a'@App{} = Cstr a a'
    cstr_ [] a@CFun a'@LCon = Cstr a a'
    cstr_ [] a@App{} a'@LCon = Cstr a a'
    cstr_ [] a a' | isVar a || isVar a' = Cstr a a'
    cstr_ ns a a' = trace_ ("!----------------------------! type error:\n" ++ show ns ++ "\nfst:\n" ++ show a ++ "\nsnd:\n" ++ show a') Empty

    unApp (UApp a b) = Just (a, b)         -- TODO: injectivity check
    unApp (Con a xs@(_:_)) = Just (Con a (init xs), last xs)
    unApp (TyCon a xs@(_:_)) = Just (TyCon a (init xs), last xs)
    unApp _ = Nothing

    isVar UVar{} = True
    isVar (UApp a b) = isVar a
    isVar _ = False

    traceInj2 (a, a') (b, b') c | debug && (susp a || susp b) = trace_ ("  inj'?  " ++ show a ++ " : " ++ a' ++ "   ----   " ++ show b ++ " : " ++ b') c
    traceInj2 _ _ c = c
    traceInj (x, y) z a | debug && susp x = trace_ ("  inj?  " ++ show x ++ " : " ++ y ++ "    ----    " ++ show z) a
    traceInj _ _ a = a

    susp Con{} = False
    susp TyCon{} = False
    susp _ = True

cstr' h x y e = EApp2 h (coe (up1E 0 x) (up1E 0 y) (Var 0) (up1E 0 e)) . EBind2 BMeta (cstr x y)

-------------------------------------------------------------------------------- simple typing

litType = \case
    LInt _    -> TInt
    LFloat _  -> TFloat
    LString _ -> TString

expType_ te = \case
    Lam h t x -> Pi h t $ expType_ (EBind2 (BLam h) t te) x
    App f x -> app (expType_ te{-todo: precise env-} f) x
    Var i -> snd $ varType "C" i te
    Pi{} -> TType
    Label s@(FunName _ t) ts _ -> foldl app t $ reverse ts
    TFun _ t ts -> foldl app t ts
    TCaseFun _ t _ ts -> foldl app t ts
    TCon _ _ t ts -> foldl app t ts
    TTyCon _ t ts -> foldl app t ts
    TType -> TType
    ELit l -> litType l
    Meta{} -> error "meta type"
    Assign{} -> error "let type"
  where
    app (Pi _ a b) x = substE "expType_" 0 x b
    app t x = error $ "app: " ++ show t

-------------------------------------------------------------------------------- inference

fixDef n = Lam Hidden TType $ Lam Visible (Pi Visible (Var 0) (Var 1)) $ TFun n fixType [Var 1, Var 0]
fixType = Pi Hidden TType $ Pi Visible (Pi Visible (Var 0) (Var 1)) (Var 1)

type TCM m = ExceptT String m

runTCM = either error id . runExcept

-- todo: do only if NoTypeNamespace extension is not on
lookupName s@('\'':s') m = maybe (Map.lookup s' m) Just $ Map.lookup s m
lookupName s m = Map.lookup s m
elemIndex' s@('\'':s') m = maybe (elemIndex s' m) Just $ elemIndex s m
elemIndex' s m = elemIndex s m
notElem' s@('\'':s') m = notElem s m && notElem s' m
notElem' s m = notElem s m

getDef te s = maybe (throwError $ "getDef: can't find: " ++ s) return (lookupName s $ extractEnv te)

both f = f *** f

inferN :: forall m . Monad m => TraceLevel -> Env -> SExp -> TCM m ExpType
inferN tracelevel = infer  where

    infer :: Env -> SExp -> TCM m ExpType
    infer te exp = (if tracelevel >= 1 then trace_ ("infer: " ++ showEnvSExp te exp) else id) $ (if debug then fmap (recheck' te *** id) else id) $ case exp of
        SVar i      -> focus te (Var i)
        STyped et   -> focus_ te et
        SGlobal s   -> focus_ te =<< getDef te s
        SApp  h a b -> infer (EApp1 h te b) a
        SBind h a b -> infer ((if h /= BMeta then CheckType TType else id) $ EBind1 h te $ (if isPi h then TyType else id) b) a

    checkN :: Env -> SExp -> Exp -> TCM m ExpType
    checkN te x t = (if tracelevel >= 1 then trace_ $ "check: " ++ showEnvSExpType te x t else id) $ checkN_ te x t

    checkN_ te e t
        | SApp h a b <- e = infer (CheckAppType h t te b) a
        | SLam h a b <- e, Pi h' x y <- t, h == h'  = if checkSame te a x then checkN (EBind2 (BLam h) x te) b y else error "checkN"
        | Pi Hidden a b <- t, notHiddenLam e = checkN (EBind2 (BLam Hidden) a te) (upS e) b
        | otherwise = infer (CheckType t te) e
      where
        -- todo
        notHiddenLam = \case
            SLam Visible _ _ -> True
            SGlobal s | Lam Hidden _ _ <- fst $ fromMaybe (error $ "infer: can't find: " ++ s) $ lookupName s $ extractEnv te -> False
                            -- todo: use type instead of expr.
                      | otherwise -> True
            _ -> False

    -- todo
    checkSame te (Wildcard _) a = True
    checkSame te (SBind BMeta SType (STyped (Var 0, _))) a = True
    checkSame te a b = error $ "checkSame: " ++ show (a, b)

    hArgs (Pi Hidden _ b) = 1 + hArgs b
    hArgs _ = 0

    focus env e = focus_ env (e, expType_ env e)

    focus_ :: Env -> ExpType -> TCM m ExpType
    focus_ env (e, et) = (if tracelevel >= 1 then trace_ $ "focus: " ++ showEnvExp env e else id) $ (if debug then fmap (recheck' env *** id) else id) $ case env of
        CheckSame x te -> focus_ (EBind2 BMeta (cstr x e) te) (up1E 0 e, up1E 0 et)
        CheckAppType h t te b
            | Pi h' x (downE 0 -> Just y) <- et, h == h' -> focus_ (EBind2 BMeta (cstr t y) $ EApp1 h te b) (up1E 0 e, up1E 0 et)
            | otherwise -> focus_ (EApp1 h (CheckType t te) b) (e, et)
        EApp1 h te b
            | Pi h' x y <- et, h == h' -> checkN (EApp2 h e te) b x
            | Pi Hidden x y  <- et, h == Visible -> focus_ (EApp1 Hidden env $ Wildcard $ Wildcard SType) (e, et)  --  e b --> e _ b
            | otherwise -> infer (CheckType (Var 2) $ cstr' h (upE 0 2 et) (Pi Visible (Var 1) (Var 1)) (upE 0 2 e) $ EBind2 BMeta TType $ EBind2 BMeta TType te) (upS__ 0 3 b)
        CheckType t te
            | hArgs et > hArgs t
                            -> focus_ (EApp1 Hidden (CheckType t te) $ Wildcard $ Wildcard SType) (e, et)
            | otherwise     -> focus_ (EBind2 BMeta (cstr t et) te) (up1E 0 e, up1E 0 et)
        EApp2 h a te        -> focus te $ app_ a e        --  h??
        EBind1 h te b       -> infer (EBind2 h e te) b
        EBind2 BMeta tt te
            | Unit <- tt    -> refocus te $ both (substE_ te 0 TT) (e, et)
            | Empty <- tt   -> throwError "halt" -- todo: better error msg
            | T2 x y <- tt -> let
                    te' = EBind2 BMeta (up1E 0 y) $ EBind2 BMeta x te
                in focus_ te' $ both (substE_ te' 2 (t2C te' (Var 1) (Var 0)) . upE 0 2) (e, et)
            | Cstr a b <- tt, a == b  -> refocus te $ both (substE "inferN2" 0 TT) (e, et)
            | Cstr a b <- tt, Just r <- cst a b -> r
            | Cstr a b <- tt, Just r <- cst b a -> r
            | EBind2 h x te' <- te, h /= BMeta, Just b' <- downE 0 tt
                            -> refocus (EBind2 h (up1E 0 x) $ EBind2 BMeta b' te') $ both (substE "inferN3" 2 (Var 0) . up1E 0) (e, et)
            | EBind1 h te' x  <- te -> refocus (EBind1 h (EBind2 BMeta tt te') $ upS__ 1 1 x) (e, et)
            | CheckAppType h t te' x <- te -> refocus (CheckAppType h (up1E 0 t) (EBind2 BMeta tt te') $ upS x) (e, et)
            | EApp1 h te' x   <- te -> refocus (EApp1 h (EBind2 BMeta tt te') $ upS x) (e, et)
            | EApp2 h x te'   <- te -> refocus (EApp2 h (up1E 0 x) $ EBind2 BMeta tt te') (e, et)
            | CheckType t te' <- te -> refocus (CheckType (up1E 0 t) $ EBind2 BMeta tt te') (e, et)
            | otherwise             -> focus_ te (Bind BMeta tt e, et {-???-})
          where
            cst x = \case
                Var i | fst (varType "X" i te) == BMeta
                      , Just y <- downE i x
                      -> Just $ assign'' te i y $ both (substE_ te 0 (ReflCstr y) . substE_ te (i+1) (up1E 0 y)) (e, et)
                _ -> Nothing
        EBind2 (BLam h) a te -> focus_ te (Lam h a e, Pi h a e)
        EBind2 (BPi h) a te -> focus_ te (Bind (BPi h) a e, TType)
        EAssign i b te -> case te of
            EBind2 h x te' | i > 0, Just b' <- downE 0 b
                              -> refocus' (EBind2 h (substE "inferN5" (i-1) b' x) (EAssign (i-1) b' te')) (e, et)
            EBind1 h te' x    -> refocus' (EBind1 h (EAssign i b te') $ substS (i+1) (up1E 0 b) x) (e, et)
            CheckAppType h t te' x -> refocus' (CheckAppType h (substE "inferN6" i b t) (EAssign i b te') $ substS i b x) (e, et)
            EApp1 h te' x     -> refocus' (EApp1 h (EAssign i b te') $ substS i b x) (e, et)
            EApp2 h x te'     -> refocus' (EApp2 h (substE_ te'{-todo: precise env-} i b x) $ EAssign i b te') (e, et)
            CheckType t te'   -> refocus' (CheckType (substE "inferN8" i b t) $ EAssign i b te') (e, et)
            te@EBind2{}       -> maybe (assign' te i b (e, et)) (flip refocus' (e, et)) $ pull i te
            te@EAssign{}      -> maybe (assign' te i b (e, et)) (flip refocus' (e, et)) $ pull i te
            -- todo: CheckSame Exp Env
          where
            pull i = \case
                EBind2 BMeta _ te | i == 0 -> Just te
                EBind2 h x te   -> EBind2 h <$> downE (i-1) x <*> pull (i-1) te
                EAssign j b te  -> EAssign (if j <= i then j else j-1) <$> downE i b <*> pull (if j <= i then i+1 else i) te
                _               -> Nothing
        EGlobal{} -> return (e, et)
        _ -> error $ "focus: " ++ show env
      where
        assign', assign'' :: Env -> Int -> Exp -> ExpType -> TCM m ExpType
        assign'  te i x (e, t) = assign (\i x e -> focus te (Assign i x e)) (foc te) i x e
        assign'' te i x (e, t) = assign (foc te) (foc te) i x e
        foc te i x = focus $ EAssign i x te

        refocus, refocus' :: Env -> ExpType -> TCM m ExpType
        refocus = refocus_ focus_
        refocus' = refocus_ refocus'

        refocus_ f e (Bind BMeta x a, t) = f (EBind2 BMeta x e) (a, t)
        refocus_ _ e (Assign i x a, t) = focus (EAssign i x e) a
        refocus_ _ e (a, t) = focus e a

-------------------------------------------------------------------------------- debug support

recheck :: Env -> Exp -> Exp
recheck e = if debug_light then recheck' e else id

recheck' :: Env -> Exp -> Exp
recheck' e x = recheck_ "main" (checkEnv e) x
  where
    checkEnv = \case
        e@EGlobal{} -> e
        EBind1 h e b -> EBind1 h (checkEnv e) b
        EBind2 h t e -> EBind2 h (recheckEnv e t) $ checkEnv e            --  E [\(x :: t) -> e]    -> check  E [t]
        EApp1 h e b -> EApp1 h (checkEnv e) b
        EApp2 h a e -> EApp2 h (recheckEnv {-(EApp1 h e _)-}e a) $ checkEnv e              --  E [a x]        ->  check  
        EAssign i x e -> EAssign i (recheckEnv e $ up1E i x) $ checkEnv e                -- __ <i := x>
        CheckType x e -> CheckType (recheckEnv e x) $ checkEnv e
        CheckSame x e -> CheckSame (recheckEnv e x) $ checkEnv e
        CheckAppType h x e y -> CheckAppType h (recheckEnv e x) (checkEnv e) y

    recheckEnv = recheck_ "env"

    recheck_ msg te = \case
        Var k -> Var k
        Lam h a b -> Lam h (ch True te{-ok?-} a) $ ch False (EBind2 (BLam h) a te) b
        Bind h a b -> Bind h (ch (h /= BMeta) te{-ok?-} a) $ ch (isPi h) (EBind2 h a te) b
        App a b -> appf (recheck'' te{-ok?-} a) (recheck'' (EApp2 Visible a te) b)
        Label s@(FunName _ t) as x -> Label s (fst $ foldl appf' ([], t) $ map (recheck'' te) $ reverse as) x   -- todo: te
        ELit l -> ELit l
        TType -> TType
        Con s [] -> Con s []
        Con s as -> reApp $ recheck_ "prim" te $ foldl App (Con s []) as
        TyCon s [] -> TyCon s []
        TyCon s as -> reApp $ recheck_ "prim" te $ foldl App (TyCon s []) as
        CaseFun s [] -> CaseFun s []
        CaseFun s as -> reApp $ recheck_ "fun" te $ foldl App (CaseFun s []) as
        Fun s [] -> Fun s []
        Fun s as -> reApp $ recheck_ "fun" te $ foldl App (Fun s []) as
      where
        reApp (App f x) = case reApp f of
            Fun s args -> Fun s $ args ++ [x]
            CaseFun s args -> CaseFun s $ args ++ [x]
            Con s args -> Con s $ args ++ [x]
            TyCon s args -> TyCon s $ args ++ [x]
        reApp x = x

        -- todo: remove
        appf' (a, Pi h x y) (b, x')
            | x == x' = (b: a, substE "recheck" 0 b y)
            | otherwise = error $ "recheck0 " ++ msg ++ "\nexpected: " ++ showEnvExp te x ++ "\nfound: " ++ showEnvExp te x' ++ "\nin term: " ++ showEnvExp te b

        appf (a, Pi h x y) (b, x')
            | x == x' = app_ a b
            | otherwise = error $ "recheck " ++ msg ++ "\nexpected: " ++ showEnvExp te{-todo-} x ++ "\nfound: " ++ showEnvExp te{-todo-} x' ++ "\nin term: " ++ showEnvExp te (App a b)

        recheck'' te a = (b, expType_ te b) where b = recheck_ "2" te a

        ch False te e = recheck_ "ch" te e
        ch True te e = case recheck'' te e of
            (e', TType) -> e'
            _ -> error $ "recheck'':\n" ++ showEnvExp te e

-------------------------------------------------------------------------------- statements

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
    Meta a t -> bind Hidden a <$> replaceMetas bind t
-- todo: remove   Assign i x t -> bind Hidden (cstr (Var i) $ upE i 1 x) $ upE i 1 $ replaceMetas bind t
    t -> checkMetas t

-- todo: remove
checkMetas = \case
    x@Meta{} -> throwError $ "checkMetas: " ++ show x
    x@Assign{} -> throwError $ "checkMetas: " ++ show x
    Lam h a b -> Lam h <$> checkMetas a <*> checkMetas b
    Bind (BLam _) _ _ -> error "impossible: chm"
    Bind h a b -> Bind h <$> checkMetas a <*> checkMetas b
    Label s xs v -> Label s <$> mapM checkMetas xs <*> pure v
    App a b  -> App <$> checkMetas a <*> checkMetas b
    Fun s xs -> Fun s <$> mapM checkMetas xs
    CaseFun s xs -> CaseFun s <$> mapM checkMetas xs
    Con s xs -> Con s <$> mapM checkMetas xs
    TyCon s xs -> TyCon s <$> mapM checkMetas xs
    x@TType  -> pure x
    x@ELit{} -> pure x
    x@Var{}  -> pure x

getGEnv f = gets (flip EGlobal mempty) >>= f
inferTerm tr f t = getGEnv $ \env -> let env' = f env in smartTrace $ \tr -> 
    fmap (\t -> if tr_light then length (showExp $ fst t) `seq` t else t) $ fmap (addType . recheck env') $ replaceMetas Lam . fst =<< lift (inferN (if tr then trace_level else 0) env' t)
inferType tr t = getGEnv $ \env -> fmap (recheck env) $ replaceMetas Pi . fst =<< lift (inferN (if tr then trace_level else 0) (CheckType TType env) t)

smartTrace :: MonadError String m => (Bool -> m a) -> m a
smartTrace f | trace_level == 0 = f False
smartTrace f = catchError (f False) $ \err ->
    trace_ (unlines
        [ "---------------------------------"
        , err
        , "try again with trace"
        , "---------------------------------"
        ]) $ f True

addToEnv :: Monad m => String -> (Exp, Exp) -> ElabStmtM m ()
addToEnv s (x, t) = (if tr_light then trace_ (s ++ "  ::  " ++ showExp t) else id) $ modify $ Map.alter (Just . maybe (x, t) (const $ error $ "already defined: " ++ s)) s


label' a b c | labellableName a = c
label' a b c = {- trace_ a $ -} label a b c

expType = expType_ (EGlobal initEnv [])
addType x = (x, expType x)

addToEnv_ s (x, t) = addToEnv s (label' (FunName s t) [] x, t)
addToEnv_' s (x, t) x' = let t = expType x' in addToEnv s (fiix (FunName s t) x, traceD ("addToEnv: " ++ s ++ " = " ++ showExp x') t)
addToEnv'' s t ct = addToEnv s (TyCon (TyConName s t ct) [], t)
addToEnv' b s t = addToEnv s (label' (FunName s t) [] $ mkPrim b s t, t)
  where
    mkPrim (Just Nothing) n t = TyCon (TyConName n t $ error "tycon case type") []
    mkPrim (Just (Just i)) n t = Con (ConName n i t) []
    mkPrim Nothing n t = f t
      where
        f (Pi h a b) = Lam h a $ f b
        f _ = TFun n t $ map Var $ reverse [0..arity t - 1]

addToEnv''' _ s t i = addToEnv s (f t, t)
  where
    f (Pi h a b) = Lam h a $ f b
    f _ = TCaseFun s t i $ map Var $ reverse [0..arity t - 1]

downTo n m = map SVar [n+m-1, n+m-2..n]

fiix :: FunName -> Exp -> Exp
fiix n (Lam Hidden _ e) = par 0 e where
    par i (Lam Hidden k z) = Lam Hidden k $ par (i+1) z
    par i (Var i' `App` t `App` f) | i == i' = x where
        x = label n (map Var [0..i-1]) $ f `app_` x

defined' = Map.keys

handleStmt :: MonadFix m => Stmt -> ElabStmtM m ()
handleStmt = \case
  Let n mt (downS 0 -> Just t) -> inferTerm tr id (maybe id (flip SAnn) mt t) >>= addToEnv_ n
  Let n mt t -> inferTerm tr (EBind2 BMeta fixType) (SAppV (SVar 0) $ upS $ SLam Visible (Wildcard SType) $ maybe id (flip SAnn) mt t) >>= \(x, t) ->
    addToEnv_' n (x, t) $ flip app_ (fixDef "f_i_x") x
  Primitive con s t -> gets defined' >>= \d -> inferType tr (addForalls d t) >>= addToEnv' ((\x -> if x then Nothing else Just (-1)) <$> con) s
  Wrong stms -> do
    e <- catchError (False <$ mapM_ handleStmt stms) $ \err -> trace_ ("ok, error catched: " ++ err) $ return True
    when (not e) $ error "not an error"
  Data s ps t_ cs -> do
    af <- gets $ addForalls . (s:) . defined'
    vty <- inferType tr $ addParams ps t_
    let
        pnum' = length $ filter ((== Visible) . fst) ps
        inum = arity vty - length ps

        mkConstr j (cn, af -> ct)
            | c == SGlobal s && take pnum' xs == downTo (length . fst . getParamsS $ ct) pnum'
            = do
                cty <- inferType tr (addParams [(Hidden, x) | (Visible, x) <- ps] ct)
                let     pars = zipWith (\x -> id *** STyped . flip (,) TType . upE x (1+j)) [0..] $ drop (length ps) $ fst $ getParams cty
                        act = length . fst . getParams $ cty
                        acts = map fst . fst . getParams $ cty
                addToEnv' (Just $ Just j) cn cty
                return $ addParams pars
                       $ foldl SAppV (SVar $ j + length pars) $ drop pnum' xs ++ [apps' cn (zip acts $ downTo (j+1+length pars) (length ps) ++ downTo 0 (act- length ps))]
            | otherwise = throwError $ "illegal data definition (parameters are not uniform) " -- ++ show (c, cn, take pnum' xs, act)
            where
                                        (c, map snd -> xs) = getApps $ snd $ getParamsS ct

        motive = addParams (replicate inum (Visible, Wildcard SType)) $
           SPi Visible (apps' s $ zip (map fst ps) (downTo inum $ length ps) ++ zip (map fst $ fst $ getParamsS t_) (downTo 0 inum)) SType

    mdo
        addToEnv'' s vty ct
        cons <- zipWithM mkConstr [0..] cs
        ct <- inferType tr
            ( (\x -> traceD ("type of case-elim before elaboration: " ++ showSExp x) x) $ addParams
                ( [(Hidden, x) | (_, x) <- ps]
                ++ (Visible, motive)
                : map ((,) Visible) cons
                ++ replicate inum (Hidden, Wildcard SType)
                ++ [(Visible, apps' s $ zip (map fst ps) (downTo (inum + length cs + 1) $ length ps) ++ zip (map fst $ fst $ getParamsS t_) (downTo 0 inum))]
                )
            $ foldl SAppV (SVar $ length cs + inum + 1) $ downTo 1 inum ++ [SVar 0]
            )
        addToEnv''' False (Case s) ct (length ps)

-------------------------------------------------------------------------------- parser

addForalls :: [SName] -> SExp -> SExp
addForalls defined x = foldl f x [v | v <- reverse $ freeS x, v `notElem'` defined]
  where
    f e v = SPi Hidden (Wildcard SType) $ substSG v (SVar 0) $ upS e

defined defs = ("Type":) $ flip foldMap defs $ \case
    Wrong _ -> []
    TypeAnn x _ -> [x]
    Let x _ _ -> [x]
    Data x _ _ cs -> x: map fst cs
    Primitive _ x _ -> [x]

type P = ParsecT (IndentStream (CharIndentStream String)) SourcePos Identity

lexer :: Pa.GenTokenParser (IndentStream (CharIndentStream String)) SourcePos Identity
lexer = makeTokenParser $ makeIndentLanguageDef style
  where
    style = Pa.LanguageDef
        { Pa.commentStart   = "{-"
        , Pa.commentEnd     = "-}"
        , Pa.commentLine    = "--"
        , Pa.nestedComments = True
        , Pa.identStart     = letter <|> oneOf "_"
        , Pa.identLetter    = alphaNum <|> oneOf "_'"
        , Pa.opStart        = Pa.opLetter style
        , Pa.opLetter       = oneOf ":!#$%&*+./<=>?@\\^|-~"
        , Pa.reservedOpNames= ["->", "=>", "~", "\\", "|", "::", "<-", "=", "@"]
        , Pa.reservedNames  = ["forall", "data", "builtins", "builtincons", "builtintycons", "_", "case", "of", "where", "import", "module", "let", "in", "infix", "infixr", "infixl", "if", "then", "else", "wrong"]
        , Pa.caseSensitive  = True
        }

position :: P SourcePos
position = getPosition

positionBeforeSpace :: P SourcePos
positionBeforeSpace = getState

optional :: P a -> P (Maybe a)
optional = optionMaybe

keyword :: String -> P ()
keyword = Pa.reserved lexer

operator :: String -> P ()
operator = Pa.reservedOp lexer

lcIdents (Just True, _) = tick <$> Pa.identifier lexer
  where
    tick n | n `elem` ["Type", "Nat", "Float", "Int", "Bool", "IO", "Unit", "Empty", "T2"] = n
           | otherwise = '\'': n
lcIdents _ = Pa.identifier lexer
lcOps = Pa.operator lexer

ident = id
parens    = Pa.parens lexer
braces    = Pa.braces lexer
brackets  = Pa.brackets lexer
commaSep  = Pa.commaSep lexer
commaSep1 = Pa.commaSep1 lexer
dot       = Pa.dot lexer
comma     = Pa.comma lexer
colon     = Pa.colon lexer
natural   = Pa.natural lexer
integer   = Pa.integer lexer
float     = Pa.float lexer
charLiteral   = Pa.charLiteral lexer
stringLiteral = Pa.stringLiteral lexer
whiteSpace    = Pa.whiteSpace lexer

data Extension
    = NoImplicitPrelude
    | NoTypeNamespace
    | NoConstructorNamespace
    deriving (Eq, Ord, Show)

type Name = String
type DefinitionR = Stmt

data Export = ExportModule Name | ExportId Name

data ModuleR
  = Module
  { extensions    :: [Extension]
  , moduleImports :: [Name]    -- TODO
  , moduleExports :: Maybe [Export]
  , definitions   :: [DefinitionR]
  }

(<&>) = flip (<$>)

-------------------------------------------------------------------------------- parser combinators

-- see http://blog.ezyang.com/2014/05/parsec-try-a-or-b-considered-harmful/comment-page-1/#comment-6602
try' s m = try m <?> s
{-
qualified_ id = do
    q <- try' "qualification" $ upperCase' <* dot
    (N t qs n i) <- qualified_ id
    return $ N t (q:qs) n i
  <|>
    id
  where
    upperCase' = (:) <$> satisfy isUpper <*> many (satisfy isAlphaNum)
-}
-------------------------------------------------------------------------------- identifiers

check msg p m = try' msg $ do
    x <- m
    if p x then return x else fail $ msg ++ " expected"

--upperCase, lowerCase, symbols, colonSymbols :: P String
upperCase ns = check "uppercase ident" (isUpper . head) $ ident $ lcIdents ns
lowerCase ns = (if snd ns then check "lowercase ident" (isLower . head) else id) (ident $ lcIdents ns) <|> try (('_':) <$ char '_' <*> ident (lcIdents ns))
symbols   = check "symbols" ((/=':') . head) $ ident lcOps
colonSymbols = "Cons" <$ operator ":" <|> check "symbols" ((==':') . head) (ident lcOps)

--------------------------------------------------------------------------------

pattern ExpN' :: String -> P.Doc -> String
pattern ExpN' s p <- ((,) undefined -> (p, s)) where ExpN' s p = s
pattern ExpN s = s

--typeConstructor, upperCaseIdent, typeVar, var, varId, qIdent, operator', conOperator, moduleName :: P Name
--typeConstructor = upperCase <&> \i -> TypeN' i (Pa.text i)
upperCaseIdent ns = upperCase ns <&> ExpN
--typeVar         = (\p i -> TypeN' i $ P.text $ i ++ show p) <$> position <*> lowerCase
var ns          = (\p i -> ExpN' i $ P.text $ i ++ show p) <$> position <*> lowerCase ns
qIdent ns       = {-qualified_ todo-} (var ns <|> upperCaseIdent ns)
conOperator     = (\p i -> ExpN' i $ P.text $ i ++ show p) <$> position <*> colonSymbols
varId ns        = var ns <|> parens operator'
backquotedIdent = try' "backquoted" $ char '`' *> (ExpN <$> ((:) <$> satisfy isAlpha <*> many (satisfy isAlphaNum))) <* char '`' <* whiteSpace
operator'       = (\p i -> ExpN' i $ P.text $ i ++ show p) <$> position <*> symbols
              <|> conOperator
              <|> backquotedIdent
moduleName      = {-qualified_ todo-} upperCaseIdent (Nothing, False)

-------------------------------------------------------------------------------- fixity declarations

fixityDef :: P [DefinitionR]
fixityDef = do
  dir <-    Nothing      <$ keyword "infix" 
        <|> Just FDLeft  <$ keyword "infixl"
        <|> Just FDRight <$ keyword "infixr"
  localIndentation Gt $ do
    i <- natural
    ns <- commaSep1 operator'
    return [PrecDef n (dir, fromIntegral i) | n <- ns]

--------------------------------------------------------------------------------

export :: Namespace -> P Export
export ns =
        ExportModule <$ keyword "module" <*> moduleName
    <|> ExportId <$> varId ns

parseExtensions :: P [Extension]
parseExtensions = do
    try (string "{-#")
    simpleSpace
    string "LANGUAGE"
    simpleSpace
    s <- commaSep ext
    simpleSpace
    string "#-}"
    simpleSpace
    return s
  where
    simpleSpace = skipMany (satisfy isSpace)

    ext = do
        s <- some $ satisfy isAlphaNum
        case s of
            "NoImplicitPrelude" -> return NoImplicitPrelude
            "NoTypeNamespace"   -> return NoTypeNamespace
            "NoConstructorNamespace" -> return NoConstructorNamespace
            _ -> fail $ "language extension expected instead of " ++ s

parse :: SourceName -> String -> Either String ModuleR
parse f = (show +++ id) . runIdentity . runParserT p (newPos "" 0 0) f . mkIndentStream 0 infIndentation True Ge . mkCharIndentStream
  where
    p = do
        getPosition >>= setState
        setPosition =<< flip setSourceName f <$> getPosition
        exts <- concat <$> many parseExtensions
        let ns = (if NoTypeNamespace `elem` exts then Nothing else Just False, not $ NoConstructorNamespace `elem` exts)
        whiteSpace
        header <- optional $ do
            modn <- keyword "module" *> moduleName
            exps <- optional (parens $ commaSep $ export ns)
            keyword "where"
            return (modn, exps)
        idefs <- many $ keyword "import" *> moduleName
        defs <- parseStmts ns []
        eof
        return $ Module
          { extensions = exts
          , moduleImports = if NoImplicitPrelude `elem` exts
                then idefs
                else ExpN "Prelude": idefs
          , moduleExports = join $ snd <$> header
          , definitions   = removePreExps defs
          }

removePreExps defs = map f defs
  where
    f = \case
        TypeAnn n e -> TypeAnn n $ g e
        Let n m e -> Let n (g <$> m) (g e)
        Data n p t c -> Data n ((id *** g) <$> p) (g t) ((id *** g) <$> c)
        Primitive b n t -> Primitive b n (g t)
        Wrong s -> Wrong $ f <$> s

    g = \case
        e@SGlobal{} -> e
        e@SVar{}    -> e
        e@STyped{}  -> e
        SBind b e f -> SBind b (g e) (g f)
        SApp v e f  -> SApp v (g e) (g f)
        SPreExp (PreExp x) -> g (x defs)

parseType ns mb vs = maybe id option mb $ keyword "::" *> parseTTerm ns PrecLam vs
patVar ns = lcIdents ns <|> "" <$ keyword "_"
typedId ns mb vs = (,) <$> patVar ns <*> localIndentation Gt {-TODO-} (parseType ns mb vs)
typedId' ns mb vs = (,) <$> commaSep1 (patVar ns) <*> localIndentation Gt {-TODO-} (parseType ns mb vs)

telescope ns mb vs = option (vs, []) $ do
    (x, vt) <-
            operator "@" *> (maybe empty (\x -> flip (,) (Hidden, x) <$> patVar ns) mb <|> parens (f Hidden))
        <|> try (parens $ f Visible)
        <|> maybe ((,) "" . (,) Visible <$> parseTerm ns PrecAtom vs) (\x -> flip (,) (Visible, x) <$> patVar ns) mb
    (id *** (vt:)) <$> telescope ns mb (x: vs)
  where
    f v = (id *** (,) v) <$> typedId ns mb vs

parseStmts ns e = pairTypeAnns . concat <$> some (parseStmt ns e)
  where
    pairTypeAnns ds = concatMap f ds where
        f TypeAnn{} = []
        f PrecDef{} = []
        f (Let n Nothing x) | (t: _) <- [t | TypeAnn n' t <- ds, n' == n] = [Let n (Just t) x]
        f x = [x]

parseStmt :: Namespace -> [String] -> P [Stmt]
parseStmt ns e =
     do pure . Wrong <$ keyword "wrong" <*> localIndentation Gt (localAbsoluteIndentation $ parseStmts ns e)
 <|> do con <- Nothing <$ keyword "builtins" <|> Just False <$ keyword "builtincons" <|> Just True <$ keyword "builtintycons"
        fmap concat $ localIndentation Gt $ localAbsoluteIndentation $ many $ do
            (\(vs, t) -> Primitive con <$> vs <*> pure t) <$> typedId' ns Nothing []
 <|> do keyword "data"
        localIndentation Gt $ do
            x <- lcIdents (typeNS ns)
            (nps, ts) <- telescope (typeNS ns) (Just SType) []
            t <- parseType (typeNS ns) (Just SType) nps
            let mkConTy (_, ts') = foldr (uncurry SPi) (foldl SAppV (SGlobal x) $ downTo (length ts') $ length ts) ts'
            cs <-
                 do keyword "where" *> localIndentation Ge (localAbsoluteIndentation $ many $ typedId' ns Nothing nps)
             <|> do keyword "=" *> sepBy ((,) <$> (pure <$> lcIdents ns) <*> (mkConTy <$> telescope (typeNS ns) Nothing nps)) (keyword "|")
            return $ pure $ Data x ts t $ concatMap (\(vs, t) -> (,) <$> vs <*> pure t) cs
 <|> do (vs, t) <- try $ typedId' ns Nothing []
        return $ TypeAnn <$> vs <*> pure t
 <|> fixityDef
 <|> do try' "operator definition" $ do
          a1 <- patVar ns
          n <- operator'
          a2 <- patVar ns
          localIndentation Gt $ do
            t' <- keyword "=" *> parseETerm ns PrecLam (a2: a1: n: e)
            return $ pure $ Let n Nothing $ SLam Visible (Wildcard SType) $ SLam Visible (Wildcard SType) t'
 <|> do n <- varId ns
        localIndentation Gt $ do
            (fe, ts) <- telescope (expNS ns) (Just $ Wildcard SType) (n: e)
            t' <- keyword "=" *> parseETerm ns PrecLam fe
            return $ pure $ Let n Nothing $ foldr (uncurry SLam) t' ts

sapp a (v, b) = SApp v a b

type Namespace = (Maybe Bool {-True: type namespace-}, Bool)

parseTTerm ns = parseTerm $ typeNS ns
parseETerm ns = parseTerm $ expNS ns

typeNS = (True <$) *** id
expNS = (False <$) *** id

parseTerm :: Namespace -> Prec -> [String] -> P SExp
parseTerm ns PrecLam e =
     mkIf <$ keyword "if" <*> parseTerm ns PrecLam e <* keyword "then" <*> parseTerm ns PrecLam e <* keyword "else" <*> parseTerm ns PrecLam e
 <|> do tok <- (SPi . const Hidden <$ keyword "." <|> SPi . const Visible <$ keyword "->") <$ keyword "forall"
           <|> (SLam <$ keyword "->") <$ operator "\\"
        (fe, ts) <- telescope (typeNS ns) (Just $ Wildcard SType) e
        f <- tok
        t' <- parseTTerm ns PrecLam fe
        return $ foldr (uncurry f) t' ts
 <|> do (preExp .) . compileCase <$ keyword "case" <*> parseETerm ns PrecLam e
                                 <* keyword "of" <*> localIndentation Ge (localAbsoluteIndentation $ some $ parseClause ns e)
 <|> do preExp . compileGuardTree . Alts <$> parseSomeGuards ns (const True) e
 <|> do t <- parseTerm ns PrecEq e
        option t $ mkPi <$> (Visible <$ keyword "->" <|> Hidden <$ keyword "=>") <*> pure t <*> parseTTerm ns PrecLam e
parseTerm ns PrecEq e = parseTerm ns PrecAnn e >>= \t -> option t $ SCstr t <$ operator "~" <*> parseTTerm ns PrecAnn e
parseTerm ns PrecAnn e = parseTerm ns PrecOp e >>= \t -> option t $ SAnn t <$> parseType ns Nothing e
parseTerm ns PrecOp e = calculatePrecs <$> p where
    p = parseTerm ns PrecApp e >>= \t -> option (t, []) $ (\op (t', xs) -> (t, (op, t): xs)) <$> operator' <*> p
parseTerm ns PrecApp e = foldl sapp <$> parseTerm ns PrecAtom e <*> many
            (   (,) Visible <$> parseTerm ns PrecAtom e
            <|> (,) Hidden <$ operator "@" <*> parseTTerm ns PrecAtom e)
parseTerm ns PrecAtom e =
     sLit . LChar    <$> charLiteral
 <|> sLit . LString  <$> stringLiteral
 <|> sLit . LFloat   <$> try float
 <|> sLit . LInt . fromIntegral <$ char '#' <*> natural
 <|> toNat <$> natural
 <|> Wildcard (Wildcard SType) <$ keyword "_"
 <|> (\x -> maybe (SGlobal x) SVar $ elemIndex' x e) <$> lcIdents ns
 <|> mkList ns <$> brackets (commaSep $ parseTerm ns PrecLam e)
 <|> mkTuple ns <$> parens (commaSep $ parseTerm ns PrecLam e)
 <|> do keyword "let"
        dcls <- localIndentation Ge (localAbsoluteIndentation $ parseStmts ns e)
        mkLets dcls <$ keyword "in" <*> parseTerm ns PrecLam e

mkIf b t f = SGlobal "PrimIfThenElse" `SAppV` b `SAppV` t `SAppV` f

--------------------------------------------------------------------------------

calculatePrecs :: (SExp, [(SName, SExp)]) -> SExp
calculatePrecs (e, []) = e
calculatePrecs (e, xs) = preExp $ \dcls -> calcPrec (\op x y -> op `SAppV` x `SAppV` y) (\(SGlobal n) -> n) (pm dcls) e $ (SGlobal *** id) <$> xs
  where
    pm dcls = Map.fromList [(n, f) | PrecDef n f <- dcls]

type PrecMap = Map.Map SName Fixity

calcPrec
  :: (Show e)
     => (e -> e -> e -> e)
     -> (e -> Name)
     -> PrecMap
     -> e
     -> [(e, e)]
     -> e
calcPrec app getname ps e es = compileOps [((Nothing, -1), undefined, e)] es
  where
    compileOps [(_, _, e)] [] = e
    compileOps acc [] = compileOps (shrink acc) []
    compileOps acc@((p, g, e1): ee) es_@((op, e'): es) = case compareFixity (pr, op) (p, g) of
        Right GT -> compileOps ((pr, op, e'): acc) es
        Right LT -> compileOps (shrink acc) es_
        Left err -> error err
      where
        pr = fromMaybe --(error $ "no prec for " ++ ppShow n)
                       (Just FDLeft, 9)
                       $ Map.lookup (getname op) ps

    shrink ((_, op, e): (pr, op', e'): es) = (pr, op', app op e' e): es

    compareFixity ((dir, i), op) ((dir', i'), op')
        | i > i' = Right GT
        | i < i' = Right LT
        | otherwise = case (dir, dir') of
            (Just FDLeft, Just FDLeft) -> Right LT
            (Just FDRight, Just FDRight) -> Right GT
            _ -> Left $ "fixity error:" ++ show (op, op')

mkPi Hidden (getTTuple -> Just (n, xs)) b | n == length xs = foldr (sNonDepPi Hidden) b xs
mkPi h a b = sNonDepPi h a b

sNonDepPi h a b = SPi h a $ upS b

getTTuple (SAppV (getTTuple -> Just (n, xs)) z) = Just (n, xs ++ [z]{-todo: eff-})
getTTuple (SGlobal s@(splitAt 6 -> ("'Tuple", reads -> [(n, "")]))) = Just (n :: Int, [])
getTTuple _ = Nothing

mkLets [] e = e
mkLets (Let n Nothing x: ds) e = SLam Visible (Wildcard SType) (substSG n (SVar 0) $ upS $ mkLets ds e) `SAppV` x

mkTuple _ [x] = x
mkTuple (Just True, _) xs = foldl SAppV (SGlobal $ "'Tuple" ++ show (length xs)) xs
mkTuple (Just False, _) xs = foldl SAppV (SGlobal $ "Tuple" ++ show (length xs)) xs
mkTuple _ xs = error "mkTuple"

mkList (Just True, _) [x] = SGlobal "List" `SAppV` x
mkList (Just False, _) xs = foldr (\x l -> SGlobal "Cons" `SAppV` x `SAppV` l) (SGlobal "Nil") xs
mkList _ xs = error "mkList"

parseSomeGuards ns f e = do
    pos <- sourceColumn <$> getPosition <* keyword "|"
    guard $ f pos
    (e', f) <-
         do (e', PCon p vs) <- try $ parsePat ns e <* keyword "<-"
            x <- parseETerm ns PrecEq e
            return (e', \gs' gs -> GuardNode x p vs (Alts gs'): gs)
     <|> do x <- parseETerm ns PrecEq e
            return (e, \gs' gs -> [GuardNode x "True" [] $ Alts gs', GuardNode x "False" [] $ Alts gs])
    f <$> (parseSomeGuards ns (> pos) e' <|> (:[]) . GuardLeaf <$ keyword "->" <*> parseETerm ns PrecLam e')
      <*> (parseSomeGuards ns (== pos) e <|> pure [])

parseClause ns e = do
    (fe, p) <- parsePat ns e
    localIndentation Gt $ (,) p <$ keyword "->" <*> parseETerm ns PrecLam fe

parsePat ns e = do
    i <- lcIdents ns
    is <- many $ patVar ns
    return (reverse is ++ e, PCon i $ map ((:[]) . const PVar) is)

compileCase :: SExp -> [(Pat, SExp)] -> [Stmt] -> SExp
compileCase x cs@((PCon cn _, _): _) adts = (\x -> traceD ("case: " ++ showSExp x) x) $ compileCase' t x [(length vs, e) | (cn, _) <- cns, (PCon c vs, e) <- cs, c == cn]
  where
    (t, cns) = findAdt adts cn

findAdt adts cstr = head $ [(t, csn) | Data t _ _ csn <- adts, cstr `elem` map fst csn] ++ error ("compileCase: " ++ cstr)

pattern SMotive = SLam Visible (Wildcard SType) (Wildcard SType)

compileCase' :: SName -> SExp -> [(Int, SExp)] -> SExp
compileCase' t x cs = foldl SAppV (SGlobal (Case t) `SAppV` SMotive)
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

compileGuardTree :: GuardTree -> [Stmt] -> SExp
compileGuardTree t adts = (\x -> traceD ("  !  :" ++ showSExp x) x) $ guardTreeToCases t
  where
    guardTreeToCases :: GuardTree -> SExp
    guardTreeToCases t = case alts t of
        [] -> SGlobal "undefined"
        GuardLeaf e: _ -> e
        ts@(GuardNode f s _ _: _) ->
          compileCase' t f $
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
    EApp2 h (Lam Visible TType (Var 0)) ts -> envDoc ts $ shApp h (shAtom "tyType") <$> m
    EApp2 h a ts        -> envDoc ts $ shApp h <$> expDoc a <*> m
    EAssign i x ts      -> envDoc ts $ shLet i (expDoc x) m
    CheckType t ts      -> envDoc ts $ shAnn ":" False <$> m <*> expDoc t
    CheckSame t ts      -> envDoc ts $ shCstr <$> m <*> expDoc t
    CheckAppType h t te b      -> envDoc (EApp1 h (CheckType t te) b) m

expDoc :: Exp -> Doc
expDoc e = fmap inGreen <$> f e
  where
    f = \case
        Label s xs _    -> foldl (shApp Visible) (shAtom (inRed $ show s)) <$> mapM f (reverse xs)
        Var k           -> shVar k
        App a b         -> shApp Visible <$> f a <*> f b
        Lam h a b       -> join $ shLam (usedE 0 b) (BLam h) <$> f a <*> pure (f b)
        Bind h a b      -> join $ shLam (usedE 0 b) h <$> f a <*> pure (f b)
        Cstr a b        -> shCstr <$> f a <*> f b
        FunN s xs       -> foldl (shApp Visible) (shAtom s) <$> mapM f xs
        CaseFunN s xs   -> foldl (shApp Visible) (shAtom s) <$> mapM f xs
        ConN s xs       -> foldl (shApp Visible) (shAtom s) <$> mapM f xs
        TyConN s xs     -> foldl (shApp Visible) (shAtom s) <$> mapM f xs
        TType           -> pure $ shAtom "Type"
        ELit l          -> pure $ shAtom $ show l
        Assign i x e    -> shLet i (f x) (f e)

sExpDoc :: SExp -> Doc
sExpDoc = \case
    SGlobal s       -> pure $ shAtom s
    SAnn a b        -> shAnn ":" False <$> sExpDoc a <*> sExpDoc b
    TyType a        -> shApp Visible (shAtom "tyType") <$> sExpDoc a
    SApp h a b      -> shApp h <$> sExpDoc a <*> sExpDoc b
--    Wildcard t      -> shAnn True (shAtom "_") <$> sExpDoc t
    SBind h a b     -> join $ shLam (usedS 0 b) h <$> sExpDoc a <*> pure (sExpDoc b)
    STyped (e, t)   -> expDoc e
    SVar i          -> expDoc (Var i)

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
    | PrecOp
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

splitESC ('\ESC':'[': (span (/='m') -> (a, ~(c: b)))) | c == 'm' = Just (a, b)
splitESC _ = Nothing

instance IsString (Prec -> String) where fromString = const

inGreen = withEsc 32
inBlue = withEsc 34
inRed = withEsc 31
underlined = withEsc 40
withEsc i s = ESC (show i) $ s ++ ESC "" ""

correctEscs = (++ "\ESC[K") . f ["39","49"] where
    f acc (ESC i@(_:_) cs) = ESC i $ f (i:acc) cs
    f (a: acc) (ESC "" cs) = ESC (compOld (cType a) acc) $ f acc cs
    f acc (c: cs) = c: f acc cs
    f acc [] = []

    compOld x xs = head $ filter ((== x) . cType) xs

    cType n
        | "30" <= n && n <= "39" = 0
        | "40" <= n && n <= "49" = 1
        | otherwise = 2


putStrLn_ = putStrLn . correctEscs
trace_ = trace . correctEscs
traceD x = if debug then trace_ x else id

-------------------------------------------------------------------------------- main

unLabel' te@(FunName _ t) s xs = f t [] $ reverse xs
  where
    f (Pi h a b) acc (x: xs) = f (substE "ulr" 0 x b) (x: acc) xs
    f t acc bs = foldl App (g t $ reverse acc) bs

    g (Pi h a b) as = Lam h a $ g b $ map (up1E 0) as ++ [Var 0]
    g _ as = TFun s t as

type TraceLevel = Int
trace_level = 0 :: TraceLevel  -- 0: no trace
tr = False --trace_level >= 2
tr_light = trace_level >= 1

debug = False--True--tr
debug_light = True--False

infer :: GlobalEnv -> [Stmt] -> Either String GlobalEnv
infer env = fmap snd . runExcept . flip runStateT (initEnv <> env) . mapM_ handleStmt

main = do
    args <- getArgs
    let name = head $ args ++ ["tests/accept/DepPrelude"]
        f = name ++ ".lc"
        f' = name ++ ".lci"

    s <- readFile f
    case parse f s >>= infer initEnv . definitions of
      Left e -> putStrLn_ e
      Right (fmap (showExp *** showExp) -> s_) -> do
        putStrLn_ "----------------------"
        b <- doesFileExist f'
        if b then do
            s' <- Map.fromList . read <$> readFile f'
            bs <- sequence $ Map.elems $ Map.mapWithKey (\k -> either (\x -> False <$ putStrLn_ (either (const "missing") (const "new") x ++ " definition: " ++ k)) id) $ Map.unionWithKey check (Left . Left <$> s') (Left . Right <$> s_)
            when (not $ and bs) $ do
                putStr "write changes? (Y/N) "
                x <- getChar
                when (x `elem` ("yY" :: String)) $ do
                    writeFile f' $ show $ Map.toList s_
                    putStrLn_ "Changes written."
          else do
            writeFile f' $ show $ Map.toList s_
            putStrLn_ $ f' ++ " was written."
        putStrLn_ $ maybe "!main was not found" fst $ Map.lookup "main" s_
  where
    check k (Left (Left (x, t))) (Left (Right (x', t')))
        | t /= t' = Right $ False <$ putStrLn_ ("!!! type diff: " ++ k ++ "\n  old:   " ++ t ++ "\n  new:   " ++ t')
        | x /= x' = Right $ False <$ putStrLn_ ("!!! def diff: " ++ k)
        | otherwise = Right $ return True

-------------------------------------------------------------------------------- utils

dropNth i xs = take i xs ++ drop (i+1) xs
iterateN n f e = iterate f e !! n
holes xs = [(as, x, bs) | (as, x: bs) <- zip (inits xs) (tails xs)]

