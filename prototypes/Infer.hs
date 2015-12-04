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
module Infer
    ( Binder (..), SName, Lit(..), Visibility(..), FunName(..), CaseFunName(..), ConName(..), TyConName(..), Export(..), ModuleR(..)
    , Exp (..), GlobalEnv
    , pattern Var, pattern Fun, pattern CaseFun, pattern App
    , parse, removePreExps
    , mkGlobalEnv', joinGlobalEnv', extractGlobalEnv'
    , litType, infer
    ) where

import Data.Monoid
import Data.Maybe
import Data.List
import Data.Char
import Data.String
import qualified Data.Set as Set
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
    | Let SName MFixity (Maybe SExp) SExp
    | Data SName [(Visibility, SExp)]{-parameters-} SExp{-type-} [(SName, SExp)]{-constructor names and types-}
    | Primitive (Maybe Bool{-Just True: type constructor; Just False: constructor; Nothing: function-}) SName SExp{-type-}
    | PrecDef SName Fixity
    | Wrong [Stmt]
    | FunAlt SName [((Visibility, SExp), Pat)] (Maybe SExp) SExp -- eliminated during parsing
    | ValueDef ([SName], Pat) SExp
    deriving (Show)

data SExp
    = SGlobal SName
    | SBind Binder SExp SExp
    | SApp Visibility SExp SExp
    | SLet SExp SExp
    | SVar !Int
    | STyped ExpType
    | SPreExp PreExp    -- eliminated at the end of parsing
  deriving (Eq, Show)

type FixityMap = Map.Map SName Fixity
type ConsMap = Map.Map SName (SName{-type name-}, [(SName, Int)]{-constructors with arities-})
type GlobalEnv' = (FixityMap, ConsMap)

newtype PreExp = PreExp (GlobalEnv' -> SExp)    -- building of expr. needs ADTs and fixity info

instance Eq PreExp where _ == _ = error "(==) on PreExp"
instance Show PreExp where show _ = error "show on PreExp"

preExp :: (GlobalEnv' -> SExp) -> SExp
preExp = SPreExp . PreExp

type Fixity = (Maybe FixityDir, Int)
type MFixity = Maybe Fixity
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
            -- label is used for optional evaluation and indirectly for getting fixity info
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

data ConName = ConName SName MFixity Int Type
instance Show ConName where show (ConName n _ _ _) = n
instance Eq ConName where ConName n _ _ _ == ConName n' _ _ _ = n == n'

conTypeName :: ConName -> TyConName
conTypeName (ConName _ _ _ t) = case snd (getParams t) of
    TyCon n _ -> n
    _ -> error "impossible"

data TyConName = TyConName SName MFixity Type [ConName]{-constructors-} Type{-case type-}
instance Show TyConName where show (TyConName n _ _ _ _) = n
instance Eq TyConName where TyConName n _ _ _ _ == TyConName n' _ _ _ _ = n == n'

data FunName = FunName SName MFixity Type
instance Show FunName where show (FunName n _ _) = n
instance Eq FunName where FunName n _ _ == FunName n' _ _ = n == n'

data CaseFunName = CaseFunName SName Type Int{-num of parameters-}
instance Show CaseFunName where show (CaseFunName n _ _) = n
instance Eq CaseFunName where CaseFunName n _ _ == CaseFunName n' _ _ = n == n'

caseName (c:cs) = toLower c: cs ++ "Case"

type ExpType = (Exp, Type)

pattern Fun a b = Neut (Fun_ a b)
pattern CaseFun a b = Neut (CaseFun_ a b)
pattern FunN a b <- Fun (FunName a _ _) b
pattern CaseFunN a b <- CaseFun (CaseFunName a _ _) b
pattern TFun a t b <- Fun (FunName a _ t) b where TFun a t b = Fun (FunName a Nothing t) b
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

pattern ConN s a   <- Con (ConName s _ _ _) a
pattern TyConN s a <- TyCon (TyConName s _ _ _ _) a
pattern TCon s i t a <- Con (ConName s _ i t) a where TCon s i t a = Con (ConName s Nothing i t) a  -- todo: don't match on type
pattern TTyCon s t a <- TyCon (TyConName s _ t _ _) a where TTyCon s t a = TyCon (TyConName s Nothing t (error "todo: tcn cons 2") $ error "TTyCon") a
pattern TTyCon0 s  <- TyCon (TyConName s _ TType _ _) [] where TTyCon0 s = TyCon (TyConName s Nothing TType (error "todo: tcn cons 3") $ error "TTyCon0") []
pattern Sigma a b  <- TyConN "Sigma" [a, Lam' b] where Sigma a b = TTyCon "Sigma" (error "sigmatype") [a, Lam Visible a{-todo: don't duplicate-} b]
pattern Unit        = TTyCon0 "Unit"
pattern TT          = TCon "TT" 0 Unit []
pattern T2 a b      = TFun "T2" (TType :~> TType :~> TType) [a, b]
pattern T2C a b     = TCon "T2C" (-1) (Unit :~> Unit :~> Unit) [a, b]
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
tTuple3 a b c = TTyCon "'Tuple3" (TType :~> TType :~> TType :~> TType) [a, b, c]
tMat a b c = TTyCon "'Mat" (TNat :~> TNat :~> TType :~> TType) [a, b, c]

t2C TT TT = TT
t2C a b = T2C a b

t2 Unit a = a
t2 a Unit = a
t2 Empty _ = Empty
t2 _ Empty = Empty
t2 a b = TFun "T2" (TType :~> TType :~> TType) [a, b]

pattern EInt a      = ELit (LInt a)
pattern EFloat a    = ELit (LFloat a)

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
    | ELet1 Env SExp
    | ELet2 ExpType Env
    | EGlobal GlobalEnv [Stmt]

    | EBind1' Binder Env Exp            -- todo: move Exp zipper constructor to a separate ADT (if needed)
    | EPrim SName [Exp] Env [Exp]    -- todo: move Exp zipper constructor to a separate ADT (if needed)

    | EAssign Int Exp Env
    | CheckType Exp Env
    | CheckSame Exp Env
    | CheckAppType Visibility Exp Env SExp
  deriving Show

--pattern CheckAppType h t te b = EApp1 h (CheckType t te) b

type GlobalEnv = Map.Map SName (Exp, Type)

extractEnv :: Env -> GlobalEnv
extractEnv = either id extractEnv . parent

parent = \case
    EAssign _ _ x        -> Right x
    EBind2 _ _ x         -> Right x
    EBind1 _ x _         -> Right x
    EBind1' _ x _        -> Right x
    EApp1 _ x _          -> Right x
    EApp2 _ _ x          -> Right x
    ELet1 x _            -> Right x
    ELet2 _ x            -> Right x
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

labellableName (FunName n _ _) = n `elem` ["matchInt", "matchList"] --False

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
    SLet a b -> foldS g f i a <> foldS g f (i+1) b
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
freeE = foldE (\i k -> Set.fromList [k - i | k >= i]) 0

usedS = (getAny .) . foldS mempty ((Any .) . (==))
usedE = (getAny .) . foldE ((Any .) . (==))

mapS = mapS_ (const SGlobal)
mapS_ gg ff = mapS__ gg ff $ \i j -> case ff i $ Var j of
            Var k -> SVar k
            -- x -> STyped x -- todo
mapS__ gg f1 f2 h e = g e where
    g i = \case
        SApp v a b -> SApp v (g i a) (g i b)
        SLet a b -> SLet (g i a) (g (h i) b)
        SBind k a b -> SBind k (g i a) (g (h i) b)
        STyped (x, t) -> STyped (f1 i x, f1 i t)
        SVar j -> f2 i j
        SGlobal x -> gg i x
        x -> error $ "mapS__: " ++ show x

rearrangeS :: (Int -> Int) -> SExp -> SExp
rearrangeS f = mapS__ (const SGlobal) (const id) (\i j -> SVar $ if j < i then j else i + f (j - i)) (+1) 0

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

substSS :: Int -> SExp -> SExp -> SExp
substSS k x = mapS__ (const SGlobal) (error "substSS") (\(i, x) j -> case compare j i of
            EQ -> x
            GT -> SVar $ j - 1
            LT -> SVar j
            ) ((+1) *** upS) (k, x)
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
    f n (ELet2 (x, t) es) = if n == 0 then (BLam Visible{-??-}, up1E 0 t) else id *** up1E 0 $ f (n-1) es
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
    CaseFun (CaseFunName n t pars) (drop (pars + 1) -> ps@(last -> Con (ConName _ _ i _) (drop pars -> vs))) | i /= (-1) -> foldl app_ (ps !! i) vs
    T2 a b -> t2 a b
    FunN "T2C" [a, b] -> t2C a b

    FunN "PrimIfThenElse" [_, xt, xf, ConN "True" []] -> xt
    FunN "PrimIfThenElse" [_, xt, xf, ConN "False" []] -> xf
    FunN "primAdd" [EInt i, EInt j] -> EInt (i + j)
    FunN "primSub" [EInt i, EInt j] -> EInt (i - j)
    FunN "primMod" [EInt i, EInt j] -> EInt (i `mod` j)
    FunN "primSqrt" [EInt i] -> EInt $ round $ sqrt $ fromIntegral i
    FunN "primIntEq" [EInt i, EInt j] -> eBool (i == j)
    FunN "primIntLess" [EInt i, EInt j] -> eBool (i < j)

    FunN "PrimSubS" [_, _, _, _, EFloat x, EFloat y] -> EFloat (x - y)

-- todo: elim
    Fun n@(FunName "natElim" _ _) [a, z, s, Succ x] -> let      -- todo: replace let with better abstraction
                sx = s `app_` x
            in sx `app_` eval (EApp2 Visible sx te) (Fun n [a, z, s, x])
    FunN "natElim" [_, z, s, Zero] -> z
    Fun na@(FunName "finElim" _ _) [m, z, s, n, ConN "FSucc" [i, x]] -> let six = s `app_` i `app_` x-- todo: replace let with better abstraction
        in six `app_` eval (EApp2 Visible six te) (Fun na [m, z, s, i, x])
    FunN "finElim" [m, z, s, n, ConN "FZero" [i]] -> z `app_` i

    FunN "matchInt" [t, f, TyConN "Int" []] -> t
    FunN "matchInt" [t, f, c@LCon] -> f `app_` c
    FunN "matchList" [t, f, TyConN "List" [a]] -> t `app_` a
    FunN "matchList" [t, f, c@LCon] -> f `app_` c

    FunN "Floating" [TVec (Succ (Succ Zero)) TFloat] -> Unit
    FunN "Floating" [TVec (Succ (Succ (Succ (Succ Zero)))) TFloat] -> Unit
    Fun n@(FunName "Eq_" _ _) [TyConN "List" [a]] -> eval te $ Fun n [a]
    FunN "Eq_" [TInt] -> Unit
    FunN "Eq_" [LCon] -> Empty
    FunN "Monad" [TyConN "IO" []] -> Unit
    FunN "Num" [TFloat] -> Unit
    FunN "Num" [TInt] -> Unit
    FunN "ValidFrameBuffer" [n] -> Unit -- todo
    FunN "ValidOutput" [n] -> Unit      -- todo
    FunN "AttributeTuple" [n] -> Unit   -- todo
    FunN "fromInt" [TInt, _, n@EInt{}] -> n

    FunN "VecScalar" [Succ Zero, t] -> t
    FunN "VecScalar" [n@(Succ (Succ _)), t] -> TVec n t
    FunN "TFFrameBuffer" [TyConN "'Image" [n, t]] -> TFrameBuffer n t
    FunN "TFFrameBuffer" [TyConN "'Tuple2" [TyConN "'Image" [i@(fromNat -> Just n), t], TyConN "'Image" [fromNat -> Just n', t']]]
        | n == n' -> TFrameBuffer i $ tTuple2 t t'      -- todo
    FunN "TFFrameBuffer" [TyConN "'Tuple3" [TyConN "'Image" [i@(fromNat -> Just n), t], TyConN "'Image" [fromNat -> Just n', t'], TyConN "'Image" [fromNat -> Just n'', t'']]]
        | n == n' && n == n'' -> TFrameBuffer i $ tTuple3 t t' t''      -- todo
    FunN "FragOps" [TyConN "'FragmentOperation" [t]] -> t
    FunN "FragOps" [TyConN "'Tuple2" [TyConN "'FragmentOperation" [t], TyConN "'FragmentOperation" [t']]] -> tTuple2 t t'
    FunN "FTRepr'" [TyConN "'Tuple2" [TyConN "'Interpolated" [t], TyConN "'Interpolated" [t']]] -> tTuple2 t t'          -- todo
    FunN "FTRepr'" [TyConN "'Tuple2" [TyConN "'List" [t], TyConN "'List" [t']]] -> tTuple2 t t'          -- todo
    FunN "FTRepr'" [TyConN "'Interpolated" [t]] -> t          -- todo
    FunN "ColorRepr" [TTuple0] -> TTuple0
    FunN "ColorRepr" [t@NoTup] -> TTyCon "'Color" (TType :~> TType) [t] -- todo
    FunN "JoinTupleType" [a@TyConN{}, TTuple0] -> a
    FunN "JoinTupleType" [a@NoTup, b@NoTup] -> tTuple2 a b             -- todo
    FunN "TFMat" [TVec i a, TVec j a'] | a == a' -> tMat i j a       -- todo
    FunN "MatVecElem" [TVec _ a] -> a
    FunN "MatVecElem" [TyConN "'Mat" [_, _, a]] -> a
    FunN "MatVecScalarElem" [a@TFloat] -> a
    FunN "fromInt" [TFloat, _, EInt i] -> EFloat $ fromIntegral i

    x -> x

pattern TTuple0 = TTyCon "'Tuple0" TType []
pattern NoTup <- (noTup -> True)

noTup (TyConN s _) = take 6 s /= "'Tuple" -- todo
noTup _ = False

fromNat :: Exp -> Maybe Int
fromNat Zero = Just 0
fromNat (Succ n) = (1 +) <$> fromNat n

-- todo
coe a b c d | a == b = d        -- todo
coe a b c d = Coe a b c d

reflCstr te = \case
{-
    Unit -> TT
    TType -> TT  -- ?
    Con n xs -> foldl (t2C te{-todo: more precise env-}) TT $ map (reflCstr te{-todo: more precise env-}) xs
    TyCon n xs -> foldl (t2C te{-todo: more precise env-}) TT $ map (reflCstr te{-todo: more precise env-}) xs
    x -> {-error $ "reflCstr: " ++ show x-} ReflCstr x
-}
    x -> TT

cstr = cstr__ []
  where
    cstr__ = cstr_

    cstr_ [] a a' | a == a' = Unit
    cstr_ ns TType TType = Unit
    cstr_ ns (Con a []) (Con a' []) | a == a' = Unit
    cstr_ ns (TyCon a []) (TyCon a' []) | a == a' = Unit
    cstr_ ns (Var i) (Var i') | i == i', i < length ns = Unit
    cstr_ (_: ns) (downE 0 -> Just a) (downE 0 -> Just a') = cstr__ ns a a'
    cstr_ ((t, t'): ns) (UApp (downE 0 -> Just a) (UVar 0)) (UApp (downE 0 -> Just a') (UVar 0)) = traceInj2 (a, "V0") (a', "V0") $ cstr__ ns a a'
    cstr_ ((t, t'): ns) a (UApp (downE 0 -> Just a') (UVar 0)) = traceInj (a', "V0") a $ cstr__ ns (Lam Visible t a) a'
    cstr_ ((t, t'): ns) (UApp (downE 0 -> Just a) (UVar 0)) a' = traceInj (a, "V0") a' $ cstr__ ns a (Lam Visible t' a')
    cstr_ ns (Lam h a b) (Lam h' a' b') | h == h' = t2 (cstr__ ns a a') (cstr__ ((a, a'): ns) b b')
    cstr_ ns (UBind h a b) (UBind h' a' b') | h == h' = t2 (cstr__ ns a a') (cstr__ ((a, a'): ns) b b')
    cstr_ ns (unApp -> Just (a, b)) (unApp -> Just (a', b')) = traceInj2 (a, show b) (a', show b') $ t2 (cstr__ ns a a') (cstr__ ns b b')
--    cstr_ ns (Label f xs _) (Label f' xs' _) | f == f' = foldr1 T2 $ zipWith (cstr__ ns) xs xs'
    cstr_ ns (FunN "VecScalar" [a, b]) (TVec a' b') = t2 (cstr__ ns a a') (cstr__ ns b b')
    cstr_ ns (FunN "VecScalar" [a, b]) (FunN "VecScalar" [a', b']) = t2 (cstr__ ns a a') (cstr__ ns b b')
    cstr_ ns (FunN "VecScalar" [a, b]) t@(TTyCon0 n) | isElemTy n = t2 (cstr__ ns a (Succ Zero)) (cstr__ ns b t)
    cstr_ ns t@(TTyCon0 n) (FunN "VecScalar" [a, b]) | isElemTy n = t2 (cstr__ ns a (Succ Zero)) (cstr__ ns b t)
    cstr_ ns@[] (FunN "TFMat" [x, y]) (TyConN "'Mat" [i, j, a]) = t2 (cstr__ ns x (TVec i a)) (cstr__ ns y (TVec j a))
    cstr_ ns@[] (TyConN "'Tuple2" [x, y]) (FunN "JoinTupleType" [x'@NoTup, y']) = t2 (cstr__ ns x x') (cstr__ ns y y')
    cstr_ ns@[] (TyConN "'Color" [x]) (FunN "ColorRepr" [x']) = cstr__ ns x x'
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

    isElemTy n = n `elem` ["Bool", "Float", "Int"]


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
    Label s@(FunName _ _ t) ts _ -> foldl app t $ reverse ts
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
    infer te exp = (if tracelevel >= 1 then trace_ ("infer: " ++ showEnvSExp te exp) else id) $ (if debug then fmap (recheck' "infer" te *** id) else id) $ case exp of
        SVar i      -> focus te (Var i)
        STyped et   -> focus_ te et
        SGlobal s   -> focus_ te =<< getDef te s
        SApp  h a b -> infer (EApp1 h te b) a
        SLet a b    -> infer (ELet1 te b) a -- infer te (SLam Visible (Wildcard SType) b `SAppV` a)
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
    focus_ env (e, et) = (if tracelevel >= 1 then trace_ $ "focus: " ++ showEnvExp env e else id) $ (if debug then fmap (recheck' "focus" env *** id) else id) $ case env of
        CheckSame x te -> focus_ (EBind2 BMeta (cstr x e) te) (up1E 0 e, up1E 0 et)
        CheckAppType h t te b
            | Pi h' x (downE 0 -> Just y) <- et, h == h' -> focus_ (EBind2 BMeta (cstr t y) $ EApp1 h te b) (up1E 0 e, up1E 0 et)
            | otherwise -> focus_ (EApp1 h (CheckType t te) b) (e, et)
        EApp1 h te b
            | Pi h' x y <- et, h == h' -> checkN (EApp2 h e te) b x
            | Pi Hidden x y  <- et, h == Visible -> focus_ (EApp1 Hidden env $ Wildcard $ Wildcard SType) (e, et)  --  e b --> e _ b
            | otherwise -> infer (CheckType (Var 2) $ cstr' h (upE 0 2 et) (Pi Visible (Var 1) (Var 1)) (upE 0 2 e) $ EBind2 BMeta TType $ EBind2 BMeta TType te) (upS__ 0 3 b)
        ELet1 te b -> replaceMetas "let" Lam e >>= \e' -> infer (ELet2 (addType_ te e') te) b
        ELet2 (x, xt) te -> focus_ te (app_ (Lam Visible xt e) x, et)
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
                in focus_ te' $ both (substE_ te' 2 (t2C (Var 1) (Var 0)) . upE 0 2) (e, et)
            | Cstr a b <- tt, a == b  -> refocus te $ both (substE "inferN2" 0 TT) (e, et)
            | Cstr a b <- tt, Just r <- cst a b -> r
            | Cstr a b <- tt, Just r <- cst b a -> r
            | EBind2 h x te' <- te, h /= BMeta, Just b' <- downE 0 tt
                            -> refocus (EBind2 h (up1E 0 x) $ EBind2 BMeta b' te') $ both (substE "inferN3" 2 (Var 0) . up1E 0) (e, et)
            | ELet2 (x, xt) te' <- te, Just b' <- downE 0 tt
                            -> refocus (ELet2 (up1E 0 x, up1E 0 xt) $ EBind2 BMeta b' te') $ both (substE "inferN32" 2 (Var 0) . up1E 0) (e, et)
            | EBind1 h te' x  <- te -> refocus (EBind1 h (EBind2 BMeta tt te') $ upS__ 1 1 x) (e, et)
            | ELet1 te' x     <- te, usedE 0 e {-todo: tweak?-}
                                    -> refocus (ELet1 (EBind2 BMeta tt te') $ upS__ 1 1 x) (e, et)
            | CheckAppType h t te' x <- te -> refocus (CheckAppType h (up1E 0 t) (EBind2 BMeta tt te') $ upS x) (e, et)
            | EApp1 h te' x   <- te -> refocus (EApp1 h (EBind2 BMeta tt te') $ upS x) (e, et)
            | EApp2 h x te'   <- te -> refocus (EApp2 h (up1E 0 x) $ EBind2 BMeta tt te') (e, et)
            | CheckType t te' <- te -> refocus (CheckType (up1E 0 t) $ EBind2 BMeta tt te') (e, et)
            | otherwise             -> focus_ te (Bind BMeta tt e, et {-???-})
          where
            cst x = \case
                Var i | fst (varType "X" i te) == BMeta
                      , Just y <- downE i x
                      -> Just $ assign'' te i y $ both (substE_ te 0 ({-ReflCstr y-}TT) . substE_ te (i+1) (up1E 0 y)) (e, et)
                _ -> Nothing
        EBind2 (BLam h) a te -> focus_ te (Lam h a e, Pi h a e)
        EBind2 (BPi h) a te -> focus_ te (Bind (BPi h) a e, TType)
        EAssign i b te -> case te of
            EBind2 h x te' | i > 0, Just b' <- downE 0 b
                              -> refocus' (EBind2 h (substE "inferN5" (i-1) b' x) (EAssign (i-1) b' te')) (e, et)
            ELet2 (x, xt) te' | i > 0, Just b' <- downE 0 b
                              -> refocus' (ELet2 (substE "inferN51" (i-1) b' x, substE "inferN52" (i-1) b' xt) (EAssign (i-1) b' te')) (e, et)
            ELet1 te' x       -> refocus' (ELet1 (EAssign i b te') $ substS (i+1) (up1E 0 b) x) (e, et)
            EBind1 h te' x    -> refocus' (EBind1 h (EAssign i b te') $ substS (i+1) (up1E 0 b) x) (e, et)
            CheckAppType h t te' x -> refocus' (CheckAppType h (substE "inferN6" i b t) (EAssign i b te') $ substS i b x) (e, et)
            EApp1 h te' x     -> refocus' (EApp1 h (EAssign i b te') $ substS i b x) (e, et)
            EApp2 h x te'     -> refocus' (EApp2 h (substE_ te'{-todo: precise env-} i b x) $ EAssign i b te') (e, et)
            CheckType t te'   -> refocus' (CheckType (substE "inferN8" i b t) $ EAssign i b te') (e, et)
            EAssign j a te' | i < j
                              -> focus_ (EAssign (j-1) (substE "ea" i b a) $ EAssign i (upE (j-1) 1 b) te') (e, et)
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

type Message = String

recheck :: Message -> Env -> Exp -> Exp
recheck msg e = if debug_light then recheck' msg e else id

recheck' :: Message -> Env -> Exp -> Exp
recheck' msg' e x = {-length (showExp e') `seq` -} e'
  where
    e' = recheck_ "main" (checkEnv e) x
    checkEnv = \case
        e@EGlobal{} -> e
        EBind1 h e b -> EBind1 h (checkEnv e) b
        EBind2 h t e -> EBind2 h (recheckEnv e t) $ checkEnv e            --  E [\(x :: t) -> e]    -> check  E [t]
        ELet1 e b -> ELet1 (checkEnv e) b
        ELet2 (x, t) e -> ELet2 (recheckEnv e x, recheckEnv e t{-?-}) $ checkEnv e
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
        App a b -> appf (recheck'' "app1" te{-ok?-} a) (recheck'' "app2" (EApp2 Visible a te) b)
        Label s@(FunName _ _ t) as x -> Label s (fst $ foldl appf' ([], t) $ map (recheck'' "label" te) $ reverse as) x   -- todo: te
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
            | otherwise = error_ $ "recheck0 " ++ msg ++ "\nexpected: " ++ showEnvExp te x ++ "\nfound: " ++ showEnvExp te x' ++ "\nin term: " ++ showEnvExp te b

        appf (a, Pi h x y) (b, x')
            | x == x' = app_ a b
            | otherwise = error_ $ "recheck " ++ msg' ++ "; " ++ msg ++ "\nexpected: " ++ showEnvExp te{-todo-} x ++ "\nfound: " ++ showEnvExp te{-todo-} x' ++ "\nin term: " ++ showEnvExp te (App a b)

        recheck'' msg te a = (b, expType_ te b) where b = recheck_ msg te a

        ch False te e = recheck_ "ch" te e
        ch True te e = case recheck'' "check" te e of
            (e', TType) -> e'
            _ -> error_ $ "recheck'':\n" ++ showEnvExp te e

-------------------------------------------------------------------------------- statements

addParams ps t = foldr (uncurry SPi) t ps

getParamsS (SPi h t x) = ((h, t):) *** id $ getParamsS x
getParamsS x = ([], x)

getApps (SApp h a b) = id *** (++ [(h, b)]) $ getApps a -- todo: make it efficient
getApps x = (x, [])

arity :: Exp -> Int
arity = length . arity_
arity_ = map fst . fst . getParams

getParams :: Exp -> ([(Visibility, Exp)], Exp)
getParams (Pi h a b) = ((h, a):) *** id $ getParams b
getParams x = ([], x)

apps a b = foldl SAppV (SGlobal a) b
apps' a b = foldl sapp (SGlobal a) b

replaceMetas err bind = \case
    Meta a t -> bind Hidden a <$> replaceMetas err bind t
-- todo: remove   Assign i x t -> bind Hidden (cstr (Var i) $ upE i 1 x) $ upE i 1 $ replaceMetas bind t
    t -> checkMetas err t

-- todo: remove
checkMetas err = \case
    x@Meta{} -> throwError $ "checkMetas " ++ err ++ ": " ++ show x
    x@Assign{} -> throwError $ "checkMetas " ++ err ++ ": " ++ show x
    Lam h a b -> Lam h <$> f a <*> f b
    Bind (BLam _) _ _ -> error "impossible: chm"
    Bind h a b -> Bind h <$> f a <*> f b
    Label s xs v -> Label s <$> mapM f xs <*> pure v
    App a b  -> App <$> f a <*> f b
    Fun s xs -> Fun s <$> mapM f xs
    CaseFun s xs -> CaseFun s <$> mapM f xs
    Con s xs -> Con s <$> mapM f xs
    TyCon s xs -> TyCon s <$> mapM f xs
    x@TType  -> pure x
    x@ELit{} -> pure x
    x@Var{}  -> pure x
  where
    f = checkMetas err

getGEnv f = gets (flip EGlobal mempty) >>= f
inferTerm msg tr f t = getGEnv $ \env -> let env' = f env in smartTrace $ \tr -> 
    fmap (\t -> if tr_light then length (showExp $ fst t) `seq` t else t) $ fmap (addType . recheck msg env') $ replaceMetas "lam" Lam . fst =<< lift (inferN (if tr then trace_level else 0) env' t)
inferType tr t = getGEnv $ \env -> fmap (recheck "inferType" env) $ replaceMetas "pi" Pi . fst =<< lift (inferN (if tr then trace_level else 0) (CheckType TType env) t)

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
--addToEnv s (x, t) | Just msg <- ambiguityCheck s t = throwError msg
addToEnv s (x, t) = maybe id (\msg -> trace_ msg) (ambiguityCheck s t) $ (if tr_light then trace_ (s ++ "  ::  " ++ showExp t) else id) $ modify $ Map.alter (Just . maybe (x, t) (const $ error $ "already defined: " ++ s)) s

-- Ambiguous: (Int ~ F a) => Int
-- Not ambiguous: (Show a, a ~ F b) => b
--ambiguityCheck :: Doc -> TCMS Exp -> TCMS Exp
ambiguityCheck s ty = do
    case [(n, c) | (n, c) <- hid, not $ any (`Set.member` defined) $ Set.insert n $ freeE c] of
        [] -> Nothing
        err -> Just $ s ++ " has ambiguous type:\n" ++ showExp ty ++ "\nproblematic vars:\n" ++ show err
  where
    defined = dependentVars hid $ freeE ty'

    i = length hid_
    hid = zipWith (\k t -> (k, upE 0 (k+1) t)) (reverse [0..i-1]) hid_

    (hid_, ty') = f ty
    f (Pi Hidden a b) = (a:) *** id $ f b
    f t = ([], t)

-- compute dependent type vars in constraints
-- Example:  dependentVars [(a, b) ~ F b c, d ~ F e] [c] == [a,b,c]
dependentVars :: [(Int, Exp)] -> Set.Set Int -> Set.Set Int
dependentVars ie s = cycle mempty s
  where
    freeVars = freeE

    cycle acc s
        | Set.null s = acc
        | otherwise = cycle (acc <> s) (grow s Set.\\ acc)

    grow = flip foldMap ie $ \case
      (n, t) -> (Set.singleton n <-> freeVars t) <> case t of
        Cstr ty f -> freeVars ty <-> freeVars f
--        Split a b c -> freeVars a <-> (freeVars b <> freeVars c)
--        CUnify{} -> mempty --error "dependentVars: impossible" 
        _ -> mempty
--      (n, ISubst False x) -> (Set.singleton n <-> freeVars x)
      where
        a --> b = \s -> if Set.null $ a `Set.intersection` s then mempty else b
        a <-> b = (a --> b) <> (b --> a)

label' a b c | labellableName a = c
label' a b c = {- trace_ a $ -} label a b c

expType = expType_ (EGlobal initEnv [])
addType x = (x, expType x)
addType_ te x = (x, expType_ te x)

addToEnv_ s mf (x, t) = addToEnv s (label' (FunName s mf t) [] x, t)
addToEnv_' s mf (x, t) x' = let t = expType x' in addToEnv s (fiix (FunName s mf t) x, traceD ("addToEnv: " ++ s ++ " = " ++ showExp x') t)
addToEnv' b s t = addToEnv s (label' (FunName s Nothing t) [] $ mkPrim b s t, t)
  where
    mkPrim (Just Nothing) n t = TyCon (TyConName n Nothing t (error "todo: tcn cons 1") $ error "tycon case type") []
    mkPrim (Just (Just i)) n t = Con (ConName n Nothing i t) []
    mkPrim Nothing n t = f t
      where
        f (Pi h a b) = Lam h a $ f b
        f _ = TFun n t $ map Var $ reverse [0..arity t - 1]

downTo n m = map SVar [n+m-1, n+m-2..n]

fiix :: FunName -> Exp -> Exp
fiix n (Lam Hidden _ e) = par 0 e where
    par i (Lam Hidden k z) = Lam Hidden k $ par (i+1) z
    par i (Var i' `App` t `App` f) | i == i' = x where
        x = label n (map Var [0..i-1]) $ f `app_` x

defined' = Map.keys

addF = gets $ addForalls . defined'

handleStmt :: MonadFix m => Stmt -> ElabStmtM m ()
handleStmt = \case
  PrecDef{} -> return ()
  Let n mf mt (downS 0 -> Just t) -> addF >>= \af -> inferTerm n tr id (maybe id (flip SAnn . af) mt t) >>= addToEnv_ n mf
  Let n mf mt t -> addF >>= \af -> inferTerm n tr (EBind2 BMeta fixType) (SAppV (SVar 0) $ upS $ SLam Visible (Wildcard SType) $ maybe id (flip SAnn . af) mt t) >>= \(x, t) ->
    addToEnv_' n mf (x, t) $ flip app_ (fixDef "f_i_x") x
  Primitive con s t -> addF >>= \af -> inferType tr (af t) >>= addToEnv' ((\x -> if x then Nothing else Just (-1)) <$> con) s
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
                        conn = ConName cn Nothing j cty
                addToEnv cn (Con conn [], cty)
                return ( conn
                       , addParams pars
                       $ foldl SAppV (SVar $ j + length pars) $ drop pnum' xs ++ [apps' cn (zip acts $ downTo (j+1+length pars) (length ps) ++ downTo 0 (act- length ps))]
                       )
            | otherwise = throwError $ "illegal data definition (parameters are not uniform) " -- ++ show (c, cn, take pnum' xs, act)
            where
                                        (c, map snd -> xs) = getApps $ snd $ getParamsS ct

        motive = addParams (replicate inum (Visible, Wildcard SType)) $
           SPi Visible (apps' s $ zip (map fst ps) (downTo inum $ length ps) ++ zip (map fst $ fst $ getParamsS t_) (downTo 0 inum)) SType

        addToEnv'' s t cs ct = addToEnv s (TyCon (TyConName s Nothing t cs ct) [], t)
        addToEnv''' _ s t i = addToEnv s (f t, t)
          where
            f (Pi h a b) = Lam h a $ f b
            f _ = TCaseFun s t i $ map Var $ reverse [0..arity t - 1]
    mdo
        addToEnv'' s vty (map fst cons) ct
        cons <- zipWithM mkConstr [0..] cs
        ct <- inferType tr
            ( (\x -> traceD ("type of case-elim before elaboration: " ++ showSExp x) x) $ addParams
                ( [(Hidden, x) | (_, x) <- ps]
                ++ (Visible, motive)
                : map ((,) Visible . snd) cons
                ++ replicate inum (Hidden, Wildcard SType)
                ++ [(Visible, apps' s $ zip (map fst ps) (downTo (inum + length cs + 1) $ length ps) ++ zip (map fst $ fst $ getParamsS t_) (downTo 0 inum))]
                )
            $ foldl SAppV (SVar $ length cs + inum + 1) $ downTo 1 inum ++ [SVar 0]
            )
        addToEnv''' False (caseName s) ct (length ps)

-------------------------------------------------------------------------------- parser

addForalls :: [SName] -> SExp -> SExp
addForalls defined x = foldl f x [v | v <- reverse $ freeS x, v `notElem'` defined]
  where
    f e v = SPi Hidden (Wildcard SType) $ substSG v (SVar 0) $ upS e

defined defs = ("Type":) $ flip foldMap defs $ \case
    Wrong _ -> []
    TypeAnn x _ -> [x]
    Let x _ _ _ -> [x]
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
        , Pa.reservedOpNames= ["->", "=>", "~", "\\", "|", "::", "<-", "=", "@", ".."]
        , Pa.reservedNames  = ["forall", "data", "builtins", "builtincons", "builtintycons", "_", "case", "of", "where", "import", "module", "let", "in", "infix", "infixr", "infixl", "if", "then", "else", "class", "instance", "wrong"]
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
upperCase (Nothing, _) = mzero -- todo
upperCase ns = (if snd ns then check "uppercase ident" (isUpper . head) else id) $ ident $ lcIdents ns
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
moduleName      = {-qualified_ todo-} upperCaseIdent (Just False, False)

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
          , definitions   = defs
          }

removePreExpsGT :: GlobalEnv' -> GuardTree -> GuardTree
removePreExpsGT ge = \case
    GuardNode e n p t -> GuardNode (f e) n p $ g t
    Alts ts -> Alts $ map g ts
    GuardLeaf e -> GuardLeaf $ f e
  where
    g = removePreExpsGT ge
    f = removePreExpsE ge

removePreExps :: GlobalEnv' -> [Stmt] -> [Stmt]
removePreExps ge = map f
  where
    f = \case
        TypeAnn n e -> TypeAnn n $ g e
        Let n mf m e -> Let n mf (g <$> m) (g e)
        Data n p t c -> Data n ((id *** g) <$> p) (g t) ((id *** g) <$> c)
        Primitive b n t -> Primitive b n (g t)
        Wrong s -> Wrong $ f <$> s
        ValueDef p e -> ValueDef p $ g e
        p@PrecDef{} -> p

    g = removePreExpsE ge

removePreExpsE :: GlobalEnv' -> SExp -> SExp
removePreExpsE ge = g where
    g = \case
        e@SGlobal{} -> e
        e@SVar{}    -> e
        e@STyped{}  -> e
        SBind b e f -> SBind b (g e) (g f)
        SLet e f    -> SLet (g e) (g f)
        SApp v e f  -> SApp v (g e) (g f)
        SPreExp (PreExp x) -> g (x ge)

parseType ns mb vs = maybe id option mb $ keyword "::" *> parseTTerm ns PrecLam vs
patVar ns = lcIdents ns <|> "" <$ keyword "_"
patVar2 ns = lowerCase ns <|> "" <$ keyword "_"
typedId ns mb vs = (,) <$> patVar ns <*> localIndentation Gt {-TODO-} (parseType ns mb vs)
typedId' ns mb vs = (,) <$> commaSep1 (varId ns <|> patVar ns) <*> localIndentation Gt {-TODO-} (parseType ns mb vs)

telescope ns mb vs = option (vs, []) $ do
    (x, vt) <-
            operator "@" *> (maybe empty (\x -> flip (,) (Hidden, x) <$> patVar ns) mb <|> parens (f Hidden))
        <|> try (parens $ f Visible)
        <|> maybe ((,) "" . (,) Visible <$> parseTerm ns PrecAtom vs) (\x -> flip (,) (Visible, x) <$> patVar ns) mb
    (id *** (vt:)) <$> telescope ns mb (x: vs)
  where
    f v = (id *** (,) v) <$> typedId ns mb vs

parseClause ns e = do
    (fe, p) <- pattern' ns e
    localIndentation Gt $ (,) p <$ keyword "->" <*> parseETerm ns PrecLam fe

patternAtom ns vs =
     (,) vs . flip ViewPat eqPP . SAppV (SGlobal "primCompareFloat") . sLit . LFloat <$> try float
 <|> (,) vs . flip ViewPat eqPP . SAppV (SGlobal "primCompareInt") . sLit . LInt . fromIntegral <$> natural
 <|> (,) <$> ((:vs) <$> patVar2 ns) <*> (pure PVar)
 <|> (,) vs . flip PCon [] <$> upperCaseIdent ns
 <|> (id *** mkListPat) <$> brackets (patlist ns vs <|> pure (vs, []))
 <|> (id *** mkTupPat) <$> parens (patlist ns vs)

eqPP = ParPat [PCon "EQ" []]
truePP = ParPat [PCon "True" []]

patlist ns vs = commaSep' (\vs -> (\(vs, p) t -> (vs, patType p t)) <$> pattern' ns vs <*> parseType ns (Just $ Wildcard SType) vs) vs

mkListPat (p: ps) = PCon "Cons" $ map (ParPat . (:[])) [p, mkListPat ps]
mkListPat [] = PCon "Nil" []

pattern' ns vs =
     {-((,) vs . PLit . LFloat) <$> try float
 <|> -}pCon <$> upperCaseIdent ns <*> patterns ns vs
 <|> (patternAtom ns vs >>= \(vs, p) -> option (vs, p) ((id *** (\p' -> PCon "Cons" (ParPat . (:[]) <$> [p, p']))) <$ operator ":" <*> patternAtom ns vs))

patterns ns vs =
     do patternAtom ns vs >>= \(vs, p) -> patterns ns vs >>= \(vs, ps) -> pure (vs, ParPat [p]: ps)
 <|> pure (vs, [])

pCon i (vs, x) = (vs, PCon i x)

patType p (Wildcard SType) = p
patType p t = PatType (ParPat [p]) t

mkTupPat :: [Pat] -> Pat
mkTupPat [x] = x
mkTupPat ps = PCon ("Tuple" ++ show (length ps)) (ParPat . (:[]) <$> ps)

commaSep' p vs =
     p vs >>= \(vs, x) -> (\(vs, xs) -> (vs, x: xs)) <$ comma <*> commaSep' p vs
                      <|> pure (vs, [x])

telescope' ns vs = option (vs, []) $ do
    (vs', vt) <-
            operator "@" *> (f Hidden <$> patternAtom ns vs)
        <|> f Visible <$> patternAtom ns vs
    (id *** (vt:)) <$> telescope' ns vs'
  where
    f h (vs, PatType (ParPat [p]) t) = (vs, ((h, t), p))
    f h (vs, p) = (vs, ((h, Wildcard SType), p))

parseStmts ns e = pairTypeAnns . concat <$> some (parseStmt ns e)
  where
    pairTypeAnns ds = concatMap f $ groupBy h ds where
        h (FunAlt n _ _ _) (FunAlt m _ _ _) = m == n
        h _ _ = False

        f [TypeAnn{}] = []
        f [p@PrecDef{}] = [p]

        f fs@((FunAlt n vs _ _): _) = [Let n (listToMaybe [t | PrecDef n' t <- ds, n' == n])
                                   (listToMaybe [t | TypeAnn n' t <- ds, n' == n])
                                   (foldr (uncurry SLam) (compileGuardTree' $ Alts
                                        [ compilePatts (zip (map snd vs) $ reverse [0..length vs - 1]) gs x
                                        | FunAlt _ vs gs x <- fs
                                        ]) (map fst vs))
                            ]
        f x = x

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
 <|> do (n, (fe, ts)) <-
            do try' "operator definition" $ do
                (e', a1) <- patternAtom ns ("": e)
                n <- operator'
                (e'', a2) <- patternAtom ns $ take (length e' - length e) e' ++ n: e
                localIndentation Gt $ lookAhead $ operator "=" <|> operator "|"
                return (n, (e'', (,) (Visible, Wildcard SType) <$> [a1, a2]))
          <|> do try $ do
                    n <- varId ns
                    localIndentation Gt $ (,) n <$> telescope' (expNS ns) (n: e) <* (lookAhead $ operator "=" <|> operator "|")
        localIndentation Gt $ do
            gu <- option Nothing $ do
                keyword "|"
                Just <$> parseETerm ns PrecOp fe
            keyword "="
            rhs <- parseETerm ns PrecLam fe
            f <- option id $ do
                keyword "where"
                dcls <- localIndentation Ge (localAbsoluteIndentation $ parseStmts ns fe)
                return $ mkLets' dcls
            return $ pure $ FunAlt n ts gu $ f rhs
 <|> do (e', p) <- try $ pattern' ns e <* keyword "="
        localIndentation Gt $ do
            ex <- parseETerm ns PrecLam e'
            return $ pure $ ValueDef (take (length e' - length e) e', p) ex

pattern TPVar t = ParPat [PatType (ParPat [PVar]) t]

sapp a (v, b) = SApp v a b

type Namespace = (Maybe Bool {-True: type namespace-}, Bool)

parseTTerm ns = parseTerm $ typeNS ns
parseETerm ns = parseTerm $ expNS ns

typeNS = (True <$) *** id
expNS = (False <$) *** id

parseTerm :: Namespace -> Prec -> [String] -> P SExp
parseTerm ns PrecLam e =
     mkIf <$ keyword "if" <*> parseTerm ns PrecLam e <* keyword "then" <*> parseTerm ns PrecLam e <* keyword "else" <*> parseTerm ns PrecLam e
 <|> do (tok, ns) <- (SPi . const Hidden <$ keyword "." <|> SPi . const Visible <$ keyword "->", typeNS ns) <$ keyword "forall"
        (fe, ts) <- telescope ns (Just $ Wildcard SType) e
        f <- tok
        t' <- parseTerm ns PrecLam fe
        return $ foldr (uncurry f) t' ts
 <|> do (tok, ns) <- (patLam_ <$ keyword "->", expNS ns) <$ operator "\\"
        (fe, ts) <- telescope' ns e
        f <- tok
        t' <- parseTerm ns PrecLam fe
        return $ foldr (uncurry f) t' ts
 <|> do compileCase <$ keyword "case" <*> parseETerm ns PrecLam e
                                 <* keyword "of" <*> localIndentation Ge (localAbsoluteIndentation $ some $ parseClause ns e)
 <|> do compileGuardTree' . Alts <$> parseSomeGuards ns (const True) e
 <|> do t <- parseTerm ns PrecEq e
        option t $ mkPi <$> (Visible <$ keyword "->" <|> Hidden <$ keyword "=>") <*> pure t <*> parseTTerm ns PrecLam e
parseTerm ns PrecEq e = parseTerm ns PrecAnn e >>= \t -> option t $ SCstr t <$ operator "~" <*> parseTTerm ns PrecAnn e
parseTerm ns PrecAnn e = parseTerm ns PrecOp e >>= \t -> option t $ SAnn t <$> parseType ns Nothing e
parseTerm ns PrecOp e = calculatePrecs e <$> p' where
    p' = (\(t, xs) -> (mkNat ns 0, ("-!", t): xs)) <$ operator "-" <*> p_
     <|> p_
    p_ = (,) <$> parseTerm ns PrecApp e <*> (option [] $ operator' >>= p)
    p op = do (exp, op') <- try ((,) <$> parseTerm ns PrecApp e <*> operator')
              ((op, exp):) <$> p op'
       <|> pure . (,) op <$> parseTerm ns PrecLam e
parseTerm ns PrecApp e = foldl sapp <$> parseTerm ns PrecAtom e <*> many
            (   (,) Visible <$> parseTerm ns PrecAtom e
            <|> (,) Hidden <$ operator "@" <*> parseTTerm ns PrecAtom e)
parseTerm ns PrecAtom e =
     sLit . LChar    <$> charLiteral
 <|> sLit . LString  <$> stringLiteral
 <|> sLit . LFloat   <$> try float
 <|> sLit . LInt . fromIntegral <$ char '#' <*> natural
 <|> mkNat ns <$> natural
 <|> Wildcard (Wildcard SType) <$ keyword "_"
 <|> sVar e <$> (lcIdents ns <|> try (varId ns))
 <|> mkDotDot <$> try (operator "[" *> parseTerm ns PrecLam e <* operator ".." ) <*> parseTerm ns PrecLam e <* operator "]"
 <|> mkList ns <$> brackets (commaSep $ parseTerm ns PrecLam e)
 <|> mkTuple ns <$> parens (commaSep $ parseTerm ns PrecLam e)
 <|> do keyword "let"
        dcls <- localIndentation Ge (localAbsoluteIndentation $ parseStmts ns e)
        mkLets' dcls <$ keyword "in" <*> parseTerm ns PrecLam e

sVar e x = maybe (SGlobal x) SVar $ elemIndex' x e

mkIf b t f = SGlobal "PrimIfThenElse" `SAppV` b `SAppV` t `SAppV` f

mkDotDot e f = SGlobal "fromTo" `SAppV` e `SAppV` f

--------------------------------------------------------------------------------

calculatePrecs :: [SName] -> (SExp, [(SName, SExp)]) -> SExp
calculatePrecs vs (e, []) = e
calculatePrecs vs (e, xs) = preExp $ \dcls -> calcPrec (\op x y -> op `SAppV` x `SAppV` y) (getFixity dcls . gf) e $ (sVar vs *** id) <$> xs
  where
    gf (SGlobal n) = n
    gf (SVar i) = vs !! i

getFixity :: GlobalEnv' -> SName -> Fixity
getFixity (fm, _) n = fromMaybe (Just FDLeft, 9) $ Map.lookup n fm

mkGlobalEnv' :: [Stmt] -> GlobalEnv'
mkGlobalEnv' ss =
    ( Map.fromList [(s, f) | PrecDef s f <- ss]
    , Map.fromList [(cn, (t, (id *** f) <$> cs)) | Data t _ _ cs <- ss, (cn, ct) <- cs]
    )
  where
    f ct = length $ filter ((==Visible) . fst) $ fst $ getParamsS ct

extractGlobalEnv' :: GlobalEnv -> GlobalEnv'
extractGlobalEnv' ge =
    ( Map.fromList
        [ (n, f) | (n, (d, _)) <- Map.toList ge, f <- maybeToList $ case d of
            Con (ConName _ f _ _) [] -> f
            TyCon (TyConName _ f _ _ _) [] -> f
            Label (FunName _ f _) _ _ -> f
            Fun (FunName _ f _) [] -> f
            _ -> Nothing
        ]
    , Map.fromList
        [ (n, case conTypeName cn of TyConName t _ _ cons _ -> (t, map f cons))
        | (n, (Con cn [], _)) <- Map.toList ge
        ]
    )
  where
    f (ConName n _ _ ct) = (n, length $ filter ((==Visible) . fst) $ fst $ getParams ct)

joinGlobalEnv' (fm, cm) (fm', cm') = (Map.union fm fm', Map.union cm cm')

calcPrec
  :: (Show e)
     => (e -> e -> e -> e)
     -> (e -> Fixity)
     -> e
     -> [(e, e)]
     -> e
calcPrec app getFixity e es = compileOps [((Nothing, -1), undefined, e)] es
  where
    compileOps [(_, _, e)] [] = e
    compileOps acc [] = compileOps (shrink acc) []
    compileOps acc@((p, g, e1): ee) es_@((op, e'): es) = case compareFixity (pr, op) (p, g) of
        Right GT -> compileOps ((pr, op, e'): acc) es
        Right LT -> compileOps (shrink acc) es_
        Left err -> error err
      where
        pr = getFixity op

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

mkLets' ss e = preExp $ \ge -> mkLets (removePreExps ge ss) (removePreExpsE ge e)

mkLets [] e = e
mkLets (Let n _ Nothing (downS 0 -> Just x): ds) e = SLet x (substSG n (SVar 0) $ upS $ mkLets ds e)
mkLets (ValueDef (ns, p) x: ds) e = patLam p (foldl (\e n -> substSG n (SVar 0) $ upS e) (mkLets ds e) ns) `SAppV` x
mkLets (x: ds) e = error $ "mkLets: " ++ show x
    -- (p = e; f) -->  (\p -> f) e

patLam = patLam_ (Visible, Wildcard SType)

patLam_ :: (Visibility, SExp) -> Pat -> SExp -> SExp
patLam_ (v, t) p e = SLam v t $ compileGuardTree' $ compilePatts [(p, 0)] Nothing e

mkTuple _ [x] = x
mkTuple (Just True, _) xs = foldl SAppV (SGlobal $ "'Tuple" ++ show (length xs)) xs
mkTuple (Just False, _) xs = foldl SAppV (SGlobal $ "Tuple" ++ show (length xs)) xs
mkTuple _ xs = error "mkTuple"

mkList (Just True, _) [x] = SGlobal "'List" `SAppV` x
mkList (Just False, _) xs = foldr (\x l -> SGlobal "Cons" `SAppV` x `SAppV` l) (SGlobal "Nil") xs
mkList _ xs = error "mkList"

parseSomeGuards ns f e = do
    pos <- sourceColumn <$> getPosition <* keyword "|"
    guard $ f pos
    (e', f) <-
         do (e', PCon p vs) <- try $ pattern' ns e <* keyword "<-"
            x <- parseETerm ns PrecEq e
            return (e', \gs' gs -> GuardNode x p vs (Alts gs'): gs)
     <|> do x <- parseETerm ns PrecEq e
            return (e, \gs' gs -> [GuardNode x "True" [] $ Alts gs', GuardNode x "False" [] $ Alts gs])
    f <$> (parseSomeGuards ns (> pos) e' <|> (:[]) . GuardLeaf <$ keyword "->" <*> parseETerm ns PrecLam e')
      <*> (parseSomeGuards ns (== pos) e <|> pure [])

{-
 case e of  p1 -> e1; p2 -> e2; v -> e3
    --> 
 | p1 <- e -> e1
 | p2 <- e -> e2
 | -> e3 [v := e]
-}
--compileCase :: SExp -> [(Pat, SExp)] -> GuardTree
compileCase x cs = preExp $ \info -> let
    f (PCon cn ps, rhs) = GuardNode x cn ps $ GuardLeaf rhs
    f (PVar, rhs) = GuardLeaf $ substSS 0 x $ removePreExpsE info rhs
    f x = error $ "compileCase: " ++ show x
  in compileGuardTree (removePreExpsGT info $ Alts $ map f cs) info

findAdt (_, cm) con = case Map.lookup con cm of
    Just i -> i
    _ -> error $ "findAdt:" ++ con

pattern SMotive = SLam Visible (Wildcard SType) (Wildcard SType)

compileCase' :: SName -> SExp -> [(Int, SExp)] -> SExp
compileCase' t x cs = foldl SAppV (SGlobal (caseName t) `SAppV` SMotive)
    [iterate (SLam Visible (Wildcard SType)) e !! vs | (vs, e) <- cs]
    `SAppV` x

mkNat (Just False, _) n = SGlobal "fromInt" `SAppV` sLit (LInt $ fromIntegral n)
mkNat _ n = toNat n

toNat 0 = SGlobal "Zero"
toNat n = SAppV (SGlobal "Succ") $ toNat (n-1)

--------------------------------------------------------------------------------

-- parallel patterns like  v@(f -> [])@(Just x)
newtype ParPat = ParPat [Pat]
  deriving Show

data Pat
    = PVar -- Int
    | PCon SName [ParPat]
    | ViewPat SExp ParPat
    | PatType ParPat SExp
  deriving Show

data GuardTree
    = GuardNode SExp Name [ParPat] GuardTree -- _ <- _
    | Alts [GuardTree]          --      _ | _
    | GuardLeaf SExp            --     _ -> e
  deriving Show

mapGT k i = \case
    GuardNode e c pps gt -> GuardNode (i k e) c ({-todo: up-} pps) $ mapGT (k + sum (map varPP pps)) i gt
    Alts gts -> Alts $ map (mapGT k i) gts
    GuardLeaf e -> GuardLeaf $ i k e

upGT k i = mapGT k $ \k -> upS__ k i

substGT i j = mapGT 0 $ \k -> rearrangeS $ \r -> if r == k + i then k + j else if r > k + i then r - 1 else r

mapPP f = \case
    ParPat ps -> ParPat (mapP f <$> ps)

mapP :: (SExp -> SExp) -> Pat -> Pat
mapP f = \case
    PVar -> PVar
    PCon n pp -> PCon n (mapPP f <$> pp)
    ViewPat e pp -> ViewPat (f e) (mapPP f pp)
    PatType pp e -> PatType (mapPP f pp) (f e)

upP i j = mapP (upS__ i j)

varPP = \case
    ParPat ps -> sum $ map varP ps

varP = \case
    PVar -> 1
    PCon n pp -> sum $ map varPP pp
    ViewPat e pp -> varPP pp
    PatType pp e -> varPP pp


alts (Alts xs) = concatMap alts xs
alts x = [x]

compileGuardTree' :: GuardTree -> SExp
compileGuardTree' t = preExp $ \x -> {-join traceShow $ -} compileGuardTree ({-join traceShow $ -} removePreExpsGT x t) x

compileGuardTree :: GuardTree -> GlobalEnv' -> SExp
compileGuardTree t adts = (\x -> traceD ("  !  :" ++ showSExp x) x) $ guardTreeToCases t
  where
    guardTreeToCases :: GuardTree -> SExp
    guardTreeToCases t = case alts t of
        [] -> SGlobal "undefined"
        GuardLeaf e: _ -> e
        ts@(GuardNode f s _ _: _) ->
          compileCase' t f $
            [ (n, guardTreeToCases $ Alts $ map (filterGuardTree (upS__ 0 n f) cn 0 n . upGT 0 n) ts)
            | (cn, n) <- cns
            ]
          where
            (t, cns) = findAdt adts s

    filterGuardTree :: SExp -> SName{-constr.-} -> Int -> Int{-number of constr. params-} -> GuardTree -> GuardTree
    filterGuardTree f s k ns = \case
        GuardLeaf e -> GuardLeaf e
        Alts ts -> Alts $ map (filterGuardTree f s k ns) ts
        GuardNode f' s' ps gs
            | f /= f'  -> GuardNode f' s' ps $ filterGuardTree (upS__ 0 su f) s (su + k) ns gs
            | s == s'  -> filterGuardTree f s k ns $ guardNodes (zip [k+ns-1, k+ns-1..] $ zip [0..] ps) gs
            | otherwise -> Alts []
          where
            su = sum $ map varPP ps

    guardNodes :: [(Int, (Int, ParPat))] -> GuardTree -> GuardTree
    guardNodes [] l = l
    guardNodes ((v, (i, ParPat ws)): vs) e = guardNode v i ws $ guardNodes vs e

    guardNode :: Int -> Int -> [Pat] -> GuardTree -> GuardTree
--    guardNode v i [] e = e
    guardNode v i (w: []) e = case w of
        PVar -> {-todo guardNode v (subst x v ws) $ -} substGT 0 v e
--        ViewPat f p -> guardNode (ViewApp f v) p $ guardNode v ws e
--        PCon s ps' -> GuardNode v s ps' $ guardNode v ws e

{-
substGT :: Int -> Int -> GuardTree -> GuardTree
substGT i x = \case
    GuardNode e n ps t -> GuardNode (substS i (Var x) e) n ps{-todo-} $ substGT i x
    Alts gs -> Alts $ substGT i x <$> gs
    GuardLeaf e -> substS i (Var x) e
-}

-- todo: clenup
compilePatts :: [(Pat, Int)] -> Maybe SExp -> SExp -> GuardTree
compilePatts ps gu = cp [] ps
  where
    cp ps' [] e = case gu of
        Nothing -> GuardLeaf $ preExp $ \x -> {-join traceShow $ -} rearrangeS (f $ reverse ps') $ removePreExpsE x e
    cp ps' ((p@PVar, i): xs) e = cp (p: ps') xs e
    cp ps' ((p@(PCon n ps), i): xs) e = GuardNode (SVar $ i + sum (map (fromMaybe 0 . ff) ps')) n ps $ cp (p: ps') xs e
    cp ps' ((p@(ViewPat f (ParPat [PCon n ps])), i): xs) e
        = GuardNode (SAppV f $ SVar $ i + sum (map (fromMaybe 0 . ff) ps')) n ps $ cp (p: ps') xs e

    m = length ps

    ff PVar = Nothing
    ff p = Just $ varP p

    f ps i
        | i >= s = i - s + m + sum vs'
        | i < s = case vs_ !! n of
        Nothing -> m + sum vs' - 1 - n
        Just _ -> m + sum vs' - 1 - (m + sum (take n vs') + j)
      where
        i' = s - 1 - i
        (n, j) = concat (zipWith (\k j -> zip (repeat j) [0..k-1]) vs [0..]) !! i'

        vs_ = map ff ps
        vs = map (fromMaybe 1) vs_
        vs' = map (fromMaybe 0) vs_
        s = sum vs


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
    ELet1 ts b          -> envDoc ts $ shLet_ m (sExpDoc b)
    ELet2 (x, _) ts     -> envDoc ts $ shLet_ (expDoc x) m
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
    SLet a b        -> shLet_ (sExpDoc a) (sExpDoc b)
    STyped (e, t)   -> expDoc e
    SVar i          -> expDoc (Var i)

shVar i = asks $ shAtom . lookupVarName where
    lookupVarName xs | i < length xs && i >= 0 = xs !! i
    lookupVarName _ = "V" ++ show i

shLet i a b = shVar i >>= \i' -> local (dropNth i) $ shLam' <$> (cpar . shLet' (fmap inBlue i') <$> a) <*> b
shLet_ a b = (gets head <* modify tail) >>= \i -> shLam' <$> (cpar . shLet' (shAtom i) <$> a) <*> local (i:) b
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
underlined = withEsc 47
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
error_ = error . correctEscs
trace_ = trace . correctEscs
traceD x = if debug then trace_ x else id

-------------------------------------------------------------------------------- main

type TraceLevel = Int
trace_level = 0 :: TraceLevel  -- 0: no trace
tr = False --trace_level >= 2
tr_light = trace_level >= 1

debug = False--True--tr
debug_light = True--False

infer :: GlobalEnv -> [Stmt] -> Either String GlobalEnv
infer env = fmap (forceGE . snd) . runExcept . flip runStateT (initEnv <> env) . mapM_ handleStmt

forceGE x = length (concatMap (uncurry (++) . (showExp *** showExp)) $ Map.elems x) `seq` x

fromRight ~(Right x) = x

main = do
    args <- getArgs
    let name = head $ args ++ ["tests/accept/DepPrelude"]
        f = name ++ ".lc"
        f' = name ++ ".lci"

    s <- readFile f
    let parseAndInfer = do
            p <- definitions <$> parse f s
            infer initEnv $ removePreExps (mkGlobalEnv' p) p
    case parseAndInfer of
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

