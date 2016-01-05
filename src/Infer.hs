{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
module Infer
    ( Binder (..), SName, Lit(..), Visibility(..), FunName(..), CaseFunName(..), ConName(..), TyConName(..), Export(..), ModuleR(..)
    , Exp (..), GlobalEnv
    , pattern Var, pattern Fun, pattern CaseFun, pattern TyCaseFun, pattern App, pattern FunN, pattern ConN, pattern Pi, pattern PMLabel, pattern FixLabel
    , downE
    , parse
    , mkGlobalEnv', joinGlobalEnv', extractGlobalEnv'
    , litType, infer
    , FreshVars
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
import Control.Arrow hiding ((<+>))
import Control.Applicative hiding (optional)
import Control.Exception hiding (try)

import Text.Parsec hiding (parse, label, Empty, State, (<|>), many, optional)
import qualified Text.Parsec.Token as Pa
import Text.Parsec.Pos
import Text.Parsec.Indentation hiding (Any)
import Text.Parsec.Indentation.Char
import Token

import Debug.Trace

import qualified Pretty as P
import Pretty hiding (Doc, braces)

-------------------------------------------------------------------------------- source data

type SName = String

data Stmt
    = Let SName MFixity (Maybe SExp) [Visibility]{-source arity-} SExp
    | Data SName [(Visibility, SExp)]{-parameters-} SExp{-type-} Bool{-True:add foralls-} [(SName, SExp)]{-constructor names and types-}
    | PrecDef SName Fixity
    | ValueDef ([SName], Pat) SExp
    | TypeFamily SName [(Visibility, SExp)]{-parameters-} SExp{-type-}

    -- eliminated during parsing
    | Class SName [SExp]{-parameters-} [(SName, SExp)]{-method names and types-}
    | Instance SName [Pat]{-parameter patterns-} [SExp]{-constraints-} [Stmt]{-method definitions-}
    | TypeAnn SName SExp            -- intermediate
    | FunAlt SName [((Visibility, SExp), Pat)] (Maybe SExp) SExp
    deriving (Show)

type Range = (SourcePos, SourcePos)

joinRange :: Range -> Range -> Range
joinRange (p1,_) (_,p4) = (p1, p4)

-- source info
data SI
    = NoSI  -- no source info
    | Range Range

instance Show SI where show _ = "SI"
instance Eq SI where _ == _ = True

showSI :: Env -> SI -> String
showSI _ NoSI = ""
showSI te (Range (start,end)) = showRange start end $ fst $ extractEnv te

showRange s e source = show str
    where
      startLine = sourceLine s - 1
      endline = sourceLine e - if sourceColumn e == 1 then 1 else 0
      len = endline - startLine
      str = vcat $ (text (show s){- <+> "-" <+> text (show e)-}):
                   map text (take len $ drop startLine $ lines source)
                ++ [text $ replicate (sourceColumn s - 1) ' ' ++ replicate (sourceColumn e - sourceColumn s) '^' | len == 1]

instance Monoid SI where
  mempty = NoSI
  mappend (Range r1) (Range r2) = Range (joinRange r1 r2)
  mappend r@(Range _) _ = r
  mappend _ r@(Range _) = r
  mappend _ _ = NoSI

pattern SGlobal n <- SGlobal_ _ n where SGlobal = SGlobal_ NoSI
pattern STyped e <- STyped_ _ e where STyped = STyped_ NoSI
pattern SVar i <- SVar_ _ i where SVar = SVar_ NoSI
pattern SApp v f x <- SApp_ _ v f x where SApp = SApp_ NoSI
pattern SBind a b c <- SBind_ _ a b c where SBind = SBind_ NoSI

data SExp
    = SGlobal_ SI SName
    | SBind_ SI Binder SExp SExp
    | SApp_ SI Visibility SExp SExp
    | SLet SExp SExp    -- let x = e in f   -->  SLet e f{-x is Var 0-}
    | SVar_ SI !Int
    | STyped_ SI ExpType
  deriving (Eq, Show)

sexpSI :: SExp -> SI
sexpSI = \case
  SGlobal_ r@(Range _) _ -> r
  SBind_ r@(Range _) _ _ _  -> r
  SBind _ e1 e2          -> sexpSI e1 <> sexpSI e2
  SApp_ si _ e1 e2       -> si <> sexpSI e1 <> sexpSI e2
  SLet e1 e2             -> sexpSI e1 <> sexpSI e2
  SVar_ r@(Range _) _    -> r
  STyped_ r@(Range _) _  -> r
  _                      -> mempty

type FixityMap = Map.Map SName Fixity
type ConsMap = Map.Map SName{-constructor name-}
                (Either ((SName{-type name-}, Int{-num of indices-}), [(SName, Int)]{-constructors with arities-})
                        (Int{-arity-}))
type GlobalEnv' = (FixityMap, ConsMap)

type Fixity = (FixityDef, Int)
type MFixity = Maybe Fixity
data FixityDef = Infix | InfixL | InfixR deriving (Show)

data Binder
    = BPi  Visibility
    | BLam Visibility
    | BMeta      -- a metavariable is like a floating hidden lambda
  deriving (Eq, Show)

data Visibility = Hidden | Visible
  deriving (Eq, Show)

sLit a = STyped (ELit a, litType a)
sLitSI si a = STyped_ si (ELit a, litType a)
pattern Primitive n mf t <- Let n mf (Just t) _ (SGlobal "undefined") where Primitive n mf t = Let n mf (Just t) (map fst $ fst $ getParamsS t) $ SGlobal "undefined"
pattern SType  = STyped (TType, TType)
pattern SPi  h a b = SBind (BPi  h) a b
pattern SLam h a b = SBind (BLam h) a b
pattern Wildcard t = SBind BMeta t (SVar 0)
pattern SPi_ si  h a b = SBind_ si (BPi  h) a b
pattern SLam_ si h a b = SBind_ si (BLam h) a b
pattern Wildcard_ si t = SBind BMeta t (SVar_ si 0)
pattern SAppH a b = SApp Hidden a b
pattern SAppV a b = SApp Visible a b
pattern SAppHSI si a b = SApp_ si Hidden a b
pattern SAppVSI si a b = SApp_ si Visible a b
pattern SLamV a = SLam Visible (Wildcard SType) a
pattern SLamV_ si a = SLam_ si Visible (Wildcard SType) a
pattern SAnn a t = STyped (Lam Visible TType (Lam Visible (Var 0) (Var 0)), TType :~> Var 0 :~> Var 1) `SAppV` t `SAppV` a  --  a :: t ~~> id t a
pattern TyType a = STyped (Lam Visible TType (Var 0), TType :~> TType) `SAppV` a
    -- same as  (a :: TType)     --  a :: TType   ~~>   (\(x :: TType) -> x) a
--pattern CheckSame' a b c = SGlobal "checkSame" `SAppV` STyped a `SAppV` STyped b `SAppV` c
pattern SCstr a b = SGlobal "'EqC" `SAppV` a `SAppV` b          --    a ~ b
pattern SParEval a b = SGlobal "parEval" `SAppV` Wildcard SType `SAppV` a `SAppV` b
pattern SLabelEnd a = SGlobal "labelend" `SAppV` a
pattern ST2 a b = SGlobal "'T2" `SAppV` a `SAppV` b

isPi (BPi _) = True
isPi _ = False

infixl 2 `SAppV`, `SAppH`, `App`, `app_`

-------------------------------------------------------------------------------- destination data

data Exp
    = Bind Binder Exp Exp   -- TODO: prohibit meta binder here;  BLam is not allowed
    | Lam Visibility Exp Exp
    | Con ConName [Exp]
    | TyCon TyConName [Exp]
    | ELit Lit
    | Assign !Int Exp Exp       -- De Bruijn index decreasing assign operator, only for metavariables (non-recursive) -- TODO: remove
    | Label LabelKind Exp{-function alternatives are obeyed during reduction-} Exp{-functions are treated like constants-}
            -- label is used also for getting fixity info
    | LabelEnd Exp
    | Neut Neutral
    | TType
  deriving (Show)

data Neutral
    = Fun_ FunName [Exp]
    | CaseFun_ CaseFunName [Exp]        -- todo: neutral at the end
    | TyCaseFun_ TyCaseFunName [Exp]    -- todo: neutral at the end
    | App_ Exp{-todo: Neutral-} Exp
    | Var_ !Int                 -- De Bruijn variable
  deriving (Show)

data LabelKind
    = LabelPM   -- pattern match label
    | LabelFix  -- fix unfold label
  deriving (Show)

pattern PMLabel x y  = Label LabelPM x y
pattern FixLabel x y = Label LabelFix x y

type Type = Exp

data ConName = ConName SName MFixity Int{-ordinal number, e.g. Zero:0, Succ:1-} Type
instance Show ConName where show (ConName n _ _ _) = n
instance Eq ConName where ConName n _ _ _ == ConName n' _ _ _ = n == n'

conTypeName :: ConName -> TyConName
conTypeName (ConName _ _ _ t) = case snd (getParams t) of
    TyCon n _ -> n
    _ -> error "impossible"

data TyConName = TyConName SName MFixity Int{-num of indices-} Type [ConName]{-constructors-} Type{-case type-}
instance Show TyConName where show (TyConName n _ _ _ _ _) = n
instance Eq TyConName where TyConName n _ _ _ _ _ == TyConName n' _ _ _ _ _ = n == n'

data FunName = FunName SName MFixity Type
instance Show FunName where show (FunName n _ _) = n
instance Eq FunName where FunName n _ _ == FunName n' _ _ = n == n'

data CaseFunName = CaseFunName SName Type Int{-num of parameters-}
instance Show CaseFunName where show (CaseFunName n _ _) = caseName n
instance Eq CaseFunName where CaseFunName n _ _ == CaseFunName n' _ _ = n == n'

data TyCaseFunName = TyCaseFunName SName Type
instance Show TyCaseFunName where show (TyCaseFunName n _) = matchName n
instance Eq TyCaseFunName where TyCaseFunName n _ == TyCaseFunName n' _ = n == n'

caseName (c:cs) = toLower c: cs ++ "Case"
matchName cs = "match" ++ cs
getMatchName ('m':'a':'t':'c':'h':cs) = Just cs
getMatchName _ = Nothing
pattern MatchName cs <- (getMatchName -> Just cs)

type ExpType = (Exp, Type)

pattern Fun a b = Neut (Fun_ a b)
pattern CaseFun a b = Neut (CaseFun_ a b)
pattern TyCaseFun a b = Neut (TyCaseFun_ a b)
pattern FunN a b <- Fun (FunName a _ _) b
pattern TFun a t b <- Fun (FunName a _ t) b where TFun a t b = Fun (FunName a Nothing t) b
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

pattern Cstr a b    = TFun "'EqC" (TType :~> TType :~> TType){-todo-} [a, b]
pattern ReflCstr x  = TFun "reflCstr" (TType :~> Cstr (Var 0) (Var 0)) [x]
pattern Coe a b w x = TFun "coe" (TType :~> TType :~> Cstr (Var 1) (Var 0) :~> Var 2 :~> Var 2) [a,b,w,x]
pattern ParEval t a b = TFun "parEval" (TType :~> Var 0 :~> Var 1 :~> Var 2) [t, a, b]
pattern Undef t     = TFun "undefined" (Pi Hidden TType (Var 0)) [t]

pattern ConN s a   <- Con (ConName s _ _ _) a
pattern TyConN s a <- TyCon (TyConName s _ _ _ _ _) a
pattern TCon s i t a <- Con (ConName s _ i t) a where TCon s i t a = Con (ConName s Nothing i t) a  -- todo: don't match on type
pattern TTyCon s t a <- TyCon (TyConName s _ _ t _ _) a where TTyCon s t a = TyCon (TyConName s Nothing (error "todo: inum") t (error "todo: tcn cons 2") $ error "TTyCon") a
pattern TTyCon0 s  <- TyCon (TyConName s _ _ TType _ _) [] where TTyCon0 s = TyCon (TyConName s Nothing (error "todo: inum2") TType (error "todo: tcn cons 3") $ error "TTyCon0") []
pattern Sigma a b  <- TyConN "Sigma" [a, Lam' b] where Sigma a b = TTyCon "Sigma" (error "sigmatype") [a, Lam Visible a{-todo: don't duplicate-} b]
pattern Unit        = TTyCon0 "'Unit"
pattern TT          = TCon "TT" 0 Unit []
pattern T2 a b      = TFun "'T2" (TType :~> TType :~> TType) [a, b]
pattern T2C a b     = TFun "t2C" (Unit :~> Unit :~> Unit) [a, b]
pattern Empty       = TTyCon0 "'Empty"
pattern TInt        = TTyCon0 "'Int"
pattern TNat        = TTyCon0 "'Nat"
pattern TBool       = TTyCon0 "'Bool"
pattern TFloat      = TTyCon0 "'Float"
pattern TString     = TTyCon0 "'String"
pattern TChar       = TTyCon0 "'Char"
pattern TOrdering   = TTyCon0 "'Ordering"
pattern Zero        = TCon "Zero" 0 TNat []
pattern Succ n      = TCon "Succ" 1 (TNat :~> TNat) [n]
--pattern TVec a b    = TTyCon "'Vec" (TNat :~> TType :~> TType) [a, b]
pattern TVec a b    = TTyCon "'VecS" (TType :~> TNat :~> TType) [b, a]
pattern TFrameBuffer a b = TTyCon "'FrameBuffer" (TNat :~> TType :~> TType) [a, b]
pattern Tuple2 a b c d = TCon "Tuple2" 0 Tuple2Type [a, b, c, d]
pattern Tuple0      = TCon "Tuple0" 0 Tuple0Type []
pattern CSplit a b c <- FunN "'Split" [a, b, c]

pattern Tuple0Type :: Exp
pattern Tuple0Type  <- _ where Tuple0Type   = TTyCon0 "'Tuple0"
pattern Tuple2Type :: Exp
pattern Tuple2Type  <- _ where Tuple2Type   = Pi Hidden TType $ Pi Hidden TType $ Var 1 :~> Var 1 :~> tTuple2 (Var 3) (Var 2)

tTuple2 a b = TTyCon "'Tuple2" (TType :~> TType :~> TType) [a, b]
tTuple3 a b c = TTyCon "'Tuple3" (TType :~> TType :~> TType :~> TType) [a, b, c]

pattern NatE :: Int -> Exp
pattern NatE n <- (fromNatE -> Just n) where NatE = toNatE

toNatE :: Int -> Exp
toNatE 0         = Zero
toNatE n | n > 0 = Succ (toNatE (n - 1))

fromNatE :: Exp -> Maybe Int
fromNatE Zero = Just 0
fromNatE (Succ n) = (1 +) <$> fromNatE n
fromNatE _ = Nothing

t2C TT TT = TT
t2C a b = T2C a b

t2 Unit a = a
t2 a Unit = a
t2 Empty _ = Empty
t2 _ Empty = Empty
t2 a b = T2 a b

pattern EInt a      = ELit (LInt a)
pattern EFloat a    = ELit (LFloat a)
pattern EString a   = ELit (LString a)

mkBool False = TCon "False" 0 TBool []
mkBool True  = TCon "True"  1 TBool []

pattern LCon <- (isCon -> True)
pattern CFun <- (isCaseFunName -> True)

pattern a :~> b = Bind (BPi Visible) a b

infixr 1 :~>

isCaseFunName (Fun f _) = True
isCaseFunName (CaseFun f _) = True
isCaseFunName (TyCaseFun f _) = True
isCaseFunName _ = False

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
    | EGlobal String{-full source of current module-} GlobalEnv [Stmt]
    | ELabelEnd Env

    | EBind1' Binder Env Exp            -- todo: move Exp zipper constructor to a separate ADT (if needed)
    | EPrim SName [Exp] Env [Exp]    -- todo: move Exp zipper constructor to a separate ADT (if needed)

    | EAssign Int Exp Env
    | CheckType Exp Env
    | CheckSame Exp Env
    | CheckAppType Visibility Exp Env SExp   --pattern CheckAppType h t te b = EApp1 h (CheckType t te) b
  deriving Show

type GlobalEnv = Map.Map SName (Exp, Type)

extractEnv :: Env -> (String, GlobalEnv)
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
    ELabelEnd x          -> Right x
    EGlobal s x _        -> Left (s, x)


initEnv :: GlobalEnv
initEnv = Map.fromList
    [ (,) "'Type" (TType, TType)     -- needed?
    ]

-- monad used during elaborating statments -- TODO: use zippers instead
type ElabStmtM m = ReaderT String{-full source-} (StateT GlobalEnv (ExceptT String m))

-------------------------------------------------------------------------------- low-level toolbox

label LabelFix x y = FixLabel x y
label LabelPM x (LabelEnd y) = y
label LabelPM x y = PMLabel x y

pattern UBind a b c = {-UnLabel-} (Bind a b c)      -- todo: review
pattern UApp a b = {-UnLabel-} (App a b)            -- todo: review
pattern UVar n = Var n

instance Eq Exp where
    PMLabel a _ == PMLabel a' _ = a == a'
    FixLabel a _ == FixLabel a' _ = a == a'
    FixLabel _ a == a' = a == a'
    a == FixLabel _ a' = a == a'
    Lam' a == Lam' a' = a == a'
    Bind a b c == Bind a' b' c' = (a, b, c) == (a', b', c')
    -- Assign a b c == Assign a' b' c' = (a, b, c) == (a', b', c')
    Fun a b == Fun a' b' = (a, b) == (a', b')
    CaseFun a b == CaseFun a' b' = (a, b) == (a', b')
    TyCaseFun a b == TyCaseFun a' b' = (a, b) == (a', b')
    Con a b == Con a' b' = (a, b) == (a', b')
    TyCon a b == TyCon a' b' = (a, b) == (a', b')
    TType == TType = True
    ELit l == ELit l' = l == l'
    App a b == App a' b' = (a, b) == (a', b')
    Var a == Var a' = a == a'
    LabelEnd a == LabelEnd a' = a == a'  -- ???
    _ == _ = False

assign :: (Int -> Exp -> Exp -> a) -> (Int -> Exp -> Exp -> a) -> Int -> Exp -> Exp -> a
assign _ clet i (Var j) b | i > j = clet j (Var (i-1)) $ substE "assign" j (Var (i-1)) $ up1E i b
assign clet _ i a b = clet i a b

handleLet i j f
    | i >  j = f (i-1) j
    | i <= j = f i (j+1)

foldS g f i = \case
    SApp_ _ _ a b -> foldS g f i a <> foldS g f i b
    SLet a b -> foldS g f i a <> foldS g f (i+1) b
    SBind _ a b -> foldS g f i a <> foldS g f (i+1) b
    STyped_ _ (e, t) -> f i e <> f i t
    SVar j -> f i (Var j)
    SGlobal_ si x -> g si i x

foldE f i = \case
    PMLabel x _ -> foldE f i x
    FixLabel _ x -> foldE f i x     -- ???
    Var k -> f i k
    Lam' b -> {-foldE f i t <>  todo: explain why this is not needed -} foldE f (i+1) b
    Bind _ a b -> foldE f i a <> foldE f (i+1) b
    Fun _ as -> foldMap (foldE f i) as
    CaseFun _ as -> foldMap (foldE f i) as
    TyCaseFun _ as -> foldMap (foldE f i) as
    Con _ as -> foldMap (foldE f i) as
    TyCon _ as -> foldMap (foldE f i) as
    TType -> mempty
    ELit _ -> mempty
    App a b -> foldE f i a <> foldE f i b
    Assign j x a -> handleLet i j $ \i' j' -> foldE f i' x <> foldE f i' a
    LabelEnd x -> foldE f i x

freeS = nub . foldS (\_ _ s -> [s]) mempty 0
freeE = foldE (\i k -> Set.fromList [k - i | k >= i]) 0

usedS = (getAny .) . foldS mempty ((Any .) . usedE)
usedE = (getAny .) . foldE ((Any .) . (==))

mapS = mapS_ (\si _ x -> SGlobal_ si x)
mapS_ gg ff = mapS__ gg ff $ \i j -> case ff i $ Var j of
            Var k -> SVar k
            -- x -> STyped x -- todo
mapS__ gg f1 f2 h e = g e where
    g i = \case
        SApp_ si v a b -> SApp_ si v (g i a) (g i b)
        SLet a b -> SLet (g i a) (g (h i) b)
        SBind k a b -> SBind k (g i a) (g (h i) b)
        STyped_ si (x, t) -> STyped_ si (f1 i x, f1 i t)
        SVar j -> f2 i j
        SGlobal_ si x -> gg si i x

rearrangeS :: (Int -> Int) -> SExp -> SExp
rearrangeS f = mapS__ (\si _ x -> SGlobal_ si x) (const id) (\i j -> SVar $ if j < i then j else i + f (j - i)) (+1) 0

upS__ i n = mapS (\i -> upE i n) (+1) i
upS = upS__ 0 1

up1E i = \case
    Var k -> Var $ if k >= i then k+1 else k
    Lam h a b -> Lam h (up1E i a) (up1E (i+1) b)
    Bind h a b -> Bind h (up1E i a) (up1E (i+1) b)
    Fun s as  -> Fun s $ map (up1E i) as
    CaseFun s as  -> CaseFun s $ map (up1E i) as
    TyCaseFun s as -> TyCaseFun s $ map (up1E i) as
    Con s as  -> Con s $ map (up1E i) as
    TyCon s as -> TyCon s $ map (up1E i) as
    TType -> TType
    ELit l -> ELit l
    App a b -> App (up1E i a) (up1E i b)
    Assign j a b -> handleLet i j $ \i' j' -> assign Assign Assign j' (up1E i' a) (up1E i' b)
    Label lk x y -> Label lk (up1E i x) $ up1E i y
    LabelEnd x -> LabelEnd $ up1E i x

upE i n e = iterateN n (up1E i) e

substSS :: Int -> SExp -> SExp -> SExp
substSS k x = mapS__ (\si _ x -> SGlobal_ si x) (error "substSS") (\(i, x) j -> case compare j i of
            EQ -> x
            GT -> SVar $ j - 1
            LT -> SVar j
            ) ((+1) *** upS) (k, x)
substS j x = mapS (uncurry $ substE "substS") ((+1) *** up1E 0) (j, x)
substSG j x = mapS_ (\si x i -> if i == j then x else SGlobal_ si i) (const id) upS x
substSG0 n e = substSG n (SVar 0) $ upS e

substE err = substE_ (error $ "substE: todo: environment required in " ++ err)  -- todo: remove

substE_ :: Env -> Int -> Exp -> Exp -> Exp
substE_ te i x = \case
    Label lk z v -> label lk (substE "slab" i x z) $ substE_ te{-todo: label env?-} i x v
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
    TyCaseFun s as -> eval te $ TyCaseFun s [substE_ te{-todo: precise env?-} i x a | (xs, a, ys) <- holes as]
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
    LabelEnd a -> LabelEnd $ substE_ te i x a

downS t x | usedS t x = Nothing
          | otherwise = Just $ substS t (error "impossible: downS") x
downE t x | usedE t x = Nothing
          | otherwise = Just $ substE_ (error "impossible") t (error "impossible: downE") x

varType :: String -> Int -> Env -> (Binder, Exp)
varType err n_ env = f n_ env where
    f n (EAssign i x es) = id *** substE "varType" i x $ f (if n < i then n else n+1) es
    f n (EBind2 b t es)  = if n == 0 then (b, up1E 0 t) else id *** up1E 0 $ f (n-1) es
    f n (ELet2 (x, t) es) = if n == 0 then (BLam Visible{-??-}, up1E 0 t) else id *** up1E 0 $ f (n-1) es
    f n e = either (error $ "varType: " ++ err ++ "\n" ++ show n_ ++ "\n" ++ showEnv env) (f n) $ parent e

-------------------------------------------------------------------------------- reduction

app_ :: Exp -> Exp -> Exp
app_ (Lam' x) a = substE "app" 0 a x
app_ (Con s xs) a = Con s (xs ++ [a])
app_ (TyCon s xs) a = TyCon s (xs ++ [a])
app_ (Label lk x e) a = label lk (app_ x a) $ app_ e a
app_ (LabelEnd x) a = LabelEnd (app_ x a)   -- ???
app_ f a = App f a

eval te = \case
    App a b -> app_ a b
    Cstr a b -> cstr a b
    ReflCstr a -> reflCstr te a
    Coe a b TT d -> d

    CaseFun (CaseFunName _ t pars) (drop (pars + 1) -> ps@(last -> Con (ConName _ _ i _) (drop pars -> vs))) | i /= (-1) -> foldl app_ (ps !! i) vs
    TyCaseFun (TyCaseFunName n ty) [_, t, TyCon (TyConName n' _ _ _ _ _) vs, f] | n == n' -> foldl app_ t vs
    TyCaseFun (TyCaseFunName n ty) [_, t, LCon, f] -> f
    T2 a b -> t2 a b
    T2C a b -> t2C a b
    ParEval t a b -> parEval a b
      where
        parEval (LabelEnd x) _ = LabelEnd x
        parEval _ (LabelEnd x) = LabelEnd x
        parEval a b = ParEval t a b

    FunN "primAddInt" [EInt i, EInt j] -> EInt (i + j)
    FunN "primSubInt" [EInt i, EInt j] -> EInt (i - j)
    FunN "primModInt" [EInt i, EInt j] -> EInt (i `mod` j)
    FunN "primSqrtFloat" [EFloat i] -> EFloat $ sqrt i
    FunN "primRound" [EFloat i] -> EInt $ round i
    FunN "primIntToFloat" [EInt i] -> EFloat $ fromIntegral i
    FunN "primCompareInt" [EInt x, EInt y] -> mkOrdering $ x `compare` y
    FunN "primCompareFloat" [EFloat x, EFloat y] -> mkOrdering $ x `compare` y
    FunN "primCompareString" [EString x, EString y] -> mkOrdering $ x `compare` y

    FunN "PrimGreaterThan" [_, _, _, _, _, _, _, EFloat x, EFloat y] -> mkBool $ x > y
    FunN "PrimSubS" [_, _, _, _, EFloat x, EFloat y] -> EFloat (x - y)
    FunN "PrimSubS" [_, _, _, _, EInt x, EInt y] -> EInt (x - y)
    FunN "PrimAddS" [_, _, _, _, EFloat x, EFloat y] -> EFloat (x + y)
    FunN "PrimMulS" [_, _, _, _, EFloat x, EFloat y] -> EFloat (x * y)

    FunN "unsafeCoerce" [_, _, x@LCon] -> x

-- todo: elim

    Fun n@(FunName "natElim" _ _) [a, z, s, Succ x] -> let      -- todo: replace let with better abstraction
                sx = s `app_` x
            in sx `app_` eval (EApp2 Visible sx te) (Fun n [a, z, s, x])
    FunN "natElim" [_, z, s, Zero] -> z
    Fun na@(FunName "finElim" _ _) [m, z, s, n, ConN "FSucc" [i, x]] -> let six = s `app_` i `app_` x-- todo: replace let with better abstraction
        in six `app_` eval (EApp2 Visible six te) (Fun na [m, z, s, i, x])
    FunN "finElim" [m, z, s, n, ConN "FZero" [i]] -> z `app_` i

    FunN "'TFFrameBuffer" [TyConN "'Image" [n, t]] -> TFrameBuffer n t
    FunN "'TFFrameBuffer" [TyConN "'Tuple2" [TyConN "'Image" [i@(NatE n), t], TyConN "'Image" [NatE n', t']]]
        | n == n' -> TFrameBuffer i $ tTuple2 t t'      -- todo
    FunN "'TFFrameBuffer" [TyConN "'Tuple3" [TyConN "'Image" [i@(NatE n), t], TyConN "'Image" [NatE n', t'], TyConN "'Image" [NatE n'', t'']]]
        | n == n' && n == n'' -> TFrameBuffer i $ tTuple3 t t' t''      -- todo

    x -> x

mkOrdering = \case
    LT -> TCon "LT" 0 TOrdering []
    EQ -> TCon "EQ" 1 TOrdering []
    GT -> TCon "GT" 2 TOrdering []

pattern NoTup <- (noTup -> True)

noTup (TyConN s _) = take 6 s /= "'Tuple" -- todo
noTup _ = False

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
    cstr_ ns (FixLabel _ a) a' = cstr_ ns a a'
    cstr_ ns a (FixLabel _ a') = cstr_ ns a a'
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
    cstr_ ns (UL (FunN "'VecScalar" [a, b])) (TVec a' b') = t2 (cstr__ ns a a') (cstr__ ns b b')
    cstr_ ns (UL (FunN "'VecScalar" [a, b])) (UL (FunN "'VecScalar" [a', b'])) = t2 (cstr__ ns a a') (cstr__ ns b b')
    cstr_ ns (UL (FunN "'VecScalar" [a, b])) t@(TTyCon0 n) | isElemTy n = t2 (cstr__ ns a (NatE 1)) (cstr__ ns b t)
    cstr_ ns t@(TTyCon0 n) (UL (FunN "'VecScalar" [a, b])) | isElemTy n = t2 (cstr__ ns a (NatE 1)) (cstr__ ns b t)
    cstr_ ns@[] (UL (FunN "'TFMat" [x, y])) (TyConN "'Mat" [i, j, a]) = t2 (cstr__ ns x (TVec i a)) (cstr__ ns y (TVec j a))
    cstr_ ns@[] (TyConN "'Tuple2" [x, y]) (UL (FunN "'JoinTupleType" [x'@NoTup, y'])) = t2 (cstr__ ns x x') (cstr__ ns y y')
    cstr_ ns@[] (TyConN "'Color" [x]) (UL (FunN "'ColorRepr" [x'])) = cstr__ ns x x'
    cstr_ ns (TyConN "'FrameBuffer" [a, b]) (UL (FunN "'TFFrameBuffer" [TyConN "'Image" [a', b']])) = T2 (cstr__ ns a a') (cstr__ ns b b')
    cstr_ [] a@App{} a'@App{} = Cstr a a'
    cstr_ [] a@CFun a'@CFun = Cstr a a'
    cstr_ [] a@LCon a'@CFun = Cstr a a'
    cstr_ [] a@LCon a'@App{} = Cstr a a'
    cstr_ [] a@CFun a'@LCon = Cstr a a'
    cstr_ [] a@App{} a'@LCon = Cstr a a'
    cstr_ [] a@PMLabel{} a' = Cstr a a'
    cstr_ [] a a'@PMLabel{} = Cstr a a'
    cstr_ [] a a' | isVar a || isVar a' = Cstr a a'
    cstr_ ns a a' = trace_ ("!----------------------------! type error:\n" ++ show ns ++ "\nfst:\n" ++ showExp a ++ "\nsnd:\n" ++ showExp a' ++ "\n" ++ show a) Empty

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

    isElemTy n = n `elem` ["'Bool", "'Float", "'Int"]

pattern UL a <- (unlabel -> a)

unlabel (PMLabel a _) = unlabel a
unlabel (FixLabel _ a) = unlabel a
unlabel a = a

cstr' h x y e = EApp2 h (eval (error "cstr'") $ Coe (up1E 0 x) (up1E 0 y) (Var 0) (up1E 0 e)) . EBind2 BMeta (cstr x y)

-------------------------------------------------------------------------------- simple typing

litType = \case
    LInt _    -> TInt
    LFloat _  -> TFloat
    LString _ -> TString
    LChar _   -> TChar

expType_ te = \case
    Lam h t x -> Pi h t $ expType_ (EBind2 (BLam h) t te) x
    App f x -> app (expType_ te{-todo: precise env-} f) x
    Var i -> snd $ varType "C" i te
    Pi{} -> TType
    Label _ x _ -> expType_ te x
    TFun _ t ts -> foldl app t ts
    CaseFun (CaseFunName _ t _) ts   -> foldl app t ts
    TyCaseFun (TyCaseFunName _ t) ts -> foldl app t ts
    TCon _ _ t ts -> foldl app t ts
    TTyCon _ t ts -> foldl app t ts
    TType -> TType
    ELit l -> litType l
    Meta{} -> error "meta type"
    Assign{} -> error "let type"
    LabelEnd x -> expType_ te x
  where
    app (Pi _ a b) x = substE "expType_" 0 x b
    app t x = error $ "app: " ++ show t

-------------------------------------------------------------------------------- inference

type TCM m = ExceptT String m

runTCM = either error id . runExcept

-- todo: do only if NoTypeNamespace extension is not on
lookupName s@('\'':s') m = maybe (Map.lookup s' m) Just $ Map.lookup s m
lookupName s m = Map.lookup s m
elemIndex' s@('\'':s') m = maybe (elemIndex s' m) Just $ elemIndex s m
elemIndex' s m = elemIndex s m
notElem' s@('\'':s') m = notElem s m && notElem s' m
notElem' s m = notElem s m

getDef te si s = maybe (throwError $ "can't find: " ++ s ++ " in " ++ showSI te si {- ++ "\nitems:\n" ++ intercalate ", " (take' "..." 10 $ Map.keys $ snd $ extractEnv te)-}) return (lookupName s $ snd $ extractEnv te)

take' e n xs = case splitAt n xs of
    (as, []) -> as
    (as, _) -> as ++ [e]

both f = f *** f

inferN :: forall m . Monad m => TraceLevel -> Env -> SExp -> TCM m ExpType
inferN tracelevel = infer  where

    infer :: Env -> SExp -> TCM m ExpType
    infer te exp = (if tracelevel >= 1 then trace_ ("infer: " ++ showEnvSExp te exp) else id) $ (if debug then fmap (recheck' "infer" te *** id) else id) $ case exp of
        SLabelEnd x -> infer (ELabelEnd te) x
        SVar i      -> focus te (Var i)
        STyped_ si et -> focus_ te et
        SGlobal_ si s -> focus_ te =<< getDef te si s
        SApp_ si h a b -> infer (EApp1 h te b) a
        SLet a b    -> infer (ELet1 te b{-in-}) a{-let-} -- infer te SLamV b `SAppV` a)
        SBind h a b -> infer ((if h /= BMeta then CheckType TType else id) $ EBind1 h te $ (if isPi h then TyType else id) b) a

    checkN :: Env -> SExp -> Exp -> TCM m ExpType
    checkN te x t = (if tracelevel >= 1 then trace_ $ "check: " ++ showEnvSExpType te x t else id) $ checkN_ te x t

    checkN_ te e t
            -- temporal hack
        | x@(SGlobal (MatchName n)) `SAppV` SLamV (Wildcard _) `SAppV` a `SAppV` SVar v `SAppV` b <- e
            = infer te $ x `SAppV` (STyped (Lam Visible TType $ substE "checkN" (v+1) (Var 0) $ up1E 0 t, TType :~> TType)) `SAppV` a `SAppV` SVar v `SAppV` b
            -- temporal hack
        | x@(SGlobal "'NatCase") `SAppV` SLamV (Wildcard _) `SAppV` a `SAppV` b `SAppV` SVar v <- e
            = infer te $ x `SAppV` (STyped (Lam Visible TNat $ substE "checkN" (v+1) (Var 0) $ up1E 0 t, TNat :~> TType)) `SAppV` a `SAppV` b `SAppV` SVar v
{-
            -- temporal hack
        | x@(SGlobal "'VecSCase") `SAppV` SLamV (SLamV (Wildcard _)) `SAppV` a `SAppV` b `SAppV` c `SAppV` SVar v <- e
            = infer te $ x `SAppV` (SLamV (SLamV (STyped (substE "checkN" (v+1) (Var 0) $ upE 0 2 t, TType)))) `SAppV` a `SAppV` b `SAppV` c `SAppV` SVar v
-}
            -- temporal hack
        | SGlobal "undefined" <- e = focus te $ Undef t
        | SLabelEnd x <- e = checkN (ELabelEnd te) x t
        | SApp_ si h a b <- e = infer (CheckAppType h t te b) a
        | SLam h a b <- e, Pi h' x y <- t, h == h'  = if checkSame te a x then checkN (EBind2 (BLam h) x te) b y else error "checkN"
        | Pi Hidden a b <- t, notHiddenLam e = checkN (EBind2 (BLam Hidden) a te) (upS e) b
        | otherwise = infer (CheckType t te) e
      where
        -- todo
        notHiddenLam = \case
            SLam Visible _ _ -> True
            SGlobal s | Lam Hidden _ _ <- fst $ fromMaybe (error $ "infer: can't find: " ++ s) $ lookupName s $ snd $ extractEnv te -> False
                            -- todo: use type instead of expr.
                      | otherwise -> True
            _ -> False

    -- todo
    checkSame te (Wildcard _) a = True
    checkSame te (SGlobal "'Type") TType = True
    checkSame te (STyped_ _ (TType, TType)) TType = True
    checkSame te (SBind BMeta SType (STyped_ _ (Var 0, _))) a = True
    checkSame te a b = error $ "checkSame: " ++ show (a, b)

    hArgs (Pi Hidden _ b) = 1 + hArgs b
    hArgs _ = 0

    focus env e = focus_ env (e, expType_ env e)

    focus_ :: Env -> ExpType -> TCM m ExpType
    focus_ env (e, et) = (if tracelevel >= 1 then trace_ $ "focus: " ++ showEnvExp env e else id) $ (if debug then fmap (recheck' "focus" env *** id) else id) $ case env of
        ELabelEnd te -> focus_ te (LabelEnd e, et)
        CheckSame x te -> focus_ (EBind2 BMeta (cstr x e) te) (up1E 0 e, up1E 0 et)
        CheckAppType h t te b   -- App1 h (CheckType t te) b
            | Pi h' x (downE 0 -> Just y) <- et, h == h' -> case t of
                Pi Hidden t1 t2 | h == Visible -> focus_ (EApp1 h (CheckType t te) b) (e, et)  -- <<e>> b : {t1} -> {t2}
                _ -> focus_ (EBind2 BMeta (cstr t y) $ EApp1 h te b) (up1E 0 e, up1E 0 et)
            | otherwise -> focus_ (EApp1 h (CheckType t te) b) (e, et)
        EApp1 h te b
            | Pi h' x y <- et, h == h' -> checkN (EApp2 h e te) b x
            | Pi Hidden x y  <- et, h == Visible -> focus_ (EApp1 Hidden env $ Wildcard $ Wildcard SType) (e, et)  --  e b --> e _ b
--            | CheckType (Pi Hidden _ _) te' <- te -> error "ok"
--            | CheckAppType Hidden _ te' _ <- te -> error "ok"
            | otherwise -> infer (CheckType (Var 2) $ cstr' h (upE 0 2 et) (Pi Visible (Var 1) (Var 1)) (upE 0 2 e) $ EBind2 BMeta TType $ EBind2 BMeta TType te) (upS__ 0 3 b)
        ELet1 te b{-in-} -> replaceMetas "let" Lam e >>= \e' -> infer (ELet2 (addType_ te e'{-let-}) te) b{-in-}
        ELet2 (x{-let-}, xt) te -> focus_ te (substE "app2" 0 (x{-let-}) (  e{-in-}), et)
        CheckType t te
            | hArgs et > hArgs t
                            -> focus_ (EApp1 Hidden (CheckType t te) $ Wildcard $ Wildcard SType) (e, et)
            | hArgs et < hArgs t, Pi Hidden t1 t2 <- t
                            -> focus_ (CheckType t2 $ EBind2 (BLam Hidden) t1 te) (e, et)
            | otherwise     -> focus_ (EBind2 BMeta (cstr t et) te) (up1E 0 e, up1E 0 et)
        EApp2 h a te        -> focus te $ app_ a e        --  h??
        EBind1 h te b       -> infer (EBind2 h e te) b
        EBind2 BMeta tt te
            | Unit <- tt    -> refocus te $ both (substE_ te 0 TT) (e, et)
            | Empty <- tt   -> throwError "halt because of type error" -- todo: better error msg
            | T2 x y <- tt -> let
                    te' = EBind2 BMeta (up1E 0 y) $ EBind2 BMeta x te
                in focus_ te' $ both (substE_ te' 2 (t2C (Var 1) (Var 0)) . upE 0 2) (e, et)
            | Cstr a b <- tt, a == b  -> refocus te $ both (substE "inferN2" 0 TT) (e, et)
            | Cstr a b <- tt, Just r <- cst a b -> r
            | Cstr a b <- tt, Just r <- cst b a -> r
            | isCstr tt, EBind2 h x te' <- te, h /= BMeta{-todo: remove-}, Just x' <- downE 0 tt, x == x'
                            -> refocus te $ both (substE "inferN3" 1 (Var 0)) (e, et)
            | EBind2 h x te' <- te, h /= BMeta, Just b' <- downE 0 tt
                            -> refocus (EBind2 h (up1E 0 x) $ EBind2 BMeta b' te') $ both (substE "inferN3" 2 (Var 0) . up1E 0) (e, et)
            | ELet2 (x, xt) te' <- te, Just b' <- downE 0 tt
                            -> refocus (ELet2 (up1E 0 x, up1E 0 xt) $ EBind2 BMeta b' te') $ both (substE "inferN32" 2 (Var 0) . up1E 0) (e, et)
            | EBind1 h te' x  <- te -> refocus (EBind1 h (EBind2 BMeta tt te') $ upS__ 1 1 x) (e, et)
            | ELet1 te' x     <- te, {-usedE 0 e, -} floatLetMeta $ expType_ env $ replaceMetas' Lam $ Bind BMeta tt e --not (tt == TType) {-todo: tweak?-}
                                    -> refocus (ELet1 (EBind2 BMeta tt te') $ upS__ 1 1 x) (e, et)
            | CheckAppType h t te' x <- te -> refocus (CheckAppType h (up1E 0 t) (EBind2 BMeta tt te') $ upS x) (e, et)
            | EApp1 h te' x   <- te -> refocus (EApp1 h (EBind2 BMeta tt te') $ upS x) (e, et)
            | EApp2 h x te'   <- te -> refocus (EApp2 h (up1E 0 x) $ EBind2 BMeta tt te') (e, et)
            | CheckType t te' <- te -> refocus (CheckType (up1E 0 t) $ EBind2 BMeta tt te') (e, et)
            | ELabelEnd te'   <- te -> refocus (ELabelEnd $ EBind2 BMeta tt te') (e, et)
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
            ELabelEnd te'     -> refocus' (ELabelEnd $ EAssign i b te') (e, et)
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

isCstr (Cstr _ _) = True
isCstr (UL (FunN s _)) = s `elem` ["'Eq"]       -- todo: use Constraint type to decide this
isCstr (UL c) = {- trace_ (showExp c ++ show c) $ -} False

-------------------------------------------------------------------------------- debug support

type Message = String

recheck :: Message -> Env -> Exp -> Exp
recheck msg e = if debug_light then recheck' msg e else id

recheck' :: Message -> Env -> Exp -> Exp
recheck' msg' e x = e'
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
        Label lk z x -> Label lk (recheck_ msg te z) x
        ELit l -> ELit l
        TType -> TType
        Con s [] -> Con s []
        Con s as -> reApp $ recheck_ "prim" te $ foldl App (Con s []) as
        TyCon s [] -> TyCon s []
        TyCon s as -> reApp $ recheck_ "prim" te $ foldl App (TyCon s []) as
        CaseFun s [] -> CaseFun s []
        CaseFun s as -> reApp $ recheck_ "fun" te $ foldl App (CaseFun s []) as
        TyCaseFun s [] -> TyCaseFun s []
        TyCaseFun s as -> reApp $ recheck_ "tycfun" te $ foldl App (TyCaseFun s []) as
        Fun s [] -> Fun s []
        Fun s as -> reApp $ recheck_ "fun" te $ foldl App (Fun s []) as
        LabelEnd x -> LabelEnd $ recheck_ msg te x
      where
        reApp (App f x) = case reApp f of
            Fun s args -> Fun s $ args ++ [x]
            CaseFun s args -> CaseFun s $ args ++ [x]
            TyCaseFun s args -> TyCaseFun s $ args ++ [x]
            Con s args -> Con s $ args ++ [x]
            TyCon s args -> TyCon s $ args ++ [x]
        reApp x = x

        appf (a, Pi h x y) (b, x')
            | x == x' = app_ a b
            | otherwise = error_ $ "recheck " ++ msg' ++ "; " ++ msg ++ "\nexpected: " ++ showEnvExp te{-todo-} x ++ "\nfound: " ++ showEnvExp te{-todo-} x' ++ "\nin term: " ++ showEnvExp (EApp2 h a te) b ++ "\n" ++ showExp y
        appf (a, t) (b, x')
            = error_ $ "recheck " ++ msg' ++ "; " ++ msg ++ "\nnot a pi type: " ++ showEnvExp te{-todo-} t ++ "\n\n" ++ showEnvExp e x

        recheck'' msg te a = (b, expType_ te b) where b = recheck_ msg te a

        ch False te e = recheck_ "ch" te e
        ch True te e = case recheck'' "check" te e of
            (e', TType) -> e'
            _ -> error_ $ "recheck'':\n" ++ showEnvExp te e

-------------------------------------------------------------------------------- statements

addParamsS ps t = foldr (uncurry SPi) t ps
addParams ps t = foldr (uncurry Pi) t ps

addLams ps t = foldr (uncurry Lam) t ps

lamify t x = addLams (fst $ getParams t) $ x $ downTo 0 $ arity t

getParamsS (SPi h t x) = ((h, t):) *** id $ getParamsS x
getParamsS x = ([], x)

getApps = second reverse . run where
  run (SApp_ _ h a b) = second ((h, b):) $ run a
  run x = (x, [])

getApps' = second reverse . run where
  run (App a b) = second (b:) $ run a
  run x = (x, [])

arity :: Exp -> Int
arity = length . fst . getParams

getParams :: Exp -> ([(Visibility, Exp)], Exp)
getParams (Pi h a b) = ((h, a):) *** id $ getParams b
getParams x = ([], x)

getLams (Lam h a b) = ((h, a):) *** id $ getLams b
getLams x = ([], x)

apps a b = foldl SAppV{-SI todo-} (SGlobal_ NoSI{-todo-} a) b
apps' a b = foldl sapp{-SI todo-} (SGlobal_ NoSI{-todo-} a) b

replaceMetas err bind = \case
    Meta a t -> bind Hidden a <$> replaceMetas err bind t
    Assign i x t -> bind Hidden (cstr (Var i) $ upE i 1 x) . up1E 0 . upE i 1 <$> replaceMetas err bind t  -- todo: remove?
    t -> checkMetas err t

replaceMetas' bind = \case
    Meta a t -> bind Hidden a $ replaceMetas' bind t
    Assign i x t -> bind Hidden (cstr (Var i) $ upE i 1 x) . up1E 0 . upE i 1 $ replaceMetas' bind t
    t ->  t

-- todo: remove
checkMetas err = \case
    x@Meta{} -> throwError_ $ "checkMetas " ++ err ++ ": " ++ showExp x
    x@Assign{} -> throwError_ $ "checkMetas " ++ err ++ ": " ++ showExp x
    Lam h a b -> Lam h <$> f a <*> f b
    Bind (BLam _) _ _ -> error "impossible: chm"
    Bind h a b -> Bind h <$> f a <*> f b
    Label lk z v -> Label lk <$> f z <*> pure v
    App a b  -> App <$> f a <*> f b
    Fun s xs -> Fun s <$> mapM f xs
    CaseFun s xs -> CaseFun s <$> mapM f xs
    TyCaseFun s xs -> TyCaseFun s <$> mapM f xs
    Con s xs -> Con s <$> mapM f xs
    TyCon s xs -> TyCon s <$> mapM f xs
    x@TType  -> pure x
    x@ELit{} -> pure x
    x@Var{}  -> pure x
    LabelEnd x -> LabelEnd <$> f x
  where
    f = checkMetas err

getGEnv f = do
    src <- ask
    gets (\ge -> EGlobal src ge mempty) >>= f
inferTerm msg tr f t = getGEnv $ \env -> let env' = f env in smartTrace $ \tr -> 
    fmap (\t -> if tr_light then length (showExp $ fst t) `seq` t else t) $ fmap (addType . recheck msg env') $ replaceMetas "lam" Lam . fst =<< lift (lift $ inferN (if tr then trace_level else 0) env' t)
inferType tr t = getGEnv $ \env -> fmap (recheck "inferType" env) $ replaceMetas "pi" Pi . fst =<< lift (lift $ inferN (if tr then trace_level else 0) (CheckType TType env) t)

smartTrace :: MonadError String m => (Bool -> m a) -> m a
smartTrace f | trace_level >= 2 = f True
smartTrace f | trace_level == 0 = f False
smartTrace f = catchError (f False) $ \err ->
    trace_ (unlines
        [ "---------------------------------"
        , err
        , "try again with trace"
        , "---------------------------------"
        ]) $ f True

addToEnv :: Monad m => String -> (Exp, Exp) -> ElabStmtM m ()
addToEnv s (x, t) = do
--    maybe (pure ()) throwError_ $ ambiguityCheck s t
    (if tr_light then trace_ (s ++ "  ::  " ++ showExp t) else id) $ modify $ Map.alter (Just . maybe (x, t) (const $ error $ "already defined: " ++ s)) s

-- Ambiguous: (Int ~ F a) => Int
-- Not ambiguous: (Show a, a ~ F b) => b
ambiguityCheck :: String -> Exp -> Maybe String
ambiguityCheck s ty = case ambigVars ty of
    [] -> Nothing
    err -> Just $ s ++ " has ambiguous type:\n" ++ showExp ty ++ "\nproblematic vars:\n" ++ show err

ambigVars :: Exp -> [(Int, Exp)]
ambigVars ty = [(n, c) | (n, c) <- hid, not $ any (`Set.member` defined) $ Set.insert n $ freeE c]
  where
    defined = dependentVars hid $ freeE ty'

    i = length hid_
    hid = zipWith (\k t -> (k, upE 0 (k+1) t)) (reverse [0..i-1]) hid_
    (hid_, ty') = hiddenVars ty

floatLetMeta :: Exp -> Bool
floatLetMeta ty = (i-1) `Set.member` defined
  where
    defined = dependentVars hid $ Set.map (+i) $ freeE ty

    i = length hid_
    hid = zipWith (\k t -> (k, upE 0 (k+1) t)) (reverse [0..i-1]) hid_
    (hid_, ty') = hiddenVars ty

hiddenVars (Pi Hidden a b) = (a:) *** id $ hiddenVars b
hiddenVars t = ([], t)

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
        CSplit a b c -> freeVars a <-> (freeVars b <> freeVars c)
        _ -> mempty
      where
        a --> b = \s -> if Set.null $ a `Set.intersection` s then mempty else b
        a <-> b = (a --> b) <> (b --> a)

expType = expType_ (EGlobal (error "expType - no source") initEnv $ error "expType")
addType x = (x, expType x)
addType_ te x = (x, expType_ te x)

downTo n m = map Var [n+m-1, n+m-2..n]
downToS n m = map SVar [n+m-1, n+m-2..n]

defined' = Map.keys

addF exs = gets $ addForalls exs . defined'

fixType = Pi Hidden TType $ Pi Visible (Pi Visible (Var 0) (Var 1)) (Var 1) -- forall a . (a -> a) -> a

addLams' x [] _ e = Fun x $ reverse e
addLams' x (h: ar) (Pi h' d t) e | h == h' = Lam h d $ addLams' x ar t (Var 0: map (up1E 0) e)
addLams' x ar@(Visible: _) (Pi h@Hidden d t) e = Lam h d $ addLams' x ar t (Var 0: map (up1E 0) e)

handleStmt :: MonadFix m => Extensions -> Stmt -> ElabStmtM m ()
handleStmt exs = \case
  PrecDef{} -> return ()
    -- primitive
  Primitive n mf t_ -> do
        t <- inferType tr =<< ($ t_) <$> addF exs
        addToEnv n $ flip (,) t $ lamify t $ Fun (FunName n mf t)
    -- non-recursive let
  Let n mf mt ar (downS 0 -> Just t_) -> do
        af <- addF exs
        (x, t) <- inferTerm n tr id (maybe id (flip SAnn . af) mt t_)
        addToEnv n (label LabelPM (addLams' (FunName n mf t) ar t []) x, t)
    -- recursive let
  Let n mf mt ar t_ -> do
    af <- addF exs
    (x@(Lam Hidden _ e), _)
        <- inferTerm n tr (EBind2 BMeta fixType) (SAppV (SVar 0) $ SLamV $ maybe id (flip SAnn . af) mt t_)
    let
        par i (Hidden: ar) (Pi Hidden _ tt) (Lam Hidden k z) = Lam Hidden k $ par (i+1) ar tt z
        par i ar@(Visible: _) (Pi Hidden _ tt) (Lam Hidden k z) = Lam Hidden k $ par (i+1) ar tt z
        par i ar tt (Var i' `App` _ `App` f) | i == i' = x where
            x = label LabelPM (addLams' (FunName n mf t) ar tt $ reverse $ downTo 0 i) $ f `app_` x

        x' =  x `app_` (Lam Hidden TType $ Lam Visible (Pi Visible (Var 0) (Var 1)) $ TFun "f_i_x" fixType [Var 1, Var 0])
        t = expType x'
    addToEnv n (par 0 ar t e, traceD ("addToEnv: " ++ n ++ " = " ++ showExp x') t)
  TypeFamily s ps t -> handleStmt exs $ Primitive s Nothing $ addParamsS ps t
  Data s ps t_ addfa cs -> do
    af <- if addfa then gets $ addForalls exs . (s:) . defined' else return id
    vty <- inferType tr $ addParamsS ps t_
    let
        pnum' = length $ filter ((== Visible) . fst) ps
        inum = arity vty - length ps

        mkConstr j (cn, af -> ct)
            | c == SGlobal s && take pnum' xs == downToS (length . fst . getParamsS $ ct) pnum'
            = do
                cty <- removeHiddenUnit <$> inferType tr (addParamsS [(Hidden, x) | (Visible, x) <- ps] ct)
                let     pars = zipWith (\x -> id *** STyped . flip (,) TType . upE x (1+j)) [0..] $ drop (length ps) $ fst $ getParams cty
                        act = length . fst . getParams $ cty
                        acts = map fst . fst . getParams $ cty
                        conn = ConName cn Nothing j cty
                addToEnv cn (Con conn [], cty)
                return ( conn
                       , addParamsS pars
                       $ foldl SAppV (SVar $ j + length pars) $ drop pnum' xs ++ [apps' cn (zip acts $ downToS (j+1+length pars) (length ps) ++ downToS 0 (act- length ps))]
                       )
            | otherwise = throwError $ "illegal data definition (parameters are not uniform) " -- ++ show (c, cn, take pnum' xs, act)
            where
                (c, map snd -> xs) = getApps $ snd $ getParamsS ct

        motive = addParamsS (replicate inum (Visible, Wildcard SType)) $
           SPi Visible (apps' s $ zip (map fst ps) (downToS inum $ length ps) ++ zip (map fst $ fst $ getParamsS t_) (downToS 0 inum)) SType

    mdo
        let tcn = TyConName s Nothing inum vty (map fst cons) ct
        addToEnv s (TyCon tcn [], vty)
        cons <- zipWithM mkConstr [0..] cs
        ct <- inferType tr
            ( (\x -> traceD ("type of case-elim before elaboration: " ++ showSExp x) x) $ addParamsS
                ( [(Hidden, x) | (_, x) <- ps]
                ++ (Visible, motive)
                : map ((,) Visible . snd) cons
                ++ replicate inum (Hidden, Wildcard SType)
                ++ [(Visible, apps' s $ zip (map fst ps) (downToS (inum + length cs + 1) $ length ps) ++ zip (map fst $ fst $ getParamsS t_) (downToS 0 inum))]
                )
            $ foldl SAppV (SVar $ length cs + inum + 1) $ downToS 1 inum ++ [SVar 0]
            )
        addToEnv (caseName s) (lamify ct $ CaseFun (CaseFunName s ct $ length ps), ct)
        let ps' = fst $ getParams vty
            t =   (TType :~> TType)
              :~> addParams ps' (Var (length ps') `app_` TyCon tcn (downTo 0 $ length ps'))
              :~>  TType
              :~> Var 2 `app_` Var 0
              :~> Var 3 `app_` Var 1
        addToEnv (matchName s) (lamify t $ TyCaseFun (TyCaseFunName s t), t)

  stmt -> error $ "handleStmt: " ++ show stmt

removeHiddenUnit (Pi Hidden Unit (downE 0 -> Just t)) = removeHiddenUnit t
removeHiddenUnit (Pi h a b) = Pi h a $ removeHiddenUnit b
removeHiddenUnit t = t

-------------------------------------------------------------------------------- parser

addForalls :: Extensions -> [SName] -> SExp -> SExp
addForalls exs defined x = foldl f x [v | v@(vh:_) <- reverse $ freeS x, v `notElem'` defined, isLower vh || NoConstructorNamespace `elem` exs]
  where
    f e v = SPi Hidden (Wildcard SType) $ substSG0 v e

defined defs = ("'Type":) $ flip foldMap defs $ \case
    TypeAnn x _ -> [x]
    Let x _ _ _ _ -> [x]
    Data x _ _ _ cs -> x: map fst cs
    Class x _ cs  -> x: map fst cs
    TypeFamily x _ _ -> [x]

type InnerP = Reader GlobalEnv'

type P = ParsecT (IndentStream (CharIndentStream String)) SourcePos InnerP

lexer :: Pa.GenTokenParser (IndentStream (CharIndentStream String)) SourcePos InnerP
lexer = makeTokenParser lexeme $ makeIndentLanguageDef style
  where
    lexeme p
        = do{ x <- p; getPosition >>= setState; whiteSpace; return x  }

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
        , Pa.reservedNames  =
                [ "case", "class", "data",
                  "else", "forall", "if", "import", "infix", "in", "infixl", "infixr",
                  "instance", "let", "module", "of", "then", "qualified",
                  "where", "_"
                ]
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

data Level
  = TypeLevel
  | ExpLevel
  deriving (Eq, Show)

levelElim
  typeLevel
  expLevel = \case
    TypeLevel -> typeLevel
    ExpLevel -> expLevel

data Namespace
  = Namespace Level Bool{-True means case sensitive first letter parsing-}
  | NonTypeNamespace
  deriving (Show)

caseSensitiveNS :: Namespace -> Bool
caseSensitiveNS NonTypeNamespace = True
caseSensitiveNS (Namespace _ sensitive) = sensitive

namespaceLevel (Namespace l _) = Just l
namespaceLevel _               = Nothing

typeNS (Namespace _ p) = Namespace TypeLevel p
typeNS n = n

expNS (Namespace _ p) = Namespace ExpLevel p
expNS n = n

switchNS (Namespace l p) = Namespace (case l of ExpLevel -> TypeLevel; TypeLevel -> ExpLevel) p
switchNS n = n

tick TypeLevel ('\'':n) = n
tick TypeLevel n = '\'': n
tick _ n = n

tick' = tick . fromMaybe ExpLevel . namespaceLevel
 
ident = Pa.identifier lexer
tickIdent ns = tick' ns <$> ident

lcOps = Pa.operator lexer

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
    deriving (Enum, Eq, Ord, Show)

type Name = String
type DefinitionR = Stmt

data Export = ExportModule Name | ExportId Name
type Extensions = [Extension]

data ModuleR
  = Module
  { extensions    :: Extensions
  , moduleImports :: [Name]    -- TODO
  , moduleExports :: Maybe [Export]
  , definitions   :: GlobalEnv' -> Either String [DefinitionR]
  , sourceCode    :: String
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

optionTry p = optionMaybe (try p)

-------------------------------------------------------------------------------- identifiers

check msg p m = try' msg $ do
    x <- m
    if p x then return x else fail $ msg ++ " expected"

head' ('\'': c: _) = c
head' (c: _) = c

--upperCase, lowerCase, symbols, colonSymbols :: P String
upperCase NonTypeNamespace = mzero -- todo
upperCase ns = (if caseSensitiveNS ns then check "uppercase ident" (isUpper . head') else id) $ tickIdent ns
lowerCase ns = (if caseSensitiveNS ns then check "lowercase ident" (isLower . head') else id) ident <|> try (('_':) <$ char '_' <*> ident)
symbols   = check "symbols" ((/=':') . head) lcOps
colonSymbols = "Cons" <$ operator ":" <|> check "symbols" ((==':') . head) lcOps

--------------------------------------------------------------------------------

pattern ExpN' :: String -> P.Doc -> String
pattern ExpN' s p <- ((,) undefined -> (p, s)) where ExpN' s p = s
pattern ExpN s = s

var ns          = lowerCase ns
patVar ns       = lowerCase ns <|> "" <$ keyword "_"
qIdent ns       = {-qualified_ todo-} (var ns <|> upperCase ns)
conOperator     = colonSymbols
varId ns        = var ns <|> parens operator'
backquotedIdent = try' "backquoted" $ char '`' *> (ExpN <$> ((:) <$> satisfy isAlpha <*> many (satisfy isAlphaNum))) <* char '`' <* whiteSpace
operator'       = symbols
              <|> conOperator
              <|> backquotedIdent
moduleName      = {-qualified_ todo-} upperCase (Namespace ExpLevel True)

-------------------------------------------------------------------------------- fixity declarations

fixityDef :: P [DefinitionR]
fixityDef = do
  dir <-    Infix  <$ keyword "infix"
        <|> InfixL <$ keyword "infixl"
        <|> InfixR <$ keyword "infixr"
  localIndentation Gt $ do
    i <- fromIntegral <$> natural
    ns <- commaSep1 operator'
    return $ PrecDef <$> ns <*> pure (dir, i)

--------------------------------------------------------------------------------

export :: Namespace -> P Export
export ns =
        ExportModule <$ keyword "module" <*> moduleName
    <|> ExportId <$> varId ns

parseExtensions :: P [Extension]
parseExtensions
    = try (string "{-#") *> simpleSpace *> string "LANGUAGE" *> simpleSpace *> commaSep ext <* simpleSpace <* string "#-}" <* simpleSpace
  where
    extensions = [toEnum 0 .. ]
    extensionMap = Map.fromList $ map (show &&& return) extensions

    simpleSpace = skipMany (satisfy isSpace)
    ext = do
        s <- some $ satisfy isAlphaNum
        fromMaybe
          (fail $ "language extension expected instead of " ++ s)
          (Map.lookup s extensionMap)

importlist ns = parens (commaSep (varId ns <|> upperCase ns))

parse :: SourceName -> String -> Either String ModuleR
parse f str = x
  where
    x = (show +++ id) . flip runReader (error "globalenv used") . runParserT p (newPos "" 0 0) f . mkIndentStream 0 infIndentation True Ge . mkCharIndentStream $ str

    getModuleName (_,n,_,_,_) = n

    p = do
        getPosition >>= setState
        setPosition =<< flip setSourceName f <$> getPosition
        exts <- concat <$> many parseExtensions
        let ns = if NoTypeNamespace `elem` exts
                    then NonTypeNamespace
                    else Namespace ExpLevel (not $ NoConstructorNamespace `elem` exts)
        whiteSpace
        header <- optional $ do
            modn <- keyword "module" *> moduleName
            exps <- optional (parens $ commaSep $ export ns)
            keyword "where"
            return (modn, exps)
        let importDef =
              (,,,,) <$> (keyword "import" *> (optionTry $ keyword "qualified"))
                     <*> moduleName
                     <*> (optionTry $ keyword "hiding" *> importlist ns)
                     <*> (optionTry $ importlist ns)
                     <*> (optionTry $ keyword "as" *> moduleName)
        idefs <- many (getModuleName <$> importDef)
        st <- getParserState

        let defs ge = (show +++ id) . flip runReader ge . runParserT p (newPos "" 0 0) f . mkIndentStream 0 infIndentation True Ge . mkCharIndentStream $ ""
              where
                p = do
                    setParserState st
                    parseDefs SLabelEnd ns [] <* eof
        return $ Module
          { extensions = exts
          , moduleImports = if NoImplicitPrelude `elem` exts
                then idefs
                else ExpN "Prelude": idefs
          , moduleExports = join $ snd <$> header
          , definitions   = defs
          , sourceCode    = str
          }

parseType ns mb vs = maybe id option mb $ operator "::" *> parseTTerm ns PrecLam vs
typedId ns mb vs = (,) <$> patVar ns <*> localIndentation Gt {-TODO-} (parseType ns mb vs)
typedId' ns mb vs = (,) <$> commaSep1 (varId ns <|> patVar ns <|> upperCase ns) <*> localIndentation Gt {-TODO-} (parseType ns mb vs)

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
    localIndentation Gt $ do
        x <- operator "->" *> parseETerm ns PrecLam fe
        f <- parseWhereBlock ns fe
        return (p, f x)

patternAtom ns vs =
     (,) vs . flip ViewPat eqPP . SAppV (SGlobal "primCompareFloat") <$> sLitSI `withRange` (LFloat <$> try float)
 <|> (,) vs . mkNatPat ns <$> natural
 <|> (,) vs . flip PCon [] <$> upperCase ns
 <|> char '\'' *> patternAtom (switchNS ns) vs
 <|> (,) <$> ((:vs) <$> patVar ns) <*> (pure PVar)
 <|> (id *** mkListPat ns) <$> brackets (patlist ns vs <|> pure (vs, []))
 <|> (id *** mkTupPat ns) <$> parens (patlist ns vs)
 where
   mkNatPat (Namespace ExpLevel _) n = flip ViewPat eqPP . SAppV (SGlobal "primCompareInt") . sLit . LInt $ fromIntegral n
   mkNatPat _ n = toNatP n

eqPP = ParPat [PCon "EQ" []]
truePP = ParPat [PCon "True" []]

patlist ns vs = commaSepUnfold (\vs -> (\(vs, p) t -> (vs, patType p t)) <$> pattern' ns vs <*> parseType ns (Just $ Wildcard SType) vs) vs

mkListPat ns [p] | namespaceLevel ns == Just TypeLevel = PCon "'List" [ParPat [p]]
mkListPat ns (p: ps) = PCon "Cons" $ map (ParPat . (:[])) [p, mkListPat ns ps]
mkListPat _ [] = PCon "Nil" []

mkTupPat :: Namespace -> [Pat] -> Pat
mkTupPat _ [x] = x
mkTupPat ns ps = PCon (tick' ns $ "Tuple" ++ show (length ps)) (ParPat . (:[]) <$> ps)

pattern' ns vs =
     pCon <$> upperCase ns <*> patterns ns vs
 <|> pCon <$> try (char '\'' *> upperCase (switchNS ns)) <*> patterns ns vs
 <|> (patternAtom ns vs >>= \(vs, p) -> option (vs, p) ((id *** (\p' -> PCon "Cons" (ParPat . (:[]) <$> [p, p']))) <$ operator ":" <*> pattern' ns vs))

pCon i (vs, x) = (vs, PCon i x)

patterns ns vs =
     do patternAtom ns vs >>= \(vs, p) -> patterns ns vs >>= \(vs, ps) -> pure (vs, ParPat [p]: ps)
 <|> pure (vs, [])

patType p (Wildcard SType) = p
patType p t = PatType (ParPat [p]) t

commaSepUnfold1 :: (t -> P (t, a)) -> t -> P (t, [a])
commaSepUnfold1 p vs0 = do
  (vs1, x) <- p vs0
  (second (x:) <$ comma <*> commaSepUnfold1 p vs1) <|> pure (vs1, [x])

commaSepUnfold :: (t -> P (t, a)) -> t -> P (t, [a])
commaSepUnfold p vs = commaSepUnfold1 p vs <|> pure (vs, [])

telescope' ns vs = option (vs, []) $ do
    (vs', vt) <-
            operator "@" *> (f Hidden <$> patternAtom ns vs)
        <|> f Visible <$> patternAtom ns vs
    (id *** (vt:)) <$> telescope' ns vs'
  where
    f h (vs, PatType (ParPat [p]) t) = (vs, ((h, t), p))
    f h (vs, p) = (vs, ((h, Wildcard SType), p))

parseDefs lend ns e = (asks $ \ge -> compileFunAlts' lend ge . concat) <*> many (parseDef ns e)

compileFunAlts' lend ge ds = concatMap (compileFunAlts False lend lend ge ds) $ groupBy h ds where
    h (FunAlt n _ _ _) (FunAlt m _ _ _) = m == n
    h _ _ = False

compileFunAlts :: Bool -> (SExp -> SExp) -> (SExp -> SExp) -> GlobalEnv' -> [Stmt] -> [Stmt] -> [Stmt]
compileFunAlts par ulend lend ge ds = \case
    [Instance{}] -> []
    [Class n ps ms] -> compileFunAlts' SLabelEnd ge $
            [ FunAlt n (map noTA ps) Nothing $ foldr ST2 (SGlobal "'Unit") cstrs | Instance n' ps cstrs _ <- ds, n == n' ]
         ++ [ FunAlt n (map noTA $ replicate (length ps) PVar) Nothing $ SGlobal "'Empty" ]
         ++ concat
            [ TypeAnn m (addParamsS (map ((,) Hidden) ps) $ SPi Hidden (foldl SAppV (SGlobal n) $ downToS 0 $ length ps) $ upS t)
            : [ FunAlt m p Nothing $ {- SLam Hidden (Wildcard SType) $ upS $ -} substS 0 (Var ic) $ upS__ (ic+1) 1 e
              | Instance n' i cstrs alts <- ds, n' == n
              , Let m' ~Nothing ~Nothing ar e <- alts, m' == m
              , let p = zip ((,) Hidden <$> ps) i  -- ++ ((Hidden, Wildcard SType), PVar): []
              , let ic = sum $ map varP i
              ]
            | (m, t) <- ms
            , let ts = fst $ getParamsS $ upS t
            ]
    [TypeAnn n t] -> [Primitive n Nothing t | all (/= n) [n' | FunAlt n' _ _ _ <- ds]]
    tf@[TypeFamily n ps t] -> case [d | d@(FunAlt n' _ _ _) <- ds, n' == n] of
        [] -> tf    -- builtin type family
        alts -> compileFunAlts True id SLabelEnd ge [TypeAnn n $ addParamsS ps t] alts
    [p@PrecDef{}] -> [p]
    fs@((FunAlt n vs _ _): _)
      | any (== n) [n' | TypeFamily n' _ _ <- ds] -> []
      | otherwise ->
        [ Let n
            (listToMaybe [t | PrecDef n' t <- ds, n' == n])
            (listToMaybe [t | TypeAnn n' t <- ds, n' == n])
            (map (fst . fst) vs)
            (foldr (uncurry SLam) (compileGuardTrees par ulend lend ge
                [ compilePatts (zip (map snd vs) $ reverse [0..length vs - 1]) gs x
                | FunAlt _ vs gs x <- fs
                ]) (map fst vs))
        ]
    x -> x
  where
    noTA x = ((Visible, Wildcard SType), x)

compileGuardTrees False ulend lend ge alts = compileGuardTree ulend lend ge $ Alts alts
compileGuardTrees True ulend lend ge alts = foldr1 SParEval $ compileGuardTree ulend lend ge <$> alts

parseDef :: Namespace -> [String] -> P [Stmt]
parseDef ns e =
     do keyword "data"
        localIndentation Gt $ do
            x <- upperCase (typeNS ns)
            (nps, ts) <- telescope (typeNS ns) (Just SType) e
            t <- parseType (typeNS ns) (Just SType) nps
            let mkConTy mk (nps', ts') =
                    ( if mk then Just $ diffDBNames nps' nps else Nothing
                    , foldr (uncurry SPi) (foldl SAppV (SGlobal_ NoSI{-todo-} x) $ downToS (length ts') $ length ts) ts')
            (af, cs) <-
                 do (,) True <$ keyword "where" <*> localIndentation Ge (localAbsoluteIndentation $ many $
                        (id *** (,) Nothing) <$> typedId' ns Nothing nps)
             <|> do (,) False <$ operator "=" <*>
                      sepBy1 ((,) <$> (pure <$> upperCase ns)
                                  <*> (    braces (mkConTy True <$> (telescopeDataFields (typeNS ns) nps))
                                       <|> (mkConTy False <$> telescope (typeNS ns) Nothing nps)) )
                                      (operator "|")
             <|> pure (True, [])
            ge <- ask
            return $ mkData ge x ts t af $ concatMap (\(vs, t) -> (,) <$> vs <*> pure t) cs
 <|> do keyword "class"
        localIndentation Gt $ do
            x <- upperCase (typeNS ns)
            (nps, ts) <- telescope (typeNS ns) (Just SType) e
            cs <-
                 do keyword "where" *> localIndentation Ge (localAbsoluteIndentation $ many $ typedId' ns Nothing nps)
             <|> pure []
            return $ pure $ Class x (map snd ts) (concatMap (\(vs, t) -> (,) <$> vs <*> pure t) cs)
 <|> do keyword "instance"
        let ns' = typeNS ns
        localIndentation Gt $ do
            constraints <- option [] $ try $ getTTuple' <$> parseTerm ns' PrecEq e <* operator "=>"
            x <- upperCase ns'
            (nps, args) <- telescope' ns' e
            cs <- option [] $ keyword "where" *> localIndentation Ge (localAbsoluteIndentation $ some $
                    funAltDef (varId ns) ns nps)
             <|> pure []
            ge <- ask
            return $ pure $ Instance x ({-todo-}map snd args) (deBruinify (diffDBNames nps e ++ [x]) <$> constraints) $ compileFunAlts' id{-TODO-} ge cs
 <|> do try (keyword "type" >> keyword "family")
        let ns' = typeNS ns
        localIndentation Gt $ do
            x <- upperCase ns'
            (nps, ts) <- telescope ns' (Just SType) e
            t <- parseType ns' (Just SType) nps
            option {-open type family-}[TypeFamily x ts t] $ do
                cs <- keyword "where" *> localIndentation Ge (localAbsoluteIndentation $ many $
                    funAltDef (upperCase ns' >>= \x' -> guard (x == x') >> return x') ns' e)
                ge <- ask
                -- closed type family desugared here
                return $ compileFunAlts False id SLabelEnd ge [TypeAnn x $ addParamsS ts t] cs
 <|> do try (keyword "type" >> keyword "instance")
        let ns' = typeNS ns
        pure <$> localIndentation Gt (funAltDef (upperCase ns') ns' e)
 <|> do (vs, t) <- try $ typedId' ns Nothing []
        return $ TypeAnn <$> vs <*> pure t
 <|> fixityDef
 <|> pure <$> funAltDef (varId ns) ns e
 <|> pure . uncurry ValueDef <$> valueDef ns e
 where
   telescopeDataFields ns vs = option (vs, []) $ do
       (x, vt) <- do name <- var (expNS ns)
                     operator "::"
                     term <- parseTerm ns PrecLam vs
                     return (name, (Visible, term))
       (id *** (vt:)) <$> (comma *> telescopeDataFields ns (x: vs) <|> pure (vs, []))

funAltDef parseName ns e = do   -- todo: use ns to determine parseName
    (n, (fe, ts)) <-
        do try' "operator definition" $ do
            (e', a1) <- patternAtom ns ("": e)
            localIndentation Gt $ do
                n <- operator'
                (e'', a2) <- patternAtom ns $ init (diffDBNames e' e) ++ n: e
                lookAhead $ operator "=" <|> operator "|"
                return (n, (e'', (,) (Visible, Wildcard SType) <$> [a1, a2]))
      <|> do try $ do
                n <- parseName
                localIndentation Gt $ (,) n <$> telescope' ns (n: e) <* (lookAhead $ operator "=" <|> operator "|")
    localIndentation Gt $ do
        gu <- option Nothing $ do
            operator "|"
            Just <$> parseTerm ns PrecOp fe
        operator "="
        rhs <- parseTerm ns PrecLam []--fe
        f <- parseWhereBlock ns fe
        return $ FunAlt n ts gu $ deBruinify' fe {-hack-} $ f rhs

mkData ge x ts t af cs = [Data x ts t af $ (id *** snd) <$> cs] ++ concatMap mkProj cs
  where
    mkProj (cn, (Just fs, _)) = [ Let fn Nothing Nothing [Visible]
                                $ upS{-non-rec-} $ patLam NoSI SLabelEnd ge (PCon cn $ replicate (length fs) $ ParPat [PVar]) $ SVar i
                                | (i, fn) <- zip [0..] fs]
    mkProj _ = []

parseWhereBlock ns fe = option id $ do
    keyword "where"
    dcls <- localIndentation Ge (localAbsoluteIndentation $ parseDefs id ns fe)
    ge <- ask
    return $ mkLets ge dcls

type DBNames = [SName]  -- De Bruijn variable names

valueDef :: Namespace -> DBNames -> P ((DBNames, Pat), SExp)
valueDef ns e = do
    (e', p) <- try $ pattern' ns e <* operator "="
    localIndentation Gt $ do
        ex <- parseETerm ns PrecLam e
        return ((diffDBNames e' e, p), ex)

pattern TPVar t = ParPat [PatType (ParPat [PVar]) t]

sapp a (v, b) = SApp v a b

parseTTerm ns = parseTerm $ typeNS ns
parseETerm ns = parseTerm $ expNS ns

parseTerm :: Namespace -> Prec -> [String] -> P SExp
parseTerm ns PrecLam e =
     mkIf `withRange` ((,,) <$ keyword "if" <*> parseTerm ns PrecLam e <* keyword "then" <*> parseTerm ns PrecLam e <* keyword "else" <*> parseTerm ns PrecLam e)
 <|> do (tok, ns) <- (SPi . const Hidden <$ operator "." <|> SPi . const Visible <$ operator "->", typeNS ns) <$ keyword "forall"
        (fe, ts) <- telescope ns (Just $ Wildcard SType) e
        f <- tok
        t' <- parseTerm ns PrecLam fe
        return $ foldr (uncurry f) t' ts
 <|> do sPos <- position
        (tok, ns) <- (asks (\a r -> patLam_ r id a) <* operator "->", expNS ns) <$ operator "\\"
        (fe, ts) <- telescope' ns e
        f <- tok
        t' <- parseTerm ns PrecLam fe
        ePos <- positionBeforeSpace
        return $ foldr (uncurry (f $ Range (sPos,ePos))) t' ts
 <|> do (asks compileCase) <* keyword "case" <*> parseETerm ns PrecLam e
                                 <* keyword "of" <*> localIndentation Ge (localAbsoluteIndentation $ some $ parseClause ns e)
 <|> do (asks $ \ge -> compileGuardTree id id ge . Alts) <*> parseSomeGuards ns (const True) e
 <|> do t <- parseTerm ns PrecEq e
        option t $ mkPi <$> (Visible <$ operator "->" <|> Hidden <$ operator "=>") <*> pure t <*> parseTTerm ns PrecLam e
parseTerm ns PrecEq e = parseTerm ns PrecAnn e >>= \t -> option t $ SCstr t <$ operator "~" <*> parseTTerm ns PrecAnn e
parseTerm ns PrecAnn e = parseTerm ns PrecOp e >>= \t -> option t $ SAnn t <$> parseType ns Nothing e
parseTerm ns PrecOp e = (asks $ \dcls -> calculatePrecs dcls e) <*> p' where
    p' = ((\si (t, xs) -> (mkNat ns si 0, ("-!", t): xs)) `withRange` (operator "-" *> p_))
         <|> p_
    p_ = (,) <$> parseTerm ns PrecApp e <*> (option [] $ operator' >>= p)
    p op = do (exp, op') <- try ((,) <$> parseTerm ns PrecApp e <*> operator')
              ((op, exp):) <$> p op'
       <|> pure . (,) op <$> parseTerm ns PrecLam e
parseTerm ns PrecApp e = 
    try {- TODO: adjust try for better error messages e.g. don't use braces -}
      (foldl sapp <$> (sVar e `withRange` upperCase ns) <*> braces (commaSep $ lowerCase ns *> operator "=" *> ((,) Visible <$> parseTerm ns PrecLam e))) <|>
    (foldl sapp <$> parseTerm ns PrecSwiz e <*> many
            (   (,) Visible <$> parseTerm ns PrecSwiz e
            <|> (,) Hidden <$ operator "@" <*> parseTTerm ns PrecSwiz e))
parseTerm ns PrecSwiz e = do
    t <- parseTerm ns PrecProj e
    try (mkSwizzling t `withRange` (char '%' *> manyNM 1 4 (satisfy (`elem` ("xyzwrgba" :: [Char]))) <* whiteSpace)) <|> pure t
parseTerm ns PrecProj e = do
    t <- parseTerm ns PrecAtom e
    try (mkProjection t <$ char '.' <*> (sepBy1 (sLitSI `withRange` (LString <$> lowerCase ns)) (char '.'))) <|> pure t
parseTerm ns PrecAtom e =
     sLitSI `withRange` (LChar <$> try charLiteral)
 <|> sLitSI `withRange` (LString  <$> stringLiteral)
 <|> sLitSI `withRange` (LFloat   <$> try float)
 <|> sLitSI `withRange` (LInt . fromIntegral <$ char '#' <*> natural)
 <|> mkNat ns `withRange` natural
 <|> Wildcard (Wildcard SType) <$ keyword "_"
 <|> char '\'' *> parseTerm (switchNS ns) PrecAtom e
 <|> sVar e `withRange` (try (varId ns) <|> upperCase ns)
 <|> mkDotDot <$> try (operator "[" *> parseTerm ns PrecLam e <* operator ".." ) <*> parseTerm ns PrecLam e <* operator "]"
 <|> listCompr ns e
 <|> mkList ns `withRange` brackets (commaSep $ parseTerm ns PrecLam e)
 <|> mkTuple ns `withRange` parens (commaSep $ parseTerm ns PrecLam e)
 <|> mkRecord `withRange` braces (commaSep $ ((,) <$> lowerCase ns <* colon <*> parseTerm ns PrecLam e))
 <|> do keyword "let"
        dcls <- localIndentation Ge (localAbsoluteIndentation $ parseDefs id ns e)
        ge <- ask
        mkLets ge dcls <$ keyword "in" <*> parseTerm ns PrecLam e

mkSwizzling term si = swizzcall
  where
    sc c = SGlobal $ 'S':c:[]
    swizzcall [x] = (SAppVSI si (SGlobal "swizzscalar") term) `SAppV` (sc . synonym) x
    swizzcall xs  = (SAppVSI si (SGlobal "swizzvector") term) `SAppV` swizzparam xs
    swizzparam xs  = foldl (\exp s -> exp `SAppV` s) (vec xs) $ map (sc . synonym) xs
    vec xs = SGlobal $ case length xs of
        0 -> error "impossible: swizzling parsing returned empty pattern"
        1 -> error "impossible: swizzling went to vector for one scalar"
        n -> "V" ++ show n
    synonym 'r' = 'x'
    synonym 'g' = 'y'
    synonym 'b' = 'z'
    synonym 'a' = 'w'
    synonym c   = c

mkProjection term = foldl (\exp field -> SGlobal "project" `SAppV` field `SAppV` exp) term

-- Creates: RecordCons @[("x", _), ("y", _), ("z", _)] (1.0, (2.0, (3.0, ())))
mkRecord si xs = SAppVSI si (SGlobal "RecordCons" `SAppH` names) values
  where
    (names, values) = mkNames *** mkValues $ unzip xs

    mkNameTuple v = SGlobal "Tuple2" `SAppV` (sLit $ LString v) `SAppV` Wildcard SType
    mkNames = foldr (\n ns -> SGlobal "Cons" `SAppV` (mkNameTuple n) `SAppV` ns)
                    (SGlobal "Nil")

    mkValues = foldr (\x xs -> SGlobal "Tuple2" `SAppV` x `SAppV` xs)
                     (SGlobal "Tuple0")

mkTuple _ si [x] = x
mkTuple (Namespace level _) si xs = foldl SAppV (SGlobal_ si $ tuple ++ show (length xs)) xs
  where tuple = levelElim "'Tuple" "Tuple" level
mkTuple _ si xs = error "mkTuple"

mkList (Namespace TypeLevel _) si [x] = SAppVSI si (SGlobal "'List") x
mkList (Namespace ExpLevel  _) si xs = foldr (\x l -> SAppVSI si (SGlobal "Cons" `SAppV` x) l) (SGlobal "Nil") xs
mkList _ si xs = error "mkList"

mkNat (Namespace ExpLevel _) si n = SGlobal "fromInt" `SAppV` sLitSI si (LInt $ fromIntegral n)
mkNat _ _ n = toNat n

infix 9 `withRange`

withRange :: (SI -> a -> b) -> P a -> P b
withRange f p = (\p1 a p2 -> f (Range (p1,p2)) a) <$> position <*> p <*> positionBeforeSpace

sVar e si x = maybe (SGlobal_ si x) (SVar_ si) $ elemIndex' x e

mkIf si (b,t,f) = SGlobal_ si "primIfThenElse" `SAppV` b `SAppV` t `SAppV` f

mkDotDot e f = SGlobal "fromTo" `SAppV` e `SAppV` f

-- n, m >= 1, n < m
manyNM n m p = do
  xs <- many1 p
  let lxs = length xs
  unless (n <= lxs && lxs <= m) . fail $ unwords ["manyNM", show n, show m, "found", show lxs, "occurences."]
  return xs

-------------------------------------------------------------------------------- list comprehensions

generator, letdecl, boolExpression :: Namespace -> DBNames -> P (DBNames, SExp -> SExp)
generator ns dbs = do
    (dbs', pat) <- try $ pattern' ns dbs <* operator "<-"
    exp <- parseTerm ns PrecLam dbs
    ge <- ask
    return $ (,) dbs' $ \e -> application
        [ SGlobal "concatMap"
        , SLamV $ compileGuardTree id id ge $ Alts
            [ compilePatts [(pat, 0)] Nothing $ {-upS $ -} e
            , GuardLeaf $ SGlobal "Nil"
            ]
        , exp
        ]

letdecl ns dbs = ask >>= \ge -> keyword "let" *> ((\((dbs', p), e) -> (dbs, \exp -> mkLets ge [ValueDef (dbs', p) e] exp)) <$> valueDef ns dbs)

boolExpression ns dbs = do
    pred <- parseTerm ns PrecLam dbs
    return (dbs, \e -> application [SGlobal "primIfThenElse", pred, e, SGlobal "Nil"])

application = foldl1 SAppV

listCompr :: Namespace -> DBNames -> P SExp
listCompr ns dbs = (\e (dbs', fs) -> foldr ($) (deBruinify (diffDBNames dbs' dbs) e) fs)
 <$> try' "List comprehension" ((SGlobal "singleton" `SAppV`) <$ operator "[" <*> parseTerm ns PrecLam dbs <* operator "|")
 <*> commaSepUnfold (liftA2 (<|>) (generator ns) $ liftA2 (<|>) (letdecl ns) (boolExpression ns)) dbs <* operator "]"

-- todo: make it more efficient
diffDBNames xs ys = take (length xs - length ys) xs

deBruinify' xs e = foldl (\e (i, n) -> substSG n (SVar i) e) e $ zip [0..] xs

deBruinify :: DBNames -> SExp -> SExp
deBruinify [] e = e
deBruinify (n: ns) e = substSG0 n $ deBruinify ns e

--------------------------------------------------------------------------------

calculatePrecs :: GlobalEnv' -> [SName] -> (SExp, [(SName, SExp)]) -> SExp
calculatePrecs _ vs (e, []) = e
calculatePrecs dcls vs (e, xs) = calcPrec (\op x y -> op `SAppV` x `SAppV` y) (getFixity dcls . gf) e $ (sVar vs NoSI{-todo-} *** id) <$> xs
  where
    gf (SGlobal n) = n
    gf (SVar i) = vs !! i

getFixity :: GlobalEnv' -> SName -> Fixity
getFixity (fm, _) n = fromMaybe (InfixL, 9) $ Map.lookup n fm

mkGlobalEnv' :: [Stmt] -> GlobalEnv'
mkGlobalEnv' ss =
    ( Map.fromList [(s, f) | PrecDef s f <- ss]
    , Map.fromList $
        [(cn, Left ((t, pars ty), (id *** pars) <$> cs)) | Data t ps ty _ cs <- ss, (cn, ct) <- cs]
     ++ [(t, Right $ pars $ addParamsS ps ty) | Data t ps ty _ cs <- ss]
    )
  where
    pars ty = length $ filter ((== Visible) . fst) $ fst $ getParamsS ty -- todo

extractGlobalEnv' :: GlobalEnv -> GlobalEnv'
extractGlobalEnv' ge =
    ( Map.fromList
        [ (n, f) | (n, (d, _)) <- Map.toList ge, f <- maybeToList $ case d of
            Con (ConName _ f _ _) [] -> f
            TyCon (TyConName _ f _ _ _ _) [] -> f
            (snd . getLams -> UL (snd . getLams -> Fun (FunName _ f _) _)) -> f
            Fun (FunName _ f _) [] -> f
            _ -> Nothing
        ]
    , Map.fromList $
        [ (n, Left ((t, inum), map f cons))
        | (n, (Con cn [], _)) <- Map.toList ge, let TyConName t _ inum _ cons _ = conTypeName cn
        ] ++
        [ (n, Right $ pars t)
        | (n, (TyCon (TyConName _ f _ t _ _) [], _)) <- Map.toList ge
        ]
    )
  where
    f (ConName n _ _ ct) = (n, pars ct)
    pars = length . filter ((==Visible) . fst) . fst . getParams

joinGlobalEnv' (fm, cm) (fm', cm') = (Map.union fm fm', Map.union cm cm')

calcPrec
  :: (Show e)
     => (e -> e -> e -> e)
     -> (e -> Fixity)
     -> e
     -> [(e, e)]
     -> e
calcPrec app getFixity e es = compileOps [((Infix, -1), undefined, e)] es
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
            (InfixL, InfixL) -> Right LT
            (InfixR, InfixR) -> Right GT
            _ -> Left $ "fixity error:" ++ show (op, op')

mkPi Hidden (getTTuple' -> xs) b = foldr (sNonDepPi Hidden) b xs
mkPi h a b = sNonDepPi h a b

sNonDepPi h a b = SPi h a $ upS b

getTTuple' (getTTuple -> Just (n, xs)) | n == length xs = xs
getTTuple' x = [x]

getTTuple (SAppV (getTTuple -> Just (n, xs)) z) = Just (n, xs ++ [z]{-todo: eff-})
getTTuple (SGlobal s@(splitAt 6 -> ("'Tuple", reads -> [(n, "")]))) = Just (n :: Int, [])
getTTuple _ = Nothing

mkLets :: GlobalEnv' -> [Stmt]{-where block-} -> SExp{-main expression-} -> SExp{-big let with lambdas; replaces global names with de bruijn indices-}
mkLets _ [] e = e
mkLets ge (Let n _ mt _ (downS 0 -> Just x): ds) e
    = SLet (maybe id (flip SAnn . addForalls {-todo-}[] []) mt x) (substSG0 n $ mkLets ge ds e)
mkLets ge (ValueDef (ns, p) x: ds) e = patLam NoSI id ge p (deBruinify ns $ mkLets ge ds e) `SAppV` x    -- (p = e; f) -->  (\p -> f) e
mkLets _ (x: ds) e = error $ "mkLets: " ++ show x

patLam si f ge = patLam_ si f ge (Visible, Wildcard SType)

patLam_ :: SI -> (SExp -> SExp) -> GlobalEnv' -> (Visibility, SExp) -> Pat -> SExp -> SExp
patLam_ si f ge (v, t) p e = SLam_ si v t $ compileGuardTree f f ge $ compilePatts [(p, 0)] Nothing e

parseSomeGuards ns f e = do
    pos <- sourceColumn <$> getPosition <* operator "|"
    guard $ f pos
    (e', f) <-
         do (e', PCon p vs) <- try $ pattern' ns e <* operator "<-"
            x <- parseETerm ns PrecEq e
            return (e', \gs' gs -> GuardNode x p vs (Alts gs'): gs)
     <|> do x <- parseETerm ns PrecEq e
            return (e, \gs' gs -> [GuardNode x "True" [] $ Alts gs', GuardNode x "False" [] $ Alts gs])
    f <$> (parseSomeGuards ns (> pos) e' <|> (:[]) . GuardLeaf <$ operator "->" <*> parseETerm ns PrecLam e')
      <*> (parseSomeGuards ns (== pos) e <|> pure [])

toNat 0 = SGlobal "Zero"
toNat n | n > 0 = SAppV (SGlobal "Succ") $ toNat (n-1)

toNatP 0 = PCon "Zero" []
toNatP n | n > 0 = PCon "Succ" [ParPat [toNatP $ n-1]]

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

compileGuardTree :: (SExp -> SExp) -> (SExp -> SExp) -> GlobalEnv' -> GuardTree -> SExp
compileGuardTree unode node adts t = (\x -> traceD ("  !  :" ++ showSExp x) x) $ guardTreeToCases t
  where
    guardTreeToCases :: GuardTree -> SExp
    guardTreeToCases t = case alts t of
        [] -> unode $ SGlobal "undefined"
        GuardLeaf e: _ -> node e
        ts@(GuardNode f s _ _: _) -> case Map.lookup s (snd adts) of
            Nothing -> error $ "Constructor is not defined: " ++ s
            Just (Left ((t, inum), cns)) ->
                foldl SAppV (SGlobal (caseName t) `SAppV` iterateN (1 + inum) SLamV (Wildcard SType))
                    [ iterateN n SLamV $ guardTreeToCases $ Alts $ map (filterGuardTree (upS__ 0 n f) cn 0 n . upGT 0 n) ts
                    | (cn, n) <- cns
                    ]
                `SAppV` f
            Just (Right n) -> SGlobal (matchName s)
                `SAppV` (SLamV $ Wildcard SType)
                `SAppV` (iterateN n SLamV $ guardTreeToCases $ Alts $ map (filterGuardTree (upS__ 0 n f) s 0 n . upGT 0 n) ts)
                `SAppV` f
                `SAppV` (guardTreeToCases $ Alts $ map (filterGuardTree' f s) ts)

    filterGuardTree :: SExp -> SName{-constr.-} -> Int -> Int{-number of constr. params-} -> GuardTree -> GuardTree
    filterGuardTree f s k ns = \case
        GuardLeaf e -> GuardLeaf e
        Alts ts -> Alts $ map (filterGuardTree f s k ns) ts
        GuardNode f' s' ps gs
            | f /= f'  -> GuardNode f' s' ps $ filterGuardTree (upS__ 0 su f) s (su + k) ns gs
            | s == s'  -> filterGuardTree f s k ns $ guardNodes (zips [k+ns-1, k+ns-2..] ps) gs
            | otherwise -> Alts []
          where
            zips is ps = zip (map SVar $ zipWith (+) is $ sums $ map varPP ps) ps
            su = sum $ map varPP ps
            sums = scanl (+) 0

    filterGuardTree' :: SExp -> SName{-constr.-} -> GuardTree -> GuardTree
    filterGuardTree' f s = \case
        GuardLeaf e -> GuardLeaf e
        Alts ts -> Alts $ map (filterGuardTree' f s) ts
        GuardNode f' s' ps gs
            | f /= f' || s /= s' -> GuardNode f' s' ps $ filterGuardTree' (upS__ 0 su f) s gs
            | otherwise -> Alts []
          where
            su = sum $ map varPP ps

    guardNodes :: [(SExp, ParPat)] -> GuardTree -> GuardTree
    guardNodes [] l = l
    guardNodes ((v, ParPat ws): vs) e = guardNode v ws $ guardNodes vs e

    guardNode :: SExp -> [Pat] -> GuardTree -> GuardTree
    guardNode v [] e = e
    guardNode v (w: []) e = case w of
        PVar -> {-todo guardNode v (subst x v ws) $ -} varGuardNode 0 v e
        ViewPat f (ParPat p) -> guardNode (f `SAppV` v) p {- $ guardNode v ws -} e
        PCon s ps' -> GuardNode v s ps' {- $ guardNode v ws -} e

varGuardNode v (SVar e) gt = substGT v e gt

compileCase ge x cs
    = SLamV (compileGuardTree id id ge $ Alts [compilePatts [(p, 0)] Nothing e | (p, e) <- cs]) `SAppV` x

-- todo: clenup
compilePatts :: [(Pat, Int)] -> Maybe SExp -> SExp -> GuardTree
compilePatts ps gu = cp [] ps
  where
    cp ps' [] e = case gu of
        Nothing -> rhs
        Just ge -> GuardNode (rearrangeS (f $ reverse ps') ge) "True" [] rhs
      where rhs = GuardLeaf $ rearrangeS (f $ reverse ps') e
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

showEnv :: Env -> String
showEnv e = showDoc $ envDoc e $ pure $ shAtom $ underlined "<<HERE>>"

showEnvExp :: Env -> Exp -> String
showEnvExp e c = showDoc $ envDoc e $ epar <$> expDoc c

showEnvSExp :: Env -> SExp -> String
showEnvSExp e c = showDoc $ envDoc e $ epar <$> sExpDoc c

showEnvSExpType :: Env -> SExp -> Exp -> String
showEnvSExpType e c t = showDoc $ envDoc e $ epar <$> (shAnn "::" False <$> sExpDoc c <**> expDoc t)
  where
    infixl 4 <**>
    (<**>) :: NameDB (a -> b) -> NameDB a -> NameDB b
    a <**> b = get >>= \s -> lift $ evalStateT a s <*> evalStateT b s

showDoc :: Doc -> String
showDoc = str . flip runReader [] . flip evalStateT (flip (:) <$> iterate ('\'':) "" <*> ['a'..'z'])

type FreshVars = [String]

-- name De Bruijn indices
type NameDB a = StateT FreshVars (Reader DBNames) a

type Doc = NameDB PrecString

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
    ELabelEnd ts        -> envDoc ts $ shApp Visible (shAtom "labEnd") <$> m

expDoc :: Exp -> Doc
expDoc e = fmap inGreen <$> f e
  where
    f = \case
        PMLabel x _     -> f x
        FixLabel _ x    -> f x
        Var k           -> shVar k
        App a b         -> shApp Visible <$> f a <*> f b
        Lam h a b       -> join $ shLam (usedE 0 b) (BLam h) <$> f a <*> pure (f b)
        Bind h a b      -> join $ shLam (usedE 0 b) h <$> f a <*> pure (f b)
        Cstr a b        -> shCstr <$> f a <*> f b
        FunN s xs       -> foldl (shApp Visible) (shAtom s) <$> mapM f xs
        CaseFun s xs    -> foldl (shApp Visible) (shAtom $ show s) <$> mapM f xs
        TyCaseFun s xs  -> foldl (shApp Visible) (shAtom $ show s) <$> mapM f xs
        ConN s xs       -> foldl (shApp Visible) (shAtom s) <$> mapM f xs
        TyConN s xs     -> foldl (shApp Visible) (shAtom s) <$> mapM f xs
        TType           -> pure $ shAtom "Type"
        ELit l          -> pure $ shAtom $ show l
        Assign i x e    -> shLet i (f x) (f e)
        LabelEnd x      -> shApp Visible (shAtom "labend") <$> f x

sExpDoc :: SExp -> Doc
sExpDoc = \case
    SGlobal s       -> pure $ shAtom s
    SAnn a b        -> shAnn ":" False <$> sExpDoc a <*> sExpDoc b
    TyType a        -> shApp Visible (shAtom "tyType") <$> sExpDoc a
    SApp h a b      -> shApp h <$> sExpDoc a <*> sExpDoc b
    Wildcard t      -> shAnn ":" True (shAtom "_") <$> sExpDoc t
    SBind h a b     -> join $ shLam (usedS 0 b) h <$> sExpDoc a <*> pure (sExpDoc b)
    SLet a b        -> shLet_ (sExpDoc a) (sExpDoc b)
    STyped_ _ (e,t) -> expDoc e
    SVar i          -> expDoc (Var i)

shVar i = asks $ shAtom . lookupVarName where
    lookupVarName xs | i < length xs && i >= 0 = xs !! i
    lookupVarName _ = "V" ++ show i

newName = gets head <* modify tail

shLet i a b = shVar i >>= \i' -> local (dropNth i) $ shLam' <$> (cpar . shLet' (fmap inBlue i') <$> a) <*> b
shLet_ a b = newName >>= \i -> shLam' <$> (cpar . shLet' (shAtom i) <$> a) <*> local (i:) b
shLam used h a b = newName >>= \i ->
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
    | PrecProj      --  _ ._                {left}
    | PrecSwiz      --  _%_                 {left}
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

splitESC ('\ESC':'[': (span (/='m') -> (a, (c: b)))) | c == 'm' = Just (a, b)
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
throwError_ = throwError . correctEscs
traceD x = if debug then trace_ x else id

-------------------------------------------------------------------------------- main

type TraceLevel = Int
trace_level = 0 :: TraceLevel  -- 0: no trace
tr = False --trace_level >= 2
tr_light = trace_level >= 1

debug = False--True--tr
debug_light = True--False

infer :: String -> GlobalEnv -> Extensions -> [Stmt] -> Either String GlobalEnv
infer src env exs = fmap (forceGE . snd) . runExcept . flip runStateT (initEnv <> env) . flip runReaderT src . mapM_ (handleStmt exs)
  where
    forceGE x = length (concatMap (uncurry (++) . (showExp *** showExp)) $ Map.elems x) `seq` x

-------------------------------------------------------------------------------- utils

dropNth i xs = take i xs ++ drop (i+1) xs
iterateN n f e = iterate f e !! n
holes xs = [(as, x, bs) | (as, x: bs) <- zip (inits xs) (tails xs)]

