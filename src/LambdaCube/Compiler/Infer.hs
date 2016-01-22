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
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module LambdaCube.Compiler.Infer
    ( Binder (..), SName, Lit(..), Visibility(..), FunName(..), CaseFunName(..), ConName(..), TyConName(..), Export(..), ModuleR(..)
    , Exp (..), GlobalEnv
    , pattern Var, pattern Fun, pattern CaseFun, pattern TyCaseFun, pattern App, pattern FunN, pattern ConN, pattern PMLabel, pattern FixLabel
    , downE
    , litType
    , expType_, initEnv, Env(..), pattern EBind2
    , FreshVars, Infos, listInfos, ErrorMsg(..), PolyEnv(..), ErrorT, throwErrorTCM, parseLC, joinPolyEnvs, filterPolyEnv, inference_
    , ImportItems (..)
    , removeEscs
-- TEST Exports
    , SI(..), Range, showRange
    ) where

import Data.Monoid
import Data.Maybe
import Data.List
import Data.Char
import Data.String
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Identity
import Control.Arrow hiding ((<+>))
import Control.Applicative
import Control.Exception hiding (try)
import Control.DeepSeq

import Text.Parsec hiding (label, Empty, State, (<|>), many)
import qualified Text.Parsec.Token as Pa
import qualified Text.ParserCombinators.Parsec.Language as Pa
import Text.Parsec.Pos
import Text.Parsec.Indentation hiding (Any)
import Text.Parsec.Indentation.Char

import Debug.Trace

import qualified LambdaCube.Compiler.Pretty as P
import LambdaCube.Compiler.Pretty hiding (Doc, braces, parens)
import LambdaCube.Compiler.Token

-------------------------------------------------------------------------------- utils

(<&>) = flip (<$>)


-------------------------------------------------------------------------------- source data

type SName = String

type SIName = (SI, SName)

data Stmt
    = Let SIName MFixity (Maybe SExp) [Visibility]{-source arity-} SExp
    | Data SIName [(Visibility, SExp)]{-parameters-} SExp{-type-} Bool{-True:add foralls-} [(SIName, SExp)]{-constructor names and types-}
    | PrecDef SIName Fixity
    | ValueDef ([SIName], Pat) SExp
    | TypeFamily SIName [(Visibility, SExp)]{-parameters-} SExp{-type-}

    -- eliminated during parsing
    | Class SIName [SExp]{-parameters-} [(SIName, SExp)]{-method names and types-}
    | Instance SIName [Pat]{-parameter patterns-} [SExp]{-constraints-} [Stmt]{-method definitions-}
    | TypeAnn SIName SExp            -- intermediate
    | FunAlt SIName [((Visibility, SExp), Pat)] (Maybe SExp) SExp
    deriving (Show)

type Range = (SourcePos, SourcePos)

instance NFData SourcePos where
    rnf x = x `seq` ()

showRange :: Range -> String
showRange (b, e) | sourceName b == sourceName e = sourceName b ++ " " ++ f b ++ "-" ++ f e
  where
    f x = show (sourceLine x) ++ ":" ++ show (sourceColumn x)

joinRange :: Range -> Range -> Range
joinRange (b, e) (b', e') = (min b b', max e e')

-- source info
data SI
    = NoSI (Set String) -- no source info, attached debug info
    | Range Range

noSI = NoSI (Set.empty)

instance Show SI where show _ = "SI"
instance Eq SI where _ == _ = True

newtype SData a = SData a
instance Show (SData a) where show _ = "SData"
instance Eq (SData a) where _ == _ = True

siElim
  noSI
  range
  = \case
    NoSI ds -> noSI ds
    Range r -> range r

showSIRange = siElim (unwords . Set.toList) showRange

showSI :: Env -> SI -> String
showSI _ (NoSI ds) = unwords $ Set.toList ds
showSI te (Range (start,end)) = showRange start end $ fst $ extractEnv te
  where
    showRange s e source = show str
     where
      startLine = sourceLine s - 1
      endline = sourceLine e - if sourceColumn e == 1 then 1 else 0
      len = endline - startLine
      str = vcat $ (text (show s <> ":"){- <+> "-" <+> text (show e)-}):
                   map text (take len $ drop startLine $ lines source)
                ++ [text $ replicate (sourceColumn s - 1) ' ' ++ replicate (sourceColumn e - sourceColumn s) '^' | len == 1]

instance Monoid SI where
  mempty = NoSI (Set.empty)
  mappend (Range r1) (Range r2) = Range (joinRange r1 r2)
  mappend (NoSI ds1) (NoSI ds2) = NoSI  (ds1 `Set.union` ds2)
  mappend r@(Range _) _ = r
  mappend _ r@(Range _) = r

data SExp
    = SGlobal SIName
    | SBind SI Binder SIName{-parameter's name-} SExp SExp
    | SApp SI Visibility SExp SExp
    | SLet SExp SExp    -- let x = e in f   -->  SLet e f{-x is Var 0-}
    | SVar_ (SData SIName) !Int
    | STyped SI ExpType
  deriving (Eq, Show)

pattern SVar a b = SVar_ (SData a) b

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

sLit a = STyped noSI (ELit a, litType a)
pattern Primitive n mf t <- Let n mf (Just t) _ (SBuiltin "undefined") where Primitive n mf t = Let n mf (Just t) (map fst $ fst $ getParamsS t) $ SBuiltin "undefined"
pattern SType <- STyped _ (TType, TType) where SType = STyped (debugSI "pattern SType") (TType, TType)
pattern SPi  h a b <- SBind _ (BPi  h) _ a b where SPi  h a b = sBind (BPi  h) (debugSI "patternSPi2", "pattern_spi_name") a b
pattern SLam h a b <- SBind _ (BLam h) _ a b where SLam h a b = sBind (BLam h) (debugSI "patternSLam2", "pattern_slam_name") a b
pattern Wildcard t <- SBind _ BMeta _ t (SVar _ 0) where Wildcard t = sBind BMeta (debugSI "pattern Wildcard2", "pattern_wildcard_name") t (SVar (debugSI "pattern Wildcard2", ".wc") 0)
pattern Wildcard_ si t <- SBind _ BMeta _ t (SVar (si, _) 0)
pattern SAppH a b <- SApp _ Hidden a b where SAppH a b = sApp Hidden a b
pattern SAppV a b <- SApp _ Visible a b where SAppV a b = sApp Visible a b
pattern SLamV a = SLam Visible (Wildcard SType) a
pattern       SAnn a t <- STyped _ (Lam Visible TType (Lam Visible (Var 0) (Var 0)), TType :~> Var 0 :~> Var 1) `SAppV` t `SAppV` a  --  a :: t ~~> id t a
        where SAnn a t = STyped (debugSI "pattern SAnn") (Lam Visible TType (Lam Visible (Var 0) (Var 0)), TType :~> Var 0 :~> Var 1) `SAppV` t `SAppV` a
pattern       TyType a <- STyped _ (Lam Visible TType (Var 0), TType :~> TType) `SAppV` a
        where TyType a = STyped noSI (Lam Visible TType (Var 0), TType :~> TType) `SAppV` a
    -- same as  (a :: TType)     --  a :: TType   ~~>   (\(x :: TType) -> x) a
pattern SCstr a b = SBuiltin "'EqCT" `SAppV` SType `SAppV` a `SAppV` b          --    a ~ b
pattern SParEval a b = SBuiltin "parEval" `SAppV` Wildcard SType `SAppV` a `SAppV` b
pattern SLabelEnd a = SBuiltin "labelend" `SAppV` a
pattern ST2 a b = SBuiltin "'T2" `SAppV` a `SAppV` b

pattern SBuiltin s <- SGlobal (_, s) where SBuiltin s = SGlobal (debugSI $ "builtin " ++ s, s)

sApp v a b = SApp (sourceInfo a <> sourceInfo b) v a b
sBind v x a b = SBind (sourceInfo a <> sourceInfo b) v x a b

isPi (BPi _) = True
isPi _ = False

infixl 2 `SAppV`, `SAppH`, `App`, `app_`

-------------------------------------------------------------------------------- destination data

data Exp
    = Pi Visibility Exp Exp   -- TODO: prohibit meta binder here;  BLam is not allowed
    | Meta Exp Exp   -- TODO: prohibit meta binder here;  BLam is not allowed
    | Lam Visibility Exp Exp
    | Con ConName [Exp]
    | TyCon TyConName [Exp]
    | ELit Lit
    | Assign !Int Exp Exp       -- De Bruijn index decreasing assign reservedOp, only for metavariables (non-recursive) -- TODO: remove
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

pattern CstrT t a b = TFun "'EqCT" (TType :~> Var 0 :~> Var 1 :~> TType) [t, a, b]
pattern ReflCstr x  = TFun "reflCstr" (TType :~> CstrT TType (Var 0) (Var 0)) [x]
pattern Coe a b w x = TFun "coe" (TType :~> TType :~> CstrT TType (Var 1) (Var 0) :~> Var 2 :~> Var 2) [a,b,w,x]
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
pattern Empty s   <- TyCon (TyConName "'Empty" _ _ _ _ _) [EString s] where
        Empty s    = TyCon (TyConName "'Empty" Nothing (error "todo: inum2_") (TString :~> TType) (error "todo: tcn cons 3_") $ error "Empty") [EString s]
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
pattern Tuple0      = TCon "Tuple0" 0 TTuple0 []
pattern CSplit a b c <- FunN "'Split" [a, b, c]
pattern TInterpolated a = TTyCon "'Interpolated" (TType :~> TType) [a]

pattern TTuple0 :: Exp
pattern TTuple0  <- _ where TTuple0   = TTyCon0 "'Tuple0"
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
t2 (Empty a) (Empty b) = Empty (a <> b)
t2 (Empty s) _ = Empty s
t2 _ (Empty s) = Empty s
t2 a b = T2 a b

pattern EInt a      = ELit (LInt a)
pattern EFloat a    = ELit (LFloat a)
pattern EString a   = ELit (LString a)
pattern EBool a <- (getEBool -> Just a) where EBool = mkBool

mkBool False = TCon "False" 0 TBool []
mkBool True  = TCon "True"  1 TBool []

getEBool (ConN "False" []) = Just False
getEBool (ConN "True" []) = Just True
getEBool _ = Nothing

pattern LCon <- (isCon -> True)
pattern CFun <- (isCaseFunName -> True)

pattern a :~> b = Pi Visible a b

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
    = EBind1 SI Binder Env SExp            -- zoom into first parameter of SBind
    | EBind2_ SI Binder Exp Env             -- zoom into second parameter of SBind
    | EApp1 SI Visibility Env SExp
    | EApp2 SI Visibility Exp Env
    | ELet1 Env SExp
    | ELet2 ExpType Env
    | EGlobal String{-full source of current module-} GlobalEnv [Stmt]
    | ELabelEnd Env

    | EBind1' Binder Env Exp            -- todo: move Exp zipper constructor to a separate ADT (if needed)
    | EPrim SName [Exp] Env [Exp]    -- todo: move Exp zipper constructor to a separate ADT (if needed)

    | EAssign Int Exp Env
    | CheckType_ SI Exp Env
    | CheckIType SExp Env
    | CheckSame Exp Env
    | CheckAppType SI Visibility Exp Env SExp   --pattern CheckAppType h t te b = EApp1 h (CheckType t te) b
  deriving Show

pattern EBind2 b e env <- EBind2_ _ b e env where EBind2 b e env = EBind2_ (debugSI "6") b e env
pattern CheckType e env <- CheckType_ _ e env where CheckType e env = CheckType_ (debugSI "7") e env

type GlobalEnv = Map.Map SName (Exp, Type, SI)

extractEnv :: Env -> (String, GlobalEnv)
extractEnv = either id extractEnv . parent

parent = \case
    EAssign _ _ x        -> Right x
    EBind2 _ _ x         -> Right x
    EBind1 _ _ x _       -> Right x
    EBind1' _ x _        -> Right x
    EApp1 _ _ x _        -> Right x
    EApp2 _ _ _ x        -> Right x
    ELet1 x _            -> Right x
    ELet2 _ x            -> Right x
    CheckType _ x        -> Right x
    CheckIType _ x       -> Right x
    CheckSame _ x        -> Right x
    CheckAppType _ _ _ x _ -> Right x
    EPrim _ _ x _        -> Right x
    ELabelEnd x          -> Right x
    EGlobal s x _        -> Left (s, x)


initEnv :: GlobalEnv
initEnv = Map.fromList
    [ (,) "'Type" (TType, TType, debugSI "initEnv")     -- needed?
    ]

-- monad used during elaborating statments -- TODO: use zippers instead
type ElabStmtM m = ReaderT String{-full source-} (StateT GlobalEnv (ExceptT String (WriterT Infos m)))

newtype Infos = Infos (Map.Map (SourcePos, SourcePos) (Set.Set String))
    deriving (NFData)

instance Monoid Infos where
    mempty = Infos mempty
    Infos x `mappend` Infos y = Infos $ Map.unionWith mappend x y

-- TODO: remove
validPos p = sourceColumn p /= 1 || sourceLine p /= 1
validSI (Range (a, b)) = validPos a && validPos b
validSI _ = False

si@(Range r) `validate` xs | all validSI xs && all (/= r) [r | Range r <- xs]  = si
_ `validate` _ = noSI

mkInfoItem (Range (a, b)) i | validPos a && validPos b = Infos $ Map.singleton (a, b) $ Set.singleton i
mkInfoItem _ _ = mempty

listInfos (Infos m) = [(a,b, Set.toList i) | ((a, b), i) <- Map.toList m]

-------------------------------------------------------------------------------- low-level toolbox

label LabelFix x y = FixLabel x y
label LabelPM x (UL (LabelEnd y)) = y
label LabelPM x y = PMLabel x y

--pattern UApp a b <- {-UnLabel-} (App (isInjective -> Just a) b) where UApp = App
pattern UVar n = Var n

--isInjective _ = Nothing
--isInjective a = Just a

instance Eq Exp where
    PMLabel a _ == PMLabel a' _ = a == a'
    FixLabel a _ == FixLabel a' _ = a == a'
    FixLabel _ a == a' = a == a'
    a == FixLabel _ a' = a == a'
    Lam' a == Lam' a' = a == a'
    Meta b c == Meta b' c' = (b, c) == (b', c')
    Pi a b c == Pi a' b' c' = (a, b, c) == (a', b', c')
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
    SApp _ _ a b -> foldS g f i a <> foldS g f i b
    SLet a b -> foldS g f i a <> foldS g f (i+1) b
    SBind _ _ _ a b -> foldS g f i a <> foldS g f (i+1) b
    STyped si (e, t) -> f si i e <> f si i t
    SVar (si, _) j -> f si i (Var j)
    SGlobal (si, x) -> g si i x

foldE f i = \case
    PMLabel x _ -> foldE f i x
    FixLabel _ x -> foldE f i x     -- ???
    Var k -> f i k
    Lam' b -> {-foldE f i t <>  todo: explain why this is not needed -} foldE f (i+1) b
    Meta a b -> foldE f i a <> foldE f (i+1) b
    Pi _ a b -> foldE f i a <> foldE f (i+1) b
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

usedS = (getAny .) . foldS mempty (const $ (Any .) . usedE)
usedE = (getAny .) . foldE ((Any .) . (==))

mapS = mapS_ (\si _ x -> SGlobal (si, x))
mapS_ gg ff = mapS__ gg ff $ \sn i j -> case ff i $ Var j of
            Var k -> SVar sn k
            -- x -> STyped x -- todo
mapS__ gg f1 f2 h e = g e where
    g i = \case
        SApp si v a b -> SApp si v (g i a) (g i b)
        SLet a b -> SLet (g i a) (g (h i) b)
        SBind si k si' a b -> SBind si k si' (g i a) (g (h i) b)
        STyped si (x, t) -> STyped si (f1 i x, f1 i t)
        SVar sn j -> f2 sn i j
        SGlobal (si, x) -> gg si i x

rearrangeS :: (Int -> Int) -> SExp -> SExp
rearrangeS f = mapS__ (\si _ x -> SGlobal (si,x)) (const id) (\sn i j -> SVar sn $ if j < i then j else i + f (j - i)) (+1) 0

upS__ i n = mapS (\i -> upE i n) (+1) i
upS = upS__ 0 1

up1E i = \case
    Var k -> Var $ if k >= i then k+1 else k
    Lam h a b -> Lam h (up1E i a) (up1E (i+1) b)
    Meta a b -> Meta (up1E i a) (up1E (i+1) b)
    Pi h a b -> Pi h (up1E i a) (up1E (i+1) b)
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
substSS k x = mapS__ (\si _ x -> SGlobal (si, x)) (error "substSS") (\sn (i, x) j -> case compare j i of
            EQ -> x
            GT -> SVar sn $ j - 1
            LT -> SVar sn j
            ) ((+1) *** upS) (k, x)
substS j x = mapS (uncurry $ substE "substS") ((+1) *** up1E 0) (j, x)
substSG :: SName -> (SI -> SExp) -> SExp -> SExp
substSG j x = mapS_ (\si x i -> if i == j then x si else SGlobal (si, i)) (const id) (fmap upS) x
substSG0 n e = substSG n (\si -> (SVar (si, n) 0)) $ upS e

substE err = substE_ (error $ "substE: todo: environment required in " ++ err)  -- todo: remove

substE_ :: Env -> Int -> Exp -> Exp -> Exp
substE_ te i x = \case
    Label lk z v -> label lk (substE "slab" i x z) $ substE_ te{-todo: label env?-} i x v
    Var k -> case compare k i of GT -> Var $ k - 1; LT -> Var k; EQ -> x
    Lam h a b -> let  -- question: is mutual recursion good here?
            a' = substE_ (EBind1' (BLam h) te b') i x a
            b' = substE_ (EBind2 (BLam h) a' te) (i+1) (up1E 0 x) b
        in Lam h a' b'
    Meta a b -> let  -- question: is mutual recursion good here?
            a' = substE_ te i x a
            b' = substE_ (EBind2 BMeta a' te) (i+1) (up1E 0 x) b
        in Meta a' b'
    Pi h a b -> let  -- question: is mutual recursion good here?
            a' = substE_ te i x a
            b' = substE_ (EBind2 (BPi h) a' te) (i+1) (up1E 0 x) b
        in Pi h a' b'
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

twoOpBool :: (forall a . Ord a => a -> a -> Bool) -> Exp -> Exp -> Maybe Exp
twoOpBool f (EFloat x) (EFloat y) = Just $ EBool $ f x y
twoOpBool f (EInt x) (EInt y) = Just $ EBool $ f x y
twoOpBool _ _ _ = Nothing

eval te = \case
    FunN "'FragOps'" [UL (FunN "'FragOps" [UL x])] -> x

    App a b -> app_ a b
    CstrT TType a b -> cstr a b
    CstrT t a b -> cstrT t a b
    ReflCstr a -> reflCstr te a
    Coe a b TT d -> d

    CaseFun (CaseFunName _ t pars) (drop (pars + 1) -> ps@(last -> UL (Con (ConName _ _ i _) (drop pars -> vs)))) | i /= (-1) -> foldl app_ (ps !! i) vs
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

    FunN "PrimGreaterThan" [_, _, _, _, _, _, _, x, y] | Just r <- twoOpBool (>) x y -> r
    FunN "PrimGreaterThanEqual" [_, _, _, _, _, _, _, x, y] | Just r <- twoOpBool (>=) x y -> r
    FunN "PrimLessThan" [_, _, _, _, _, _, _, x, y] | Just r <- twoOpBool (<) x y -> r
    FunN "PrimLessThanEqual" [_, _, _, _, _, _, _, x, y] | Just r <- twoOpBool (<=) x y -> r
    FunN "PrimEqualV" [_, _, _, _, _, _, _, x, y] | Just r <- twoOpBool (==) x y -> r
    FunN "PrimNotEqualV" [_, _, _, _, _, _, _, x, y] | Just r <- twoOpBool (/=) x y -> r
    FunN "PrimEqual" [_, _, _, x, y] | Just r <- twoOpBool (==) x y -> r
    FunN "PrimNotEqual" [_, _, _, x, y] | Just r <- twoOpBool (/=) x y -> r
    FunN "PrimSubS" [_, _, _, _, x, y] | Just r <- twoOp (-) x y -> r
    FunN "PrimSub"  [_, _, x, y] | Just r <- twoOp (-) x y -> r
    FunN "PrimAddS" [_, _, _, _, x, y] | Just r <- twoOp (+) x y -> r
    FunN "PrimAdd"  [_, _, x, y] | Just r <- twoOp (+) x y -> r
    FunN "PrimMulS" [_, _, _, _, x, y] | Just r <- twoOp (*) x y -> r
    FunN "PrimMul"  [_, _, x, y] | Just r <- twoOp (*) x y -> r
    FunN "PrimDivS" [_, _, _, _, _, x, y] | Just r <- twoOp_ (/) div x y -> r
    FunN "PrimDiv"  [_, _, _, _, _, x, y] | Just r <- twoOp_ (/) div x y -> r
    FunN "PrimModS" [_, _, _, _, _, x, y] | Just r <- twoOp_ modF mod x y -> r
    FunN "PrimMod"  [_, _, _, _, _, x, y] | Just r <- twoOp_ modF mod x y -> r
    FunN "PrimNeg"  [_, x] | Just r <- oneOp negate x -> r
    FunN "PrimAnd"  [EBool x, EBool y] -> EBool (x && y)
    FunN "PrimOr"   [EBool x, EBool y] -> EBool (x || y)
    FunN "PrimXor"  [EBool x, EBool y] -> EBool (x /= y)
    FunN "PrimNot"  [_, _, _, EBool x] -> EBool $ not x

    FunN "unsafeCoerce" [_, _, x@LCon] -> x

-- todo: elim

    Fun n@(FunName "natElim" _ _) [a, z, s, Succ x] -> let      -- todo: replace let with better abstraction
                sx = s `app_` x
            in sx `app_` eval (EApp2 noSI Visible sx te) (Fun n [a, z, s, x])
    FunN "natElim" [_, z, s, Zero] -> z
    Fun na@(FunName "finElim" _ _) [m, z, s, n, ConN "FSucc" [i, x]] -> let six = s `app_` i `app_` x-- todo: replace let with better abstraction
        in six `app_` eval (EApp2 noSI Visible six te) (Fun na [m, z, s, i, x])
    FunN "finElim" [m, z, s, n, ConN "FZero" [i]] -> z `app_` i

    FunN "'TFFrameBuffer" [TyConN "'Image" [n, t]] -> TFrameBuffer n t
    FunN "'TFFrameBuffer" [TyConN "'Tuple2" [TyConN "'Image" [i, t], TyConN "'Image" [i', t']]] -> TFrameBuffer i $ tTuple2 t t'
    FunN "'TFFrameBuffer" [TyConN "'Tuple3" [TyConN "'Image" [i, t], TyConN "'Image" [i', t'], TyConN "'Image" [i'', t'']]] -> TFrameBuffer i $ tTuple3 t t' t''

    FunN "'SameLayerCounts" [TyConN "'Image" [n, t]] -> Unit
    FunN "'SameLayerCounts" [TyConN "'Tuple2" [TyConN "'Image" [i, t], TyConN "'Image" [i', t']]] -> cstrT TNat i i'
    FunN "'SameLayerCounts" [TyConN "'Tuple3" [TyConN "'Image" [i, t], TyConN "'Image" [i', t'], TyConN "'Image" [i'', t'']]] -> t2 (cstrT TNat i i') (cstrT TNat i i'')

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

cstrT t (UL a) (UL a') | a == a' = Unit
cstrT t (ConN "Succ" [a]) (ConN "Succ" [a']) = cstrT TNat a a'
cstrT t (FixLabel _ a) a' = cstrT t a a'
cstrT t a (FixLabel _ a') = cstrT t a a'
cstrT t a a' = CstrT t a a'

cstr = cstrT_ TType

-- todo: use typ
cstrT_ typ = cstr__ []
  where
    cstr__ = cstr_

    cstr_ [] (UL a) (UL a') | a == a' = Unit
    cstr_ ns (LabelEnd a) a' = cstr_ ns a a'
    cstr_ ns a (LabelEnd a') = cstr_ ns a a'
    cstr_ ns (FixLabel _ a) a' = cstr_ ns a a'
    cstr_ ns a (FixLabel _ a') = cstr_ ns a a'
--    cstr_ ns (PMLabel a _) a' = cstr_ ns a a'
--    cstr_ ns a (PMLabel a' _) = cstr_ ns a a'
--    cstr_ ns TType TType = Unit
    cstr_ ns (Con a xs) (Con a' xs') | a == a' = foldr t2 Unit $ zipWith (cstr__ ns) xs xs'
    cstr_ [] (TyConN "'FrameBuffer" [a, b]) (TyConN "'FrameBuffer" [a', b']) = t2 (cstrT TNat a a') (cstr__ [] b b')    -- todo: elim
    cstr_ ns (TyCon a xs) (TyCon a' xs') | a == a' = foldr t2 Unit $ zipWith (cstr__ ns) xs xs'
--    cstr_ ns (TyCon a []) (TyCon a' []) | a == a' = Unit
    cstr_ ns (Var i) (Var i') | i == i', i < length ns = Unit
    cstr_ (_: ns) (downE 0 -> Just a) (downE 0 -> Just a') = cstr__ ns a a'
--    cstr_ ((t, t'): ns) (UApp (downE 0 -> Just a) (UVar 0)) (UApp (downE 0 -> Just a') (UVar 0)) = traceInj2 (a, "V0") (a', "V0") $ cstr__ ns a a'
--    cstr_ ((t, t'): ns) a (UApp (downE 0 -> Just a') (UVar 0)) = traceInj (a', "V0") a $ cstr__ ns (Lam Visible t a) a'
--    cstr_ ((t, t'): ns) (UApp (downE 0 -> Just a) (UVar 0)) a' = traceInj (a, "V0") a' $ cstr__ ns a (Lam Visible t' a')
    cstr_ ns (Lam h a b) (Lam h' a' b') | h == h' = t2 (cstr__ ns a a') (cstr__ ((a, a'): ns) b b')
    cstr_ ns (Pi h a b) (Pi h' a' b') | h == h' = t2 (cstr__ ns a a') (cstr__ ((a, a'): ns) b b')
    cstr_ ns (Meta a b) (Meta a' b') = t2 (cstr__ ns a a') (cstr__ ((a, a'): ns) b b')
--    cstr_ [] t (Meta a b) = Meta a $ cstr_ [] (up1E 0 t) b
--    cstr_ [] (Meta a b) t = Meta a $ cstr_ [] b (up1E 0 t)
--    cstr_ ns (unApp -> Just (a, b)) (unApp -> Just (a', b')) = traceInj2 (a, show b) (a', show b') $ t2 (cstr__ ns a a') (cstr__ ns b b')
--    cstr_ ns (unApp -> Just (a, b)) (unApp -> Just (a', b')) = traceInj2 (a, show b) (a', show b') $ t2 (cstr__ ns a a') (cstr__ ns b b')
--    cstr_ ns (Label f xs _) (Label f' xs' _) | f == f' = foldr1 T2 $ zipWith (cstr__ ns) xs xs'
    cstr_ [] (UL (FunN "'VecScalar" [a, b])) (TVec a' b') = t2 (cstrT TNat a a') (cstr__ [] b b')
    cstr_ [] (UL (FunN "'VecScalar" [a, b])) (UL (FunN "'VecScalar" [a', b'])) = t2 (cstrT TNat a a') (cstr__ [] b b')
    cstr_ [] (UL (FunN "'VecScalar" [a, b])) t@(TTyCon0 n) | isElemTy n = t2 (cstrT TNat a (NatE 1)) (cstr__ [] b t)
    cstr_ [] t@(TTyCon0 n) (UL (FunN "'VecScalar" [a, b])) | isElemTy n = t2 (cstrT TNat a (NatE 1)) (cstr__ [] b t)
    cstr_ ns@[] (UL (FunN "'TFMat" [x, y])) (TyConN "'Mat" [i, j, a]) = t2 (cstr__ ns x (TVec i a)) (cstr__ ns y (TVec j a))
    cstr_ ns@[] (TyConN "'Tuple2" [x, y]) (UL (FunN "'JoinTupleType" [x', y'])) = t2 (cstr__ ns x x') (cstr__ ns y y')
    cstr_ ns@[] (UL (FunN "'FragOps'" [a])) (TyConN "'FragmentOperation" [x]) = cstr__ ns a x
    cstr_ ns@[] (UL (FunN "'FragOps'" [a])) (TyConN "'Tuple2" [TyConN "'FragmentOperation" [x], TyConN "'FragmentOperation" [y]]) = cstr__ ns a $ tTuple2 x y
    cstr_ ns@[] (UL (FunN "'JoinTupleType" [x', y'])) (TyConN "'Tuple2" [x, y]) = t2 (cstr__ ns x' x) (cstr__ ns y' y)
    cstr_ ns@[] (UL (FunN "'JoinTupleType" [x', y'])) x@NoTup  = t2 (cstr__ ns x' x) (cstr__ ns y' TTuple0)
    cstr_ ns@[] (x@NoTup) (UL (FunN "'InterpolatedType" [x'])) = cstr__ ns (TInterpolated x) x'
    cstr_ [] (TyConN "'FrameBuffer" [a, b]) (UL (FunN "'TFFrameBuffer" [TyConN "'Image" [a', b']])) = T2 (cstrT TNat a a') (cstr__ [] b b')
    cstr_ [] a@App{} a'@App{} = CstrT TType a a'
    cstr_ [] a@CFun a'@CFun = CstrT TType a a'
    cstr_ [] a@LCon a'@CFun = CstrT TType a a'
    cstr_ [] a@LCon a'@App{} = CstrT TType a a'
    cstr_ [] a@CFun a'@LCon = CstrT TType a a'
    cstr_ [] a@App{} a'@LCon = CstrT TType a a'
    cstr_ [] a@PMLabel{} a' = CstrT TType a a'
    cstr_ [] a a'@PMLabel{} = CstrT TType a a'
    cstr_ [] a a' | isVar a || isVar a' = CstrT TType a a'
    cstr_ ns a a' = Empty $ unlines [ "can not unify"
                                    , showExp a
                                    , "with"
                                    , showExp a'
                                    ]

--    unApp (UApp a b) | isInjective a = Just (a, b)         -- TODO: injectivity check
    unApp (Con a xs@(_:_)) = Just (Con a (init xs), last xs)
    unApp (TyCon a xs@(_:_)) = Just (TyCon a (init xs), last xs)
    unApp _ = Nothing

    isInjective _ = True--False

    isVar UVar{} = True
    isVar (App a b) = isVar a
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

-------------------------------------------------------------------------------- simple typing

litType = \case
    LInt _    -> TInt
    LFloat _  -> TFloat
    LString _ -> TString
    LChar _   -> TChar

expType_ msg te = \case
    Lam h t x -> Pi h t $ expType (EBind2 (BLam h) t te) x
    App f x -> app (expType te{-todo: precise env-} f) x
    Var i -> snd $ varType "C" i te
    Pi{} -> TType
    Label _ x _ -> expType te x
    TFun _ t ts -> foldl app t ts
    CaseFun (CaseFunName _ t _) ts   -> foldl app t ts
    TyCaseFun (TyCaseFunName _ t) ts -> foldl app t ts
    TCon _ _ t ts -> foldl app t ts
    TTyCon _ t ts -> foldl app t ts
    TType -> TType
    ELit l -> litType l
--    Meta t x -> expType (EBind2 BMeta t te) x --error "meta type"
    Meta{} -> error "meta type"
    Assign{} -> error "let type"
    LabelEnd x -> expType te x
  where
    expType = expType_ msg
    app (Pi _ a b) x = substE "expType_" 0 x b
    app t x = error $ "app " ++ msg ++ ": " ++ show t

-------------------------------------------------------------------------------- inference

type TCM m = ExceptT String (WriterT Infos m)

runTCM = either error id . runExcept

expAndType (e, t, si) = (e, t)

-- todo: do only if NoTypeNamespace extension is not on
lookupName s@('\'':s') m = expAndType <$> (maybe (Map.lookup s' m) Just $ Map.lookup s m)
lookupName s m           = expAndType <$> Map.lookup s m
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
        SAnn x t        -> checkN (CheckIType x te) t TType
        SLabelEnd x     -> infer (ELabelEnd te) x
        SVar (si, _) i  -> focus_' te exp (Var i, expType_ "1" te (Var i))
        STyped si et    -> focus_' te exp et
        SGlobal (si, s) -> focus_' te exp =<< getDef te si s
        SApp si h a b   -> infer (EApp1 (si `validate` [sourceInfo a, sourceInfo b]) h te b) a
        SLet a b        -> infer (ELet1 te b{-in-}) a{-let-} -- infer te SLamV b `SAppV` a)
        SBind si h _ a b -> infer ((if h /= BMeta then CheckType_ (sourceInfo exp) TType else id) $ EBind1 si h te $ (if isPi h then TyType else id) b) a

    checkN :: Env -> SExp -> Exp -> TCM m ExpType
    checkN te x t = do
        (if tracelevel >= 1 then trace_ $ "check: " ++ showEnvSExpType te x t else id) $ checkN_ te x t

    checkN_ te e t
            -- temporal hack
        | x@(SGlobal (si, MatchName n)) `SAppV` SLamV (Wildcard_ siw _) `SAppV` a `SAppV` (SVar siv v) `SAppV` b <- e
            = infer te $ x `SAppV` (STyped noSI (Lam Visible TType $ substE "checkN" (v+1) (Var 0) $ up1E 0 t, TType :~> TType)) `SAppV` a `SAppV` SVar siv v `SAppV` b
            -- temporal hack
        | x@(SGlobal (si, "'NatCase")) `SAppV` SLamV (Wildcard_ siw _) `SAppV` a `SAppV` b `SAppV` (SVar siv v) <- e
            = infer te $ x `SAppV` (STyped noSI (Lam Visible TNat $ substE "checkN" (v+1) (Var 0) $ up1E 0 t, TNat :~> TType)) `SAppV` a `SAppV` b `SAppV` SVar siv v
{-
            -- temporal hack
        | x@(SGlobal "'VecSCase") `SAppV` SLamV (SLamV (Wildcard _)) `SAppV` a `SAppV` b `SAppV` c `SAppV` SVar v <- e
            = infer te $ x `SAppV` (SLamV (SLamV (STyped (substE "checkN" (v+1) (Var 0) $ upE 0 2 t, TType)))) `SAppV` a `SAppV` b `SAppV` c `SAppV` SVar v
-}
            -- temporal hack
        | SGlobal (si, "undefined") <- e = focus' te e $ Undef t
        | SLabelEnd x <- e = checkN (ELabelEnd te) x t
        | SApp si h a b <- e = infer (CheckAppType si h t te b) a
        | SLam h a b <- e, Pi h' x y <- t, h == h'  = do
            tellType te e t
            same <- return $ checkSame te a x
            if same then checkN (EBind2 (BLam h) x te) b y else error $ "checkSame:\n" ++ show a ++ "\nwith\n" ++ showEnvExp te x
        | Pi Hidden a b <- t, notHiddenLam e = checkN (EBind2 (BLam Hidden) a te) (upS e) b
        | otherwise = infer (CheckType_ (sourceInfo e) t te) e
      where
        -- todo
        notHiddenLam = \case
            SLam Visible _ _ -> True
            SGlobal (si,s) | Lam Hidden _ _ <- fst $ fromMaybe (error $ "infer: can't find: " ++ s) $ lookupName s $ snd $ extractEnv te -> False
                            -- todo: use type instead of expr.
                           | otherwise -> True
            _ -> False
{-
    -- todo
    checkSame te (Wildcard _) a = return (te, True)
    checkSame te x y = do
        (ex, _) <- checkN te x TType
        return $ ex == y
-}
    checkSame te (Wildcard _) a = True
    checkSame te (SGlobal (_,"'Type")) TType = True
    checkSame te (STyped _ (TType, TType)) TType = True
    checkSame te (SBind _ BMeta _ SType (STyped _ (Var 0, _))) a = True
    checkSame te a b = error $ "checkSame: " ++ show (a, b)

    hArgs (Pi Hidden _ b) = 1 + hArgs b
    hArgs _ = 0

    focus env e = focus_ env (e, expType_ "2" env e)
    focus' env si e = focus_' env si (e, expType_ "2" env e)
    focus_' env si (e, et) = tellType env si et >> focus_ env (e, et)

    focus_ :: Env -> ExpType -> TCM m ExpType
    focus_ env (e, et) = (if tracelevel >= 1 then trace_ $ "focus: " ++ showEnvExp env e else id) $ (if debug then fmap (recheck' "focus" env *** id) else id) $ case env of
        ELabelEnd te -> focus_ te (LabelEnd e, et)
        CheckSame x te -> focus_ (EBind2_ (debugSI "focus_ CheckSame") BMeta (cstr x e) te) (up1E 0 e, up1E 0 et)
        CheckAppType si h t te b   -- App1 h (CheckType t te) b
            | Pi h' x (downE 0 -> Just y) <- et, h == h' -> case t of
                Pi Hidden t1 t2 | h == Visible -> focus_ (EApp1 si h (CheckType_ (sourceInfo b) t te) b) (e, et)  -- <<e>> b : {t1} -> {t2}
                _ -> focus_ (EBind2_ (sourceInfo b) BMeta (cstr t y) $ EApp1 si h te b) (up1E 0 e, up1E 0 et)
            | otherwise -> focus_ (EApp1 si h (CheckType_ (sourceInfo b) t te) b) (e, et)
        EApp1 si h te b
            | Pi h' x y <- et, h == h' -> checkN (EApp2 si h e te) b x
            | Pi Hidden x y  <- et, h == Visible -> focus_ (EApp1 noSI Hidden env $ Wildcard $ Wildcard SType) (e, et)  --  e b --> e _ b
--            | CheckType (Pi Hidden _ _) te' <- te -> error "ok"
--            | CheckAppType Hidden _ te' _ <- te -> error "ok"
            | otherwise -> infer (CheckType_ (sourceInfo b) (Var 2) $ cstr' h (upE 0 2 et) (Pi Visible (Var 1) (Var 1)) (upE 0 2 e) $ EBind2_ (sourceInfo b) BMeta TType $ EBind2_ (sourceInfo b) BMeta TType te) (upS__ 0 3 b)
          where
            cstr' h x y e = EApp2 noSI h (eval (error "cstr'") $ Coe (up1E 0 x) (up1E 0 y) (Var 0) (up1E 0 e)) . EBind2_ (sourceInfo b) BMeta (cstr x y)
        ELet1 te b{-in-} -> replaceMetas "let" Lam e >>= \e' -> infer (ELet2 (addType_ te e'{-let-}) te) b{-in-}
        ELet2 (x{-let-}, xt) te -> focus_ te (substE "app2" 0 (x{-let-}) (  e{-in-}), et)
        CheckIType x te -> checkN te x e
        CheckType_ si t te
            | hArgs et > hArgs t
                            -> focus_ (EApp1 noSI Hidden (CheckType_ si t te) $ Wildcard $ Wildcard SType) (e, et)
            | hArgs et < hArgs t, Pi Hidden t1 t2 <- t
                            -> focus_ (CheckType_ si t2 $ EBind2 (BLam Hidden) t1 te) (e, et)
            | otherwise     -> focus_ (EBind2_ si BMeta (cstr t et) te) (up1E 0 e, up1E 0 et)
        EApp2 si h a te     -> focus' te si $ app_ a e        --  h??
        EBind1 si h te b     -> infer (EBind2_ (sourceInfo b) h e te) b
        EBind2_ si BMeta tt te
            | Unit <- tt    -> refocus te $ both (substE_ te 0 TT) (e, et)
            | Empty msg <- tt   -> throwError $ "type error: " ++ msg ++ "\nin " ++ showSI te si ++ "\n"-- todo: better error msg
            | T2 x y <- tt -> let
                    te' = EBind2_ si BMeta (up1E 0 y) $ EBind2_ si BMeta x te
                in focus_ te' $ both (substE_ te' 2 (t2C (Var 1) (Var 0)) . upE 0 2) (e, et)
            | CstrT t a b <- tt, a == b  -> refocus te $ both (substE "inferN2" 0 TT) (e, et)
            | CstrT t a b <- tt, Just r <- cst a b -> r
            | CstrT t a b <- tt, Just r <- cst b a -> r
            | isCstr tt, EBind2 h x te' <- te{-, h /= BMeta todo: remove-}, Just x' <- downE 0 tt, x == x'
                            -> refocus te $ both (substE "inferN3" 1 (Var 0)) (e, et)
            | EBind2 h x te' <- te, h /= BMeta, Just b' <- downE 0 tt
                            -> refocus (EBind2_ si h (up1E 0 x) $ EBind2_ si BMeta b' te') $ both (substE "inferN3" 2 (Var 0) . up1E 0) (e, et)
            | ELet2 (x, xt) te' <- te, Just b' <- downE 0 tt
                            -> refocus (ELet2 (up1E 0 x, up1E 0 xt) $ EBind2_ si BMeta b' te') $ both (substE "inferN32" 2 (Var 0) . up1E 0) (e, et)
            | EBind1 si h te' x <- te -> refocus (EBind1 si h (EBind2_ si BMeta tt te') $ upS__ 1 1 x) (e, et)
            | ELet1 te' x     <- te, {-usedE 0 e, -} floatLetMeta $ expType_ "3" env $ replaceMetas' Lam $ Meta tt e --not (tt == TType) {-todo: tweak?-}
                                    -> refocus (ELet1 (EBind2_ si BMeta tt te') $ upS__ 1 1 x) (e, et)
            | CheckAppType si h t te' x <- te -> refocus (CheckAppType si h (up1E 0 t) (EBind2_ si BMeta tt te') $ upS x) (e, et)
            | EApp1 si h te' x <- te -> refocus (EApp1 si h (EBind2_ si BMeta tt te') $ upS x) (e, et)
            | EApp2 si h x te' <- te -> refocus (EApp2 si h (up1E 0 x) $ EBind2_ si BMeta tt te') (e, et)
            | CheckType_ si t te' <- te -> refocus (CheckType_ si (up1E 0 t) $ EBind2_ si BMeta tt te') (e, et)
--            | CheckIType x te' <- te -> refocus (CheckType_ si (up1E 0 t) $ EBind2_ si BMeta tt te') (e, et)
            | ELabelEnd te'   <- te -> refocus (ELabelEnd $ EBind2_ si BMeta tt te') (e, et)
            | otherwise             -> focus_ te (Meta tt e, et {-???-})
          where
            cst x = \case
                Var i | fst (varType "X" i te) == BMeta
                      , Just y <- downE i x
                      -> Just $ assign'' te i y $ both (substE_ te 0 ({-ReflCstr y-}TT) . substE_ te (i+1) (up1E 0 y)) (e, et)
                _ -> Nothing
        EBind2_ si (BLam h) a te -> focus_ te (Lam h a e, Pi h a e)
        EBind2_ si (BPi h) a te -> focus_' te si (Pi h a e, TType)
        EAssign i b te -> case te of
            EBind2_ si h x te' | i > 0, Just b' <- downE 0 b
                              -> refocus' (EBind2_ si h (substE "inferN5" (i-1) b' x) (EAssign (i-1) b' te')) (e, et)
            ELet2 (x, xt) te' | i > 0, Just b' <- downE 0 b
                              -> refocus' (ELet2 (substE "inferN51" (i-1) b' x, substE "inferN52" (i-1) b' xt) (EAssign (i-1) b' te')) (e, et)
            ELet1 te' x       -> refocus' (ELet1 (EAssign i b te') $ substS (i+1) (up1E 0 b) x) (e, et)
            EBind1 si h te' x -> refocus' (EBind1 si h (EAssign i b te') $ substS (i+1) (up1E 0 b) x) (e, et)
            CheckAppType si h t te' x -> refocus' (CheckAppType si h (substE "inferN6" i b t) (EAssign i b te') $ substS i b x) (e, et)
            EApp1 si h te' x  -> refocus' (EApp1 si h (EAssign i b te') $ substS i b x) (e, et)
            EApp2 si h x te'  -> refocus' (EApp2 si h (substE_ te'{-todo: precise env-} i b x) $ EAssign i b te') (e, et)
            CheckType_ si t te'   -> refocus' (CheckType_ si (substE "inferN8" i b t) $ EAssign i b te') (e, et)
            ELabelEnd te'     -> refocus' (ELabelEnd $ EAssign i b te') (e, et)
            EAssign j a te' | i < j
                              -> focus_ (EAssign (j-1) (substE "ea" i b a) $ EAssign i (upE (j-1) 1 b) te') (e, et)
            te@EBind2{}       -> maybe (assign' te i b (e, et)) (flip refocus' (e, et)) $ pull i te
            te@EAssign{}      -> maybe (assign' te i b (e, et)) (flip refocus' (e, et)) $ pull i te
            -- todo: CheckSame Exp Env
          where
            pull i = \case
                EBind2 BMeta _ te | i == 0 -> Just te
                EBind2_ si h x te   -> EBind2_ si h <$> downE (i-1) x <*> pull (i-1) te
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

        refocus_ f e (Meta x a, t) = f (EBind2 BMeta x e) (a, t)
        refocus_ _ e (Assign i x a, t) = focus (EAssign i x e) a
        refocus_ _ e (a, t) = focus e a

debugSI a = NoSI (Set.singleton a)

isCstr (CstrT _ _ _) = True
isCstr (UL (FunN s _)) = s `elem` ["'Eq", "'Ord", "'Num", "'CNum", "'Signed", "'Component", "'Integral", "'NumComponent", "'Floating"]       -- todo: use Constraint type to decide this
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
        EBind1 si h e b -> EBind1 si h (checkEnv e) b
        EBind2_ si h t e -> EBind2_ si h (recheckEnv e t) $ checkEnv e            --  E [\(x :: t) -> e]    -> check  E [t]
        ELet1 e b -> ELet1 (checkEnv e) b
        ELet2 (x, t) e -> ELet2 (recheckEnv e x, recheckEnv e t{-?-}) $ checkEnv e
        EApp1 si h e b -> EApp1 si h (checkEnv e) b
        EApp2 si h a e -> EApp2 si h (recheckEnv {-(EApp1 h e _)-}e a) $ checkEnv e              --  E [a x]        ->  check  
        EAssign i x e -> EAssign i (recheckEnv e $ up1E i x) $ checkEnv e                -- __ <i := x>
        CheckType_ si x e -> CheckType_ si (recheckEnv e x) $ checkEnv e
        CheckSame x e -> CheckSame (recheckEnv e x) $ checkEnv e
        CheckAppType si h x e y -> CheckAppType si h (recheckEnv e x) (checkEnv e) y

    recheckEnv = recheck_ "env"

    recheck_ msg te = \case
        Var k -> Var k
        Lam h a b -> Lam h (ch True te{-ok?-} a) $ ch False (EBind2 (BLam h) a te) b
        Meta a b -> Meta (ch False te{-ok?-} a) $ ch False (EBind2 BMeta a te) b
        Pi h a b -> Pi h (ch True te{-ok?-} a) $ ch True (EBind2 (BPi h) a te) b
        App a b -> appf (recheck'' "app1" te{-ok?-} a) (recheck'' "app2" (EApp2 noSI Visible a te) b)
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
            | otherwise = error_ $ "recheck " ++ msg' ++ "; " ++ msg ++ "\nexpected: " ++ showEnvExp te{-todo-} x ++ "\nfound: " ++ showEnvExp te{-todo-} x' ++ "\nin term: " ++ showEnvExp (EApp2 noSI h a te) b ++ "\n" ++ showExp y
        appf (a, t) (b, x')
            = error_ $ "recheck " ++ msg' ++ "; " ++ msg ++ "\nnot a pi type: " ++ showEnvExp te{-todo-} t ++ "\n\n" ++ showEnvExp e x

        recheck'' msg te a = (b, expType_ "4" te b) where b = recheck_ msg te a

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
  run (SApp _ h a b) = second ((h, b):) $ run a
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

apps a b = foldl SAppV (SGlobal a) b
apps' = foldl $ \a (v, b) -> sApp v a b

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
    Pi h a b -> Pi h <$> f a <*> f b
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

getGEnv exs f = do
    src <- ask
    gets (\ge -> EGlobal src ge mempty) >>= f
inferTerm exs msg tr f t = getGEnv exs $ \env -> let env' = f env in smartTrace exs $ \tr -> 
    fmap (addType . recheck msg env') $ replaceMetas "lam" Lam . fst =<< lift (lift $ inferN (if tr then trace_level exs else 0) env' t)
inferType exs tr t = getGEnv exs $ \env -> fmap (recheck "inferType" env) $ replaceMetas "pi" Pi . fst =<< lift (lift $ inferN (if tr then trace_level exs else 0) (CheckType_ (debugSI "inferType CheckType_") TType env) t)

smartTrace :: MonadError String m => Extensions -> (Bool -> m a) -> m a
smartTrace exs f | trace_level exs >= 2 = f True
smartTrace exs f | trace_level exs == 0 = f False
smartTrace exs f = catchError (f False) $ \err ->
    trace_ (unlines
        [ "---------------------------------"
        , err
        , "try again with trace"
        , "---------------------------------"
        ]) $ f True

addToEnv :: Monad m => Extensions -> SIName -> (Exp, Exp) -> ElabStmtM m ()
addToEnv exs (si, s) (x, t) = do
--    maybe (pure ()) throwError_ $ ambiguityCheck s t
    when (tr_light exs) $ mtrace (s ++ "  ::  " ++ showExp t)
    modify $ Map.alter (Just . maybe (x, t, si) (\(_, _, si) -> defined si)) s
    where
      defined si = error $ unwords ["already defined:", s, "at", showSIRange si]

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
        CstrT _{-todo-} ty f -> freeVars ty <-> freeVars f
        CSplit a b c -> freeVars a <-> (freeVars b <> freeVars c)
        _ -> mempty
      where
        a --> b = \s -> if Set.null $ a `Set.intersection` s then mempty else b
        a <-> b = (a --> b) <> (b --> a)

expType = expType_ "5" (EGlobal (error "expType - no source") initEnv $ error "expType")
addType x = (x, expType x)
addType_ te x = (x, expType_ "6" te x)

downTo n m = map Var [n+m-1, n+m-2..n]
downToS n m = map (SVar (debugSI "20", ".ds")) [n+m-1, n+m-2..n]

defined' = Map.keys

addF exs = gets $ addForalls exs . defined'

tellType te si t = tell $ mkInfoItem (sourceInfo si) $ removeEscs $ showExp {-te  TODO-} t
tellStmtType exs si t = getGEnv exs $ \te -> tellType te si t

handleStmt :: MonadFix m => Extensions -> Stmt -> ElabStmtM m ()
handleStmt exs = \case
  PrecDef{} -> return ()
  Primitive n mf t_ -> do
        t <- inferType exs tr =<< ($ t_) <$> addF exs
        tellStmtType exs (fst n) t
        addToEnv exs n $ flip (,) t $ lamify t $ Fun (FunName (snd n) mf t)
  Let n mf mt ar t_ -> do
        af <- addF exs
        let t__ = maybe id (flip SAnn . af) mt t_
        (x, t) <- inferTerm exs (snd n) tr id $ fromMaybe (SBuiltin "primFix" `SAppV` SLamV t__) $ downS 0 t__
        let
            term = label LabelPM (addLams' ar t 0) $ par ar t x 0

            addLams' [] _ i = Fun (FunName (snd n) mf t) $ downTo 0 i
            addLams' (h: ar) (Pi h' d t) i | h == h' = Lam h d $ addLams' ar t (i+1)
            addLams' ar@(Visible: _) (Pi h@Hidden d t) i = Lam h d $ addLams' ar t (i+1)

            par ar tt (FunN "primFix" [_, f]) i = f `app_` label LabelFix (addLams' ar tt i) (foldl app_ term $ downTo 0 i)
            par ar (Pi Hidden _ tt) (Lam Hidden k z) i = Lam Hidden k $ par (dropHidden ar) tt z (i+1)
              where
                dropHidden (Hidden: ar) = ar
                dropHidden ar = ar
            par ar t x _ = x
        tellStmtType exs (fst n) t
        addToEnv exs n (term, t)
  TypeFamily s ps t -> handleStmt exs $ Primitive s Nothing $ addParamsS ps t
  Data s ps t_ addfa cs -> do
    af <- if addfa then gets $ addForalls exs . (snd s:) . defined' else return id
    vty <- inferType exs tr $ addParamsS ps t_
    tellStmtType exs (fst s) vty
    let
        pnum' = length $ filter ((== Visible) . fst) ps
        inum = arity vty - length ps

        mkConstr j (cn, af -> ct)
            | c == SGlobal s && take pnum' xs == downToS (length . fst . getParamsS $ ct) pnum'
            = do
                cty <- removeHiddenUnit <$> inferType exs tr (addParamsS [(Hidden, x) | (Visible, x) <- ps] ct)
                tellStmtType exs (fst cn) cty
                let     pars = zipWith (\x -> id *** (STyped (debugSI "mkConstr1")) . flip (,) TType . upE x (1+j)) [0..] $ drop (length ps) $ fst $ getParams cty
                        act = length . fst . getParams $ cty
                        acts = map fst . fst . getParams $ cty
                        conn = ConName (snd cn) Nothing j cty
                addToEnv exs cn (Con conn [], cty)
                return ( conn
                       , addParamsS pars
                       $ foldl SAppV (SVar (debugSI "22", ".cs") $ j + length pars) $ drop pnum' xs ++ [apps' (SGlobal cn) (zip acts $ downToS (j+1+length pars) (length ps) ++ downToS 0 (act- length ps))]
                       )
            | otherwise = throwError $ "illegal data definition (parameters are not uniform) " -- ++ show (c, cn, take pnum' xs, act)
            where
                (c, map snd -> xs) = getApps $ snd $ getParamsS ct

        motive = addParamsS (replicate inum (Visible, Wildcard SType)) $
           SPi Visible (apps' (SGlobal s) $ zip (map fst ps) (downToS inum $ length ps) ++ zip (map fst $ fst $ getParamsS t_) (downToS 0 inum)) SType

    mdo
        let tcn = TyConName (snd s) Nothing inum vty (map fst cons) ct
        addToEnv exs s (TyCon tcn [], vty)
        cons <- zipWithM mkConstr [0..] cs
        ct <- inferType exs tr
            ( (\x -> traceD ("type of case-elim before elaboration: " ++ showSExp x) x) $ addParamsS
                ( [(Hidden, x) | (_, x) <- ps]
                ++ (Visible, motive)
                : map ((,) Visible . snd) cons
                ++ replicate inum (Hidden, Wildcard SType)
                ++ [(Visible, apps' (SGlobal s) $ zip (map fst ps) (downToS (inum + length cs + 1) $ length ps) ++ zip (map fst $ fst $ getParamsS t_) (downToS 0 inum))]
                )
            $ foldl SAppV (SVar (debugSI "23", ".ct") $ length cs + inum + 1) $ downToS 1 inum ++ [SVar (debugSI "24", ".24") 0]
            )
        addToEnv exs (fst s, caseName (snd s)) (lamify ct $ CaseFun (CaseFunName (snd s) ct $ length ps), ct)
        let ps' = fst $ getParams vty
            t =   (TType :~> TType)
              :~> addParams ps' (Var (length ps') `app_` TyCon tcn (downTo 0 $ length ps'))
              :~>  TType
              :~> Var 2 `app_` Var 0
              :~> Var 3 `app_` Var 1
        addToEnv exs (fst s, matchName (snd s)) (lamify t $ TyCaseFun (TyCaseFunName (snd s) t), t)

  stmt -> error $ "handleStmt: " ++ show stmt

removeHiddenUnit (Pi Hidden Unit (downE 0 -> Just t)) = removeHiddenUnit t
removeHiddenUnit (Pi h a b) = Pi h a $ removeHiddenUnit b
removeHiddenUnit t = t

---------------------------------------------------------------------------------------
-------------------------------------- parser -----------------------------------------

-- see http://blog.ezyang.com/2014/05/parsec-try-a-or-b-considered-harmful/comment-page-1/#comment-6602
try' s m = try m <?> s

check msg p m = try' msg $ mfilter p m

-------------------------------------------------------------------------------- parser type

type P = ParsecT (IndentStream (CharIndentStream String)) SourcePos (Reader GlobalEnv')


-------------------------------------------------------------------------------- lexing

lexer :: Pa.GenTokenParser (IndentStream (CharIndentStream String)) SourcePos (Reader GlobalEnv')
lexer = makeTokenParser lexeme $ makeIndentLanguageDef style
  where
    style = Pa.LanguageDef
        { Pa.commentStart    = Pa.commentStart    Pa.haskellDef
        , Pa.commentEnd      = Pa.commentEnd      Pa.haskellDef
        , Pa.commentLine     = Pa.commentLine     Pa.haskellDef
        , Pa.nestedComments  = Pa.nestedComments  Pa.haskellDef
        , Pa.identStart      = letter <|> char '_'  -- '_' is included also 
        , Pa.identLetter     = alphaNum <|> oneOf "_'#"
        , Pa.opStart         = Pa.opLetter style
        , Pa.opLetter        = oneOf ":!#$%&*+./<=>?@\\^|-~"
        , Pa.reservedOpNames = Pa.reservedOpNames Pa.haskellDef
        , Pa.reservedNames   = Pa.reservedNames   Pa.haskellDef
        , Pa.caseSensitive   = Pa.caseSensitive   Pa.haskellDef
        }

lexeme p = p <* (getPosition >>= setState >> whiteSpace)

parens          = Pa.parens lexer
braces          = Pa.braces lexer
brackets        = Pa.brackets lexer
commaSep        = Pa.commaSep lexer
commaSep1       = Pa.commaSep1 lexer
dot             = Pa.dot lexer
comma           = Pa.comma lexer
colon           = Pa.colon lexer
natural         = Pa.natural lexer
integer         = Pa.integer lexer
float           = Pa.float lexer
charLiteral     = Pa.charLiteral lexer
stringLiteral   = Pa.stringLiteral lexer
whiteSpace      = Pa.whiteSpace lexer
operator        = Pa.operator lexer
reserved        = Pa.reserved lexer
reservedOp      = Pa.reservedOp lexer
identifier      = Pa.identifier lexer

appRange :: P (SI -> a) -> P a
appRange p = (\p1 a p2 -> a (Range (p1,p2))) <$> getPosition <*> p <*> getState

withRange :: (SI -> a -> b) -> P a -> P b
withRange f p = appRange $ flip f <$> p

infix 9 `withRange`

-------------------------------------------------------------------------------- namespace handling

data Level
  = TypeLevel
  | ExpLevel
  deriving (Eq, Show)

levelElim typeLevel expLevel = \case
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
 
tickIdent ns = tick' ns <$> identifier

-------------------------------------------------------------------------------- identifiers

--upperCase, lowerCase, symbols, colonSymbols :: P String
upperCase NonTypeNamespace = mzero -- todo
upperCase ns    = (if caseSensitiveNS ns then check "uppercase ident" (isUpper . head') else id) $ tickIdent ns
lowerCase ns    = (if caseSensitiveNS ns then check "lowercase ident" (isLower . head') else id) identifier <|> try (('_':) <$ char '_' <*> identifier)
symbols         = check "symbols" ((/=':') . head) operator
colonSymbols    = "Cons" <$ reservedOp ":" <|> check "symbols" ((==':') . head) operator

var ns          = lowerCase ns
patVar ns       = lowerCase ns <|> "" <$ reserved "_"
qIdent ns       = {-qualified_ todo-} (var ns <|> upperCase ns)
conOperator     = colonSymbols
varId ns        = var ns <|> parens operatorT
backquotedIdent = try' "backquoted" $ lexeme $ char '`' *> ((:) <$> satisfy isAlpha <*> many (satisfy isAlphaNum)) <* char '`'
operatorT       = symbols
              <|> conOperator
              <|> backquotedIdent
moduleName      = {-qualified_ todo-} upperCase (Namespace ExpLevel True)

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

head' ('\'': c: _) = c
head' (c: _) = c

-------------------------------------------------------------------------------- fixity declarations

fixityDef :: P [Stmt]
fixityDef = do
  dir <-    Infix  <$ reserved "infix"
        <|> InfixL <$ reserved "infixl"
        <|> InfixR <$ reserved "infixr"
  localIndentation Gt $ do
    i <- fromIntegral <$> natural
    ns <- commaSep1 (withSI operatorT)
    return $ PrecDef <$> ns <*> pure (dir, i)

-------------------------------------------------------------------------------- export

data Export = ExportModule SName | ExportId SName

parseExport :: Namespace -> P Export
parseExport ns =
        ExportModule <$ reserved "module" <*> moduleName
    <|> ExportId <$> varId ns

-------------------------------------------------------------------------------- import

data ImportItems
    = ImportAllBut [SName]
    | ImportJust [SName]

importlist ns = parens (commaSep (varId ns <|> upperCase ns))

-------------------------------------------------------------------------------- extensions

type Extensions = [Extension]

data Extension
    = NoImplicitPrelude
    | NoTypeNamespace
    | NoConstructorNamespace
    | TraceTypeCheck
    deriving (Enum, Eq, Ord, Show)

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

-------------------------------------------------------------------------------- modules

data ModuleR
  = Module
  { extensions    :: Extensions
  , moduleImports :: [(SName, ImportItems)]
  , moduleExports :: Maybe [Export]
  , definitions   :: GlobalEnv' -> Either String [Stmt]
  , sourceCode    :: String
  }

parseLC :: MonadError ErrorMsg m => FilePath -> String -> m ModuleR
parseLC f str = either (throwError . ErrorMsg . show) return . flip runReader (error "globalenv used") . runParserT p (newPos "" 0 0) f . mkIndentStream 0 infIndentation True Ge . mkCharIndentStream $ str
  where
    p = do
        getPosition >>= setState
        setPosition =<< flip setSourceName f <$> getPosition
        exts <- concat <$> many parseExtensions
        let ns = if NoTypeNamespace `elem` exts
                    then NonTypeNamespace
                    else Namespace ExpLevel (not $ NoConstructorNamespace `elem` exts)
        whiteSpace
        header <- optionMaybe $ do
            modn <- reserved "module" *> moduleName
            exps <- optionMaybe (parens $ commaSep $ parseExport ns)
            reserved "where"
            return (modn, exps)
        let mkIDef _ n i h _ = (n, f i h)
              where
                f Nothing Nothing = ImportAllBut []
                f (Just h) Nothing = ImportAllBut h
                f Nothing (Just i) = ImportJust i
        idefs <- many $
              mkIDef <$> (reserved "import" *> (optionMaybe $ try $ reserved "qualified"))
                     <*> moduleName
                     <*> (optionMaybe $ try $ reserved "hiding" *> importlist ns)
                     <*> (optionMaybe $ try $ importlist ns)
                     <*> (optionMaybe $ try $ reserved "as" *> moduleName)
        st <- getParserState

        let defs ge = (show +++ id) . flip runReader ge . runParserT p (newPos "" 0 0) f . mkIndentStream 0 infIndentation True Ge . mkCharIndentStream $ ""
              where
                p = do
                    setParserState st
                    parseDefs SLabelEnd ns <* eof
        return $ Module
          { extensions = exts
          , moduleImports = if NoImplicitPrelude `elem` exts
                then idefs
                else ("Prelude", ImportAllBut []): idefs
          , moduleExports = join $ snd <$> header
          , definitions   = defs
          , sourceCode    = str
          }

--------------------------------------------------------------------------------

parseType ns mb = maybe id option mb (reservedOp "::" *> parseTTerm ns PrecLam)
typedIds ns mb = (,) <$> commaSep1 (withSI (varId ns <|> patVar ns <|> upperCase ns))
                     <*> localIndentation Gt {-TODO-} (parseType ns mb)

telescope ns mb = (DBNamesC *** id) <$> telescopeSI ns mb

telescopeSI :: Namespace -> Maybe SExp -> P ([SIName], [(Visibility, SExp)])    -- todo: refactor to [(SIName, (Visibility, SExp))]
telescopeSI ns mb = go []
  where
    go vs = option ([], []) $ do
        (x, vt) <-
          (     reservedOp "@" *> (maybe empty (\x -> flip (,) (Hidden, x) <$> withSI (patVar ns)) mb <|> parens (typedId Hidden))
            <|> try (parens $ typedId Visible)
            <|> maybe ((,) (debugSI "s13", "") . (,) Visible . dbf' (DBNamesC vs) <$> parseTerm ns PrecAtom)
                      (\x -> flip (,) (Visible, x) <$> withSI (patVar ns))
                      mb
          )
        ((++[x]) *** (vt:)) <$> go (x: vs)
      where
        typedId v = (\f s -> (f,(v,s)))
                      <$> withSI (patVar ns)
                      <*> localIndentation Gt {-TODO-} (dbf' (DBNamesC vs) <$> parseType ns mb)

telescopeDataFields :: Namespace -> P ([SIName], [(Visibility, SExp)]) 
telescopeDataFields ns = {-telescopeSI ns Nothing-} go []
  where
    go vs = option ([], []) $ do
        (x, vt) <- do name <- withSI $ var (expNS ns)
                      term <- parseType ns Nothing
                      return (name, (Visible, dbf' (DBNamesC vs) term))
        ((++[x]) *** (vt:)) <$> (comma *> go (x: vs) <|> pure ([], []))

parseClause ns = do
    (fe, p) <- pattern' ns
    localIndentation Gt $ do
        x <- reservedOp "->" *> parseETerm ns PrecLam
        f <- parseWhereBlock ns
        return (p, dbf' fe $ f x)

patternAtom ns = patternAtom' ns <&> \p -> (getPVars p, p)
patternAtom' ns =
     flip ViewPat eqPP . SAppV (SBuiltin "primCompareFloat") <$> (sLit . LFloat <$> try float)
 <|> mkNatPat ns <$> (withSI natural)
 <|> flip PCon [] <$> (withSI $ upperCase ns)
 <|> char '\'' *> patternAtom' (switchNS ns)
 <|> PVar <$> withSI (patVar ns)
 <|> pConSI . mkListPat ns <$> brackets (patlist ns <|> pure [])
 <|> pConSI . mkTupPat ns <$> parens (patlist ns)
 where
   mkNatPat (Namespace ExpLevel _) (si, n) = flip ViewPat eqPP . SAppV (SBuiltin "primCompareInt") . sLit . LInt $ fromIntegral n
   mkNatPat _ (si, n) = toNatP si n
   pConSI (PCon (_, n) ps) = PCon (sourceInfo ps, n) ps
   pConSI p = p

eqPP = ParPat [PCon (debugSI "eqPP", "EQ") []]
truePP = ParPat [PCon (debugSI "truePP", "True") []]

patlist ns = fmap snd $ commaSepUnfold (\vs -> (\(vs, p) t -> (vs, patType (dbPat vs p) t)) <$> pattern' ns <*> (dbf' vs <$> parseType ns (Just $ Wildcard SType))) mempty

mkListPat ns [p] | namespaceLevel ns == Just TypeLevel = PCon (debugSI "mkListPat4", "'List") [ParPat [p]]
mkListPat ns (p: ps) = PCon (debugSI "mkListPat2", "Cons") $ map (ParPat . (:[])) [p, mkListPat ns ps]
mkListPat _ [] = PCon (debugSI "mkListPat3", "Nil") []

mkTupPat :: Namespace -> [Pat] -> Pat
mkTupPat _ [x] = x
mkTupPat ns ps = PCon (debugSI "", tick' ns $ "Tuple" ++ show (length ps)) (ParPat . (:[]) <$> ps)

pattern' ns = pattern'_ ns <&> \p -> (getPVars p, p)
pattern'_ ns =
     PCon <$> (withSI $ upperCase ns) <*> patterns' ns
 <|> PCon <$> try (withSI (char '\'' *> upperCase (switchNS ns))) <*> patterns' ns
 <|> (patternAtom ns >>= \(vs, p) -> option p (((\p' -> PCon (debugSI "pattern'","Cons") (ParPat . (:[]) <$> [p, p']))) <$ reservedOp ":" <*> (dbPat vs <$> pattern'_ ns)))

dbPat v = mapP (dbf' v)

pCon i (vs, x) = (vs, PCon i x)

patterns ns = patterns' ns <&> \p -> (foldMap getPPVars p, p)
patterns' ns = fmap snd $
     do patternAtom ns >>= \(vs, p) -> patterns ns >>= \(vs', ps) -> pure (vs' <> vs, ParPat [p]: map (mapPP $ dbf' vs) ps)
 <|> pure (mempty, [])

patType p (Wildcard SType) = p
patType p t = PatType (ParPat [p]) t

-- todo: eliminate
commaSepUnfold :: (t -> P (t, a)) -> t -> P (t, [a])
commaSepUnfold p vs = commaSepUnfold1 p vs <|> pure (vs, [])
  where
    commaSepUnfold1 :: (t -> P (t, a)) -> t -> P (t, [a])
    commaSepUnfold1 p vs0 = do
      (vs1, x) <- p vs0
      (second (x:) <$ comma <*> commaSepUnfold1 p vs1) <|> pure (vs1, [x])

telescope' ns = go mempty where
    go vs = option (vs, []) $ do
        (vs', vt) <-
                reservedOp "@" *> (second (f Hidden . mapP (dbf' vs)) <$> patternAtom ns)
            <|> second (f Visible . mapP (dbf' vs)) <$> patternAtom ns
        (id *** (vt:)) <$> go (vs' <> vs)
      where
        f h (PatType (ParPat [p]) t) = ((h, t), p)
        f h p = ((h, Wildcard SType), p)

parseDefs lend ns = (asks $ \ge -> compileFunAlts' lend ge . concat) <*> many (parseDef ns)

compileFunAlts' lend ge ds = concatMap (compileFunAlts False lend lend ge ds) $ groupBy h ds where
    h (FunAlt n _ _ _) (FunAlt m _ _ _) = m == n
    h _ _ = False

compileFunAlts :: Bool -> (SExp -> SExp) -> (SExp -> SExp) -> GlobalEnv' -> [Stmt] -> [Stmt] -> [Stmt]
compileFunAlts par ulend lend ge ds = \case
    [Instance{}] -> []
    [Class n ps ms] -> compileFunAlts' SLabelEnd ge $
            [ TypeAnn n $ foldr (SPi Visible) SType ps ]
         ++ [ FunAlt n (map noTA ps) Nothing $ foldr ST2 (SBuiltin "'Unit") cstrs | Instance n' ps cstrs _ <- ds, n == n' ]
         ++ [ FunAlt n (map noTA $ replicate (length ps) (PVar (debugSI "compileFunAlts1", "generated_name0"))) Nothing $ SBuiltin "'Empty" `SAppV` sLit (LString $ "no instance of " ++ snd n ++ " on ???")]
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
    [TypeAnn n t] -> [Primitive n Nothing t | all (/= snd n) [n' | FunAlt (_, n') _ _ _ <- ds]]
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

parseDef :: Namespace -> P [Stmt]
parseDef ns =
     do reserved "data"
        localIndentation Gt $ do
            x <- withSI $ upperCase (typeNS ns)
            (npsd, ts) <- telescope (typeNS ns) (Just SType)
            t <- dbf' npsd <$> parseType (typeNS ns) (Just SType)
            let mkConTy mk (nps', ts') =
                    ( if mk then Just nps' else Nothing
                    , foldr (uncurry SPi) (foldl SAppV (SGlobal x) $ downToS (length ts') $ length ts) ts')
            (af, cs) <-
                 do (,) True <$ reserved "where" <*> localIndentation Ge (localAbsoluteIndentation $ many $
                        (id *** (,) Nothing . dbf' npsd) <$> typedIds ns Nothing)
             <|> do (,) False <$ reservedOp "=" <*>
                      sepBy1 ((,) <$> (pure <$> withSI (upperCase ns))
                                  <*> (    braces (mkConTy True . (\(x, y) -> (x, zipWith (\i (v, e) -> (v, dbf_ i npsd e)) [0..] y)) <$> telescopeDataFields (typeNS ns))
                                       <|> (mkConTy False . (\(x, y) -> (x, zipWith (\i (v, e) -> (v, dbf_ i npsd e)) [0..] y)) <$> telescopeSI (typeNS ns) Nothing)) )
                                      (reservedOp "|")
             <|> pure (True, [])
            ge <- ask
            return $ mkData ge x ts t af $ concatMap (\(vs, t) -> (,) <$> vs <*> pure t) $ cs
 <|> do reserved "class"
        localIndentation Gt $ do
            x <- withSI $ upperCase (typeNS ns)
            (nps, ts) <- telescope (typeNS ns) (Just SType)
            cs <-
                 do reserved "where" *> localIndentation Ge (localAbsoluteIndentation $ many $ typedIds ns Nothing)
             <|> pure []
            return $ pure $ Class x (map snd ts) (concatMap (\(vs, t) -> (,) <$> vs <*> pure (dbf' nps t)) cs)
 <|> do reserved "instance"
        let ns' = typeNS ns
        localIndentation Gt $ do
            constraints <- option [] $ try $ getTTuple' <$> parseTerm ns' PrecEq <* reservedOp "=>"
            x <- withSI $ upperCase ns'
            (nps, args) <- telescope' ns'
            cs <- option [] $ reserved "where" *> localIndentation Ge (localAbsoluteIndentation $ some $
                    dbFunAlt nps <$> funAltDef (varId ns) ns)
             <|> pure []
            ge <- ask
            return $ pure $ Instance x ({-todo-}map snd args) (dbff (diffDBNames nps ++ [snd x]) <$> constraints) $ compileFunAlts' id{-TODO-} ge cs
 <|> do try (reserved "type" >> reserved "family")
        let ns' = typeNS ns
        localIndentation Gt $ do
            x <- withSI $ upperCase ns'
            (nps, ts) <- telescope ns' (Just SType)
            t <- dbf' nps <$> parseType ns' (Just SType)
            option {-open type family-}[TypeFamily x ts t] $ do
                cs <- reserved "where" *> localIndentation Ge (localAbsoluteIndentation $ many $
                    funAltDef (upperCase ns' >>= \x' -> guard (snd x == x') >> return x') ns')
                ge <- ask
                -- closed type family desugared here
                return $ compileFunAlts False id SLabelEnd ge [TypeAnn x $ addParamsS ts t] cs
 <|> do reserved "type"
        let ns' = typeNS ns
        localIndentation Gt $ do
            x <- withSI $ upperCase ns'
            (nps, ts) <- telescopeSI ns' (Just (Wildcard SType))
            reservedOp "="
            rhs <- dbf' (DBNamesC nps) <$> parseTerm ns' PrecLam
            ge <- ask
            return $ compileFunAlts False id SLabelEnd ge
                [{-TypeAnn x $ addParamsS ts $ SType-}{-todo-}]
                [FunAlt x (reverse $ zip (reverse ts) $ map PVar nps) Nothing rhs]
 <|> do try (reserved "type" >> reserved "instance")
        let ns' = typeNS ns
        pure <$> localIndentation Gt (funAltDef (upperCase ns') ns')
 <|> do (vs, t) <- try $ typedIds ns Nothing
        return $ TypeAnn <$> vs <*> pure t
 <|> fixityDef
 <|> pure <$> funAltDef (varId ns) ns
 <|> pure . uncurry ValueDef <$> valueDef ns

funAltDef parseName ns = do   -- todo: use ns to determine parseName
    (n, (fee, tss)) <-
        do try' "operator definition" $ do
            (e', a1) <- patternAtom ns
            localIndentation Gt $ do
                n <- withSI operatorT
                (e'', a2) <- patternAtom ns
                lookAhead $ reservedOp "=" <|> reservedOp "|"
                return (n, (e'' <> e', (,) (Visible, Wildcard SType) <$> [a1, mapP (dbf' e') a2]))
      <|> do try $ do
                n <- withSI parseName
                localIndentation Gt $ (,) n <$> telescope' ns <* (lookAhead $ reservedOp "=" <|> reservedOp "|")
    let fe = dbf' $ fee <> addDBName n
        ts = map (id *** upP 0 1{-todo: replace n with Var 0-}) tss
    localIndentation Gt $ do
        gu <- option Nothing $ do
            reservedOp "|"
            Just <$> parseTerm ns PrecOp
        reservedOp "="
        rhs <- parseTerm ns PrecLam
        f <- parseWhereBlock ns
        return $ FunAlt n ts (fe <$> gu) $ fe $ f rhs

dbFunAlt v (FunAlt n ts gu e) = FunAlt n (map (id *** mapP (dbf' v)) ts) (dbf' v <$> gu) $ dbf' v e

mkData ge x ts t af cs = [Data x ts t af $ (id *** snd) <$> cs] ++ concatMap mkProj cs
  where
    mkProj (cn, (Just fs, _))
      = [ Let fn Nothing Nothing [Visible]
        $ upS{-non-rec-} $ patLam SLabelEnd ge (PCon cn $ replicate (length fs) $ ParPat [PVar (fst cn, "generated_name1")]) $ SVar (fst cn, ".proj") i
        | (i, fn) <- zip [0..] fs]
    mkProj _ = []

parseWhereBlock ns = option id $ do
    reserved "where"
    dcls <- localIndentation Ge (localAbsoluteIndentation $ parseDefs id ns)
    ge <- ask
    return $ mkLets ge dcls

newtype DBNames = DBNamesC [SIName]  -- De Bruijn variable names
instance Show DBNames where show (DBNamesC x) = show $ map snd x
instance Monoid DBNames where mempty = DBNamesC []
                              mappend (DBNamesC a) (DBNamesC b) = DBNamesC (a ++ b)

addDBName n = DBNamesC [n]
diffDBNames (DBNamesC xs) = map snd xs

sVar = withRange $ \si x -> SGlobal (si, x)

valueDef :: Namespace -> P (([SIName], Pat), SExp)
valueDef ns = do
    (DBNamesC e', p) <- try $ pattern' ns <* reservedOp "="
    localIndentation Gt $ do
        ex <- parseETerm ns PrecLam
        return ((e', p), ex)

parseTTerm ns = parseTerm $ typeNS ns
parseETerm ns = parseTerm $ expNS ns

parseTerm :: Namespace -> Prec -> P SExp
parseTerm ns prec = withRange setSI $ case prec of
    PrecLam ->
         mkIf <$ reserved "if" <*> parseTerm ns PrecLam <* reserved "then" <*> parseTerm ns PrecLam <* reserved "else" <*> parseTerm ns PrecLam
     <|> do (tok, ns) <- (SPi . const Hidden <$ reservedOp "." <|> SPi . const Visible <$ reservedOp "->", typeNS ns) <$ reserved "forall"
            (fe, ts) <- telescope ns (Just $ Wildcard SType)
            f <- tok
            t' <- dbf' fe <$> parseTerm ns PrecLam
            return $ foldr (uncurry f) t' ts
     <|> do
            reservedOp "\\"
            let ns' = expNS ns
            (fe, ts) <- telescope' ns'
            reservedOp "->"
            t' <- dbf' fe <$> parseTerm ns' PrecLam
            ge <- ask
            return $ foldr (uncurry (patLam_ id ge)) t' ts
     <|> do (asks compileCase) <* reserved "case" <*> parseETerm ns PrecLam
                               <* reserved "of" <*> localIndentation Ge (localAbsoluteIndentation $ some $ parseClause ns)
     <|> do (asks $ \ge -> compileGuardTree id id ge . Alts) <*> parseSomeGuards ns (const True)
     <|> do t <- parseTerm ns PrecEq
            option t $ mkPi <$> (Visible <$ reservedOp "->" <|> Hidden <$ reservedOp "=>") <*> pure t <*> parseTTerm ns PrecLam
    PrecEq -> parseTerm ns PrecAnn >>= \t -> option t $ SCstr t <$ reservedOp "~" <*> parseTTerm ns PrecAnn
    PrecAnn -> parseTerm ns PrecOp >>= \t -> option t $ SAnn t <$> parseType ns Nothing
    PrecOp -> asks calculatePrecs <*> p' where
        p' = ((\si (t, xs) -> (mkNat ns 0, (SBuiltin "-", t): xs)) `withRange` (reservedOp "-" *> p_))
             <|> p_
        p_ = (,) <$> parseTerm ns PrecApp <*> (option [] $ sVar operatorT >>= p)
        p op = do (exp, op') <- try ((,) <$> parseTerm ns PrecApp <*> sVar operatorT)
                  ((op, exp):) <$> p op'
           <|> pure . (,) op <$> parseTerm ns PrecLam
    PrecApp -> 
        try {- TODO: adjust try for better error messages e.g. don't use braces -}
          (apps' <$> sVar (upperCase ns) <*> braces (commaSep $ lowerCase ns *> reservedOp "=" *> ((,) Visible <$> parseTerm ns PrecLam))) <|>
        (apps' <$> parseTerm ns PrecSwiz <*> many
                (   (,) Visible <$> parseTerm ns PrecSwiz
                <|> (,) Hidden <$ reservedOp "@" <*> parseTTerm ns PrecSwiz))
    PrecSwiz -> do
        t <- parseTerm ns PrecProj
        try (mkSwizzling t `withRange` (lexeme $ char '%' *> manyNM 1 4 (satisfy (`elem` ("xyzwrgba" :: [Char]))))) <|> pure t
    PrecProj -> do
        t <- parseTerm ns PrecAtom
        try (mkProjection t <$ char '.' <*> (sepBy1 (sLit . LString <$> lowerCase ns) (char '.'))) <|> pure t
    PrecAtom ->
         sLit . LChar <$> try charLiteral
     <|> sLit . LString  <$> stringLiteral
     <|> sLit . LFloat   <$> try float
     <|> sLit . LInt . fromIntegral <$ char '#' <*> natural
     <|> mkNat ns <$> natural
     <|> Wildcard (Wildcard SType) <$ reserved "_"
     <|> char '\'' *> parseTerm (switchNS ns) PrecAtom
     <|> sVar (try (varId ns) <|> upperCase ns)
     <|> mkDotDot <$> try (reservedOp "[" *> parseTerm ns PrecLam <* reservedOp ".." ) <*> parseTerm ns PrecLam <* reservedOp "]"
     <|> listCompr ns
     <|> mkList ns <$> brackets (commaSep $ parseTerm ns PrecLam)
     <|> mkLeftSection <$> try{-todo: better try-} (parens $ (,) <$> withSI (guardM (/= "-") operatorT) <*> parseTerm ns PrecLam)
     <|> mkRightSection <$> try{-todo: better try!-} (parens $ (,) <$> parseTerm ns PrecApp <*> withSI operatorT)
     <|> mkTuple ns <$> parens (commaSep $ parseTerm ns PrecLam)
     <|> mkRecord <$> braces (commaSep $ ((,) <$> lowerCase ns <* colon <*> parseTerm ns PrecLam))
     <|> do reserved "let"
            dcls <- localIndentation Ge (localAbsoluteIndentation $ parseDefs id ns)
            ge <- ask
            mkLets ge dcls <$ reserved "in" <*> parseTerm ns PrecLam

guardM p m = m >>= \x -> if p x then return x else fail "guardM"

mkLeftSection (op, e) = SLam Visible (Wildcard SType) $ SGlobal op `SAppV` SVar (noSI, ".ls") 0 `SAppV` upS e
mkRightSection (e, op) = SLam Visible (Wildcard SType) $ SGlobal op `SAppV` upS e `SAppV` SVar (noSI, ".rs") 0

mkSwizzling term si = swizzcall
  where
    sc c = SGlobal (si,'S':c:[])
    swizzcall [x] = SBuiltin "swizzscalar" `SAppV` term `SAppV` (sc . synonym) x
    swizzcall xs  = SBuiltin "swizzvector" `SAppV` term `SAppV` swizzparam xs
    swizzparam xs  = foldl (\exp s -> exp `SAppV` s) (vec xs) $ map (sc . synonym) xs
    vec xs = SGlobal $ (,) si $ case length xs of
        0 -> error "impossible: swizzling parsing returned empty pattern"
        1 -> error "impossible: swizzling went to vector for one scalar"
        n -> "V" ++ show n
    synonym 'r' = 'x'
    synonym 'g' = 'y'
    synonym 'b' = 'z'
    synonym 'a' = 'w'
    synonym c   = c

mkProjection term = foldl (\exp field -> SBuiltin "project" `SAppV` field `SAppV` exp) term

-- Creates: RecordCons @[("x", _), ("y", _), ("z", _)] (1.0, (2.0, (3.0, ())))
mkRecord xs = SBuiltin "RecordCons" `SAppH` names `SAppV` values
  where
    (names, values) = mkNames *** mkValues $ unzip xs

    mkNameTuple v = SBuiltin "Tuple2" `SAppV` (sLit $ LString v) `SAppV` Wildcard SType
    mkNames = foldr (\n ns -> SBuiltin "Cons" `SAppV` (mkNameTuple n) `SAppV` ns)
                    (SBuiltin "Nil")

    mkValues = foldr (\x xs -> SBuiltin "Tuple2" `SAppV` x `SAppV` xs)
                     (SBuiltin "Tuple0")

mkTuple _ [x] = x
mkTuple (Namespace level _) xs = foldl SAppV (SBuiltin (tuple ++ show (length xs))) xs
  where tuple = levelElim "'Tuple" "Tuple" level
mkTuple _ xs = error "mkTuple"

mkList (Namespace TypeLevel _) [x] = SBuiltin "'List" `SAppV` x
mkList (Namespace ExpLevel  _) xs = foldr (\x l -> SBuiltin "Cons" `SAppV` x `SAppV` l) (SBuiltin "Nil") xs
mkList _ xs = error "mkList"

mkNat (Namespace ExpLevel _) n = SBuiltin "fromInt" `SAppV` sLit (LInt $ fromIntegral n)
mkNat _ n = toNat n

withSI = withRange (,)

mkIf b t f = SBuiltin "primIfThenElse" `SAppV` b `SAppV` t `SAppV` f

mkDotDot e f = SBuiltin "fromTo" `SAppV` e `SAppV` f

-- n, m >= 1, n < m
manyNM n m p = do
  xs <- many1 p
  let lxs = length xs
  unless (n <= lxs && lxs <= m) . fail $ unwords ["manyNM", show n, show m, "found", show lxs, "occurences."]
  return xs

-------------------------------------------------------------------------------- list comprehensions

generator, letdecl, boolExpression :: Namespace -> DBNames -> P (DBNames, SExp -> SExp)
generator ns dbs = do
    (dbs', pat) <- try $ pattern' ns <* reservedOp "<-"
    exp <- dbf' dbs <$> parseTerm ns PrecLam
    ge <- ask
    return $ (,) (dbs' <> dbs) $ \e -> application
        [ SBuiltin "concatMap"
        , SLamV $ compileGuardTree id id ge $ Alts
            [ compilePatts [(mapP (dbf' dbs) pat, 0)] Nothing $ {-upS $ -} e
            , GuardLeaf $ SBuiltin "Nil"
            ]
        , exp
        ]

letdecl ns dbs = ask >>= \ge -> reserved "let" *> ((\((dbs', p), e) -> (dbs, \exp -> mkLets ge [ValueDef (dbs', mapP (dbf' dbs) p) $ dbf' dbs e] exp)) <$> valueDef ns)

boolExpression ns dbs = do
    pred <- dbf' dbs <$> parseTerm ns PrecLam
    return (dbs, \e -> application [SBuiltin "primIfThenElse", pred, e, SBuiltin "Nil"])

application = foldl1 SAppV

listCompr :: Namespace -> P SExp
listCompr ns = (\e (dbs', fs) -> foldr ($) (dbff (diffDBNames dbs') e) fs)
 <$> try' "List comprehension" ((SBuiltin "singleton" `SAppV`) <$ reservedOp "[" <*> parseTerm ns PrecLam <* reservedOp "|")
 <*> commaSepUnfold (liftA2 (<|>) (generator ns) $ liftA2 (<|>) (letdecl ns) (boolExpression ns)) mempty <* reservedOp "]"

-- todo: make it more efficient
diffDBNames' xs ys = take (length xs - length ys) xs

dbf' = dbf_ 0
dbf_ j (DBNamesC xs) e = foldl (\e (i, (si, n)) -> substSG n (\si -> SVar (si, n) i) e) e $ zip [j..] xs

dbff :: [String] -> SExp -> SExp
dbff [] e = e
dbff (n: ns) e = substSG0 n $ dbff ns e

--------------------------------------------------------------------------------

--calculatePrecs :: GlobalEnv' -> DBNames -> (SExp, [(SName, SExp)]) -> SExp
calculatePrecs _ (e, []) = e
calculatePrecs dcls (e, xs) = calcPrec (\op x y -> op `SAppV` x `SAppV` y) (getFixity dcls . gf) e xs
  where
    gf (SGlobal (si, n)) = n
    gf (SVar (_, n) i) = n

getFixity :: GlobalEnv' -> SName -> Fixity
getFixity (fm, _) n = fromMaybe (InfixL, 9) $ Map.lookup n fm

mkGlobalEnv' :: [Stmt] -> GlobalEnv'
mkGlobalEnv' ss =
    ( Map.fromList [(s, f) | PrecDef (_, s) f <- ss]
    , Map.fromList $
        [(cn, Left ((t, pars ty), (snd *** pars) <$> cs)) | Data (_, t) ps ty _ cs <- ss, ((_, cn), ct) <- cs]
     ++ [(t, Right $ pars $ addParamsS ps ty) | Data (_, t) ps ty _ cs <- ss]
    )
  where
    pars ty = length $ filter ((== Visible) . fst) $ fst $ getParamsS ty -- todo

extractGlobalEnv' :: GlobalEnv -> GlobalEnv'
extractGlobalEnv' ge =
    ( Map.fromList
        [ (n, f) | (n, (d, _, si)) <- Map.toList ge, f <- maybeToList $ case d of
            Con (ConName _ f _ _) [] -> f
            TyCon (TyConName _ f _ _ _ _) [] -> f
            (snd . getLams -> UL (snd . getLams -> Fun (FunName _ f _) _)) -> f
            Fun (FunName _ f _) [] -> f
            _ -> Nothing
        ]
    , Map.fromList $
        [ (n, Left ((t, inum), map f cons))
        | (n, (Con cn [], _, si)) <- Map.toList ge, let TyConName t _ inum _ cons _ = conTypeName cn
        ] ++
        [ (n, Right $ pars t)
        | (n, (TyCon (TyConName _ f _ t _ _) [], _, _)) <- Map.toList ge
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
getTTuple (SGlobal (si, s@(splitAt 6 -> ("'Tuple", reads -> [(n, "")])))) = Just (n :: Int, [])
getTTuple _ = Nothing

mkLets :: GlobalEnv' -> [Stmt]{-where block-} -> SExp{-main expression-} -> SExp{-big let with lambdas; replaces global names with de bruijn indices-}
mkLets _ [] e = e
mkLets ge (Let n _ mt _ (downS 0 -> Just x): ds) e
    = SLet (maybe id (flip SAnn . addForalls {-todo-}[] []) mt x) (substSG0 (snd n) $ mkLets ge ds e)
mkLets ge (ValueDef (ns, p) x: ds) e = patLam id ge p (dbff (map snd ns) $ mkLets ge ds e) `SAppV` x    -- (p = e; f) -->  (\p -> f) e
mkLets _ (x: ds) e = error $ "mkLets: " ++ show x

patLam f ge = patLam_ f ge (Visible, Wildcard SType)

patLam_ :: (SExp -> SExp) -> GlobalEnv' -> (Visibility, SExp) -> Pat -> SExp -> SExp
patLam_ f ge (v, t) p e = SLam v t $ compileGuardTree f f ge $ compilePatts [(p, 0)] Nothing e

parseSomeGuards ns f = do
    pos <- sourceColumn <$> getPosition <* reservedOp "|"
    guard $ f pos
    (e', f) <-
         do (e', PCon (_, p) vs) <- try $ pattern' ns <* reservedOp "<-"
            x <- parseETerm ns PrecEq
            return (e', \gs' gs -> GuardNode x p vs (Alts gs'): gs)
     <|> do x <- parseETerm ns PrecEq
            return (mempty, \gs' gs -> [GuardNode x "True" [] $ Alts gs', GuardNode x "False" [] $ Alts gs])
    f <$> ((map (dbfGT e') <$> parseSomeGuards ns (> pos)) <|> (:[]) . GuardLeaf <$ reservedOp "->" <*> (dbf' e' <$> parseETerm ns PrecLam))
      <*> (parseSomeGuards ns (== pos) <|> pure [])

toNat 0 = SBuiltin "Zero"
toNat n | n > 0 = SAppV (SBuiltin "Succ") $ toNat (n-1)

toNatP si = run where
  run 0         = PCon (si, "Zero") []
  run n | n > 0 = PCon (si, "Succ") [ParPat [run $ n-1]]

addForalls :: Extensions -> [SName] -> SExp -> SExp
addForalls exs defined x = foldl f x [v | v@(vh:_) <- reverse $ freeS x, v `notElem'` defined, isLower vh || NoConstructorNamespace `elem` exs]
  where
    f e v = SPi Hidden (Wildcard SType) $ substSG0 v e

defined defs = ("'Type":) $ flip foldMap defs $ \case
    TypeAnn (_, x) _ -> [x]
    Let (_, x) _ _ _ _  -> [x]
    Data (_, x) _ _ _ cs -> x: map (snd . fst) cs
    Class (_, x) _ cs    -> x: map (snd . fst) cs
    TypeFamily (_, x) _ _ -> [x]
    x -> error $ unwords ["defined: Impossible", show x, "cann't be here"]
--------------------------------------------------------------------------------

class SourceInfo si where
    sourceInfo :: si -> SI

instance SourceInfo SI where
    sourceInfo = id

instance SourceInfo si => SourceInfo [si] where
    sourceInfo = mconcat . map sourceInfo

instance SourceInfo ParPat where
    sourceInfo (ParPat ps) = sourceInfo ps

instance SourceInfo Pat where
    sourceInfo = \case
        PVar (si,_) -> si
        PCon (si,_) ps -> si <> sourceInfo ps
        ViewPat e ps -> sourceInfo e  <> sourceInfo ps
        PatType ps e -> sourceInfo ps <> sourceInfo e


instance SourceInfo SExp where
    sourceInfo = \case
        SGlobal (si, _)        -> si
        SBind si _ (si', _) e1 e2 -> si
        SApp si _ e1 e2        -> si
        SLet e1 e2             -> sourceInfo e1 <> sourceInfo e2
        SVar (si, _) _         -> si
        STyped si _            -> si

class SetSourceInfo a where
    setSI :: SI -> a -> a

instance SetSourceInfo SExp where
    setSI si = \case
        SBind _ a b c d -> SBind si a b c d
        SApp _ a b c -> SApp si a b c
        SLet a b -> SLet a b
        SVar (_, n) i -> SVar (si, n) i
        STyped _ t -> STyped si t
        SGlobal (_, n) -> SGlobal (si, n)

--------------------------------------------------------------------------------

-- parallel patterns like  v@(f -> [])@(Just x)
newtype ParPat = ParPat [Pat]
  deriving Show

data Pat
    = PVar SIName -- Int
    | PCon SIName [ParPat]
    | ViewPat SExp ParPat
    | PatType ParPat SExp
  deriving Show

data GuardTree
    = GuardNode SExp SName [ParPat] GuardTree -- _ <- _
    | Alts [GuardTree]          --      _ | _
    | GuardLeaf SExp            --     _ -> e
  deriving Show

mapGT k i = \case
    GuardNode e c pps gt -> GuardNode (i k e) c ({-todo: up-} pps) $ mapGT (k + sum (map varPP pps)) i gt
    Alts gts -> Alts $ map (mapGT k i) gts
    GuardLeaf e -> GuardLeaf $ i k e

upGT k i = mapGT k $ \k -> upS__ k i

substGT i j = mapGT 0 $ \k -> rearrangeS $ \r -> if r == k + i then k + j else if r > k + i then r - 1 else r

dbfGT :: DBNames -> GuardTree -> GuardTree
dbfGT v = mapGT 0 $ \k -> dbf_ k v

mapPP f = \case
    ParPat ps -> ParPat (mapP f <$> ps)

mapP :: (SExp -> SExp) -> Pat -> Pat
mapP f = \case
    PVar n -> PVar n
    PCon n pp -> PCon n (mapPP f <$> pp)
    ViewPat e pp -> ViewPat (f e) (mapPP f pp)
    PatType pp e -> PatType (mapPP f pp) (f e)

upP i j = mapP (upS__ i j)

varPP = \case
    ParPat ps -> sum $ map varP ps

varP = \case
    PVar _ -> 1
    PCon n pp -> sum $ map varPP pp
    ViewPat e pp -> varPP pp
    PatType pp e -> varPP pp

getPVars :: Pat -> DBNames
getPVars = DBNamesC . reverse . getPVars_

getPPVars = DBNamesC . reverse . getPPVars_

getPVars_ = \case
    PVar n -> [n]
    PCon _ pp -> foldMap getPPVars_ pp
    ViewPat e pp -> getPPVars_ pp
    PatType pp e -> getPPVars_ pp

getPPVars_ = \case
    ParPat pp -> foldMap getPVars_ pp

alts (Alts xs) = concatMap alts xs
alts x = [x]

compileGuardTree :: (SExp -> SExp) -> (SExp -> SExp) -> GlobalEnv' -> GuardTree -> SExp
compileGuardTree unode node adts t = (\x -> traceD ("  !  :" ++ showSExp x) x) $ guardTreeToCases t
  where
    guardTreeToCases :: GuardTree -> SExp
    guardTreeToCases t = case alts t of
        [] -> unode $ SBuiltin "undefined"
        GuardLeaf e: _ -> node e
        ts@(GuardNode f s _ _: _) -> case Map.lookup s (snd adts) of
            Nothing -> error $ "Constructor is not defined: " ++ s
            Just (Left ((t, inum), cns)) ->
                foldl SAppV (SGlobal (debugSI "compileGuardTree2", caseName t) `SAppV` iterateN (1 + inum) SLamV (Wildcard SType))
                    [ iterateN n SLamV $ guardTreeToCases $ Alts $ map (filterGuardTree (upS__ 0 n f) cn 0 n . upGT 0 n) ts
                    | (cn, n) <- cns
                    ]
                `SAppV` f
            Just (Right n) -> SGlobal (debugSI "compileGuardTree3", matchName s)
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
            zips is ps = zip (map (SVar (debugSI "30", ".30")) $ zipWith (+) is $ sums $ map varPP ps) ps
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
        PVar _ -> {-todo guardNode v (subst x v ws) $ -} varGuardNode 0 v e
        ViewPat f (ParPat p) -> guardNode (f `SAppV` v) p {- $ guardNode v ws -} e
        PCon (_, s) ps' -> GuardNode v s ps' {- $ guardNode v ws -} e

varGuardNode v (SVar _ e) gt = substGT v e gt

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
    cp ps' ((p@PVar{}, i): xs) e = cp (p: ps') xs e
    cp ps' ((p@(PCon (si, n) ps), i): xs) e = GuardNode (SVar (si, n) $ i + sum (map (fromMaybe 0 . ff) ps')) n ps $ cp (p: ps') xs e
    cp ps' ((p@(ViewPat f (ParPat [PCon (si, n) ps])), i): xs) e
        = GuardNode (SAppV f $ SVar (si, n) $ i + sum (map (fromMaybe 0 . ff) ps')) n ps $ cp (p: ps') xs e

    m = length ps

    ff PVar{} = Nothing
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
type NameDB a = StateT FreshVars (Reader [String]) a

type Doc = NameDB PrecString
{-
expToSExp :: Exp -> SExp
expToSExp = \case
    PMLabel x _     -> expToSExp x
    FixLabel _ x    -> expToSExp x
--    Var k           -> shAtom <$> shVar k
    App a b         -> SApp Visible{-todo-} (expToSExp a) (expToSExp b)
{-
    Lam h a b       -> join $ shLam (usedE 0 b) (BLam h) <$> f a <*> pure (f b)
    Bind h a b      -> join $ shLam (usedE 0 b) h <$> f a <*> pure (f b)
    Cstr a b        -> shCstr <$> f a <*> f b
    FunN s xs       -> foldl (shApp Visible) (shAtom s) <$> mapM f xs
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
    STyped_ x (e, _) -> nameSExp $ expToSExp e  -- todo: mark boundary
    SVar i          -> SGlobal <$> shVar i
-}
envDoc :: Env -> Doc -> Doc
envDoc x m = case x of
    EGlobal{}           -> m
    EBind1 _ h ts b     -> envDoc ts $ join $ shLam (usedS 0 b) h <$> m <*> pure (sExpDoc b)
    EBind2 h a ts       -> envDoc ts $ join $ shLam True h <$> expDoc a <*> pure m
    EApp1 _ h ts b      -> envDoc ts $ shApp h <$> m <*> sExpDoc b
    EApp2 _ h (Lam Visible TType (Var 0)) ts -> envDoc ts $ shApp h (shAtom "tyType") <$> m
    EApp2 _ h a ts      -> envDoc ts $ shApp h <$> expDoc a <*> m
    ELet1 ts b          -> envDoc ts $ shLet_ m (sExpDoc b)
    ELet2 (x, _) ts     -> envDoc ts $ shLet_ (expDoc x) m
    EAssign i x ts      -> envDoc ts $ shLet i (expDoc x) m
    CheckType t ts      -> envDoc ts $ shAnn ":" False <$> m <*> expDoc t
    CheckSame t ts      -> envDoc ts $ shCstr <$> m <*> expDoc t
    CheckAppType si h t te b -> envDoc (EApp1 si h (CheckType_ (sourceInfo b) t te) b) m
    ELabelEnd ts        -> envDoc ts $ shApp Visible (shAtom "labEnd") <$> m

expDoc :: Exp -> Doc
expDoc e = fmap inGreen <$> f e
  where
    f = \case
        PMLabel x _     -> f x
        FixLabel _ x    -> f x
        Var k           -> shAtom <$> shVar k
        App a b         -> shApp Visible <$> f a <*> f b
        Lam h a b       -> join $ shLam (usedE 0 b) (BLam h) <$> f a <*> pure (f b)
        Meta a b        -> join $ shLam (usedE 0 b) BMeta <$> f a <*> pure (f b)
        Pi h a b        -> join $ shLam (usedE 0 b) (BPi h) <$> f a <*> pure (f b)
        CstrT TType a b  -> shCstr <$> f a <*> f b
        FunN s xs       -> foldl (shApp Visible) (shAtom s) <$> mapM f xs
        CaseFun s xs    -> foldl (shApp Visible) (shAtom $ show s) <$> mapM f xs
        TyCaseFun s xs  -> foldl (shApp Visible) (shAtom $ show s) <$> mapM f xs
        NatE n          -> pure $ shAtom $ show n
        ConN s xs       -> foldl (shApp Visible) (shAtom s) <$> mapM f xs
        TyConN s xs     -> foldl (shApp Visible) (shAtom s) <$> mapM f xs
        TType           -> pure $ shAtom "Type"
        ELit l          -> pure $ shAtom $ show l
        Assign i x e    -> shLet i (f x) (f e)
        LabelEnd x      -> shApp Visible (shAtom "labend") <$> f x

sExpDoc :: SExp -> Doc
sExpDoc = \case
    SGlobal (_,s)   -> pure $ shAtom s
    SAnn a b        -> shAnn ":" False <$> sExpDoc a <*> sExpDoc b
    TyType a        -> shApp Visible (shAtom "tyType") <$> sExpDoc a
    SApp _ h a b    -> shApp h <$> sExpDoc a <*> sExpDoc b
    Wildcard t      -> shAnn ":" True (shAtom "_") <$> sExpDoc t
    SBind _ h _ a b -> join $ shLam (usedS 0 b) h <$> sExpDoc a <*> pure (sExpDoc b)
    SLet a b        -> shLet_ (sExpDoc a) (sExpDoc b)
    STyped _ (e,t)  -> expDoc e
    SVar _ i        -> expDoc (Var i)

shVar i = asks $ lookupVarName where
    lookupVarName xs | i < length xs && i >= 0 = xs !! i
    lookupVarName _ = "V" ++ show i

newName = gets head <* modify tail

shLet i a b = shAtom <$> (shVar i) >>= \i' -> local (dropNth i) $ shLam' <$> (cpar . shLet' (fmap inBlue i') <$> a) <*> b
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

removeEscs (ESC _ cs) = removeEscs cs
removeEscs (c: cs) = c: removeEscs cs
removeEscs [] = []

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
trace_level exs = if TraceTypeCheck `elem` exs then 1 else 0 :: TraceLevel  -- 0: no trace
tr = False --trace_level >= 2
tr_light exs = trace_level exs >= 1

debug = False--True--tr
debug_light = True--False

newtype ErrorMsg = ErrorMsg String
instance Show ErrorMsg where show (ErrorMsg s) = s

type ErrorT = ExceptT ErrorMsg

data PolyEnv = PolyEnv
    { getPolyEnv :: GlobalEnv
    , infos      :: Infos
    }

filterPolyEnv p pe = pe { getPolyEnv = Map.filterWithKey (\k _ -> p k) $ getPolyEnv pe }

joinPolyEnvs :: MonadError ErrorMsg m => Bool -> [PolyEnv] -> m PolyEnv
joinPolyEnvs _ = return . foldr mappend' mempty'           -- todo
  where
    mempty' = PolyEnv mempty mempty
    PolyEnv a b `mappend'` PolyEnv a' b' = PolyEnv (a `mappend` a') (b `mappend` b')

throwErrorTCM :: MonadError ErrorMsg m => P.Doc -> m a
throwErrorTCM d = throwError $ ErrorMsg $ show d

inference_ :: PolyEnv -> ModuleR -> ErrorT (WriterT Infos Identity) PolyEnv
inference_ (PolyEnv pe is) m = ff $ runWriter $ runExceptT $ mdo
    defs <- either (throwError . ErrorMsg) return $ definitions m $ mkGlobalEnv' defs `joinGlobalEnv'` extractGlobalEnv' pe
    mapExceptT (fmap $ ErrorMsg +++ snd) . flip runStateT (initEnv <> pe) . flip runReaderT (sourceCode m) . mapM_ (handleStmt $ extensions m) $ defs
  where
    ff (Left e, is) = throwError e
    ff (Right ge, is) = do
        tell is
        return $ PolyEnv ge is

-------------------------------------------------------------------------------- utils

dropNth i xs = take i xs ++ drop (i+1) xs
iterateN n f e = iterate f e !! n
holes xs = [(as, x, bs) | (as, x: bs) <- zip (inits xs) (tails xs)]
mtrace s = trace_ s $ return ()
