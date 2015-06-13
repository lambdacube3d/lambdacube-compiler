{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
module Type where

import Data.Function
import Data.Char
import Data.Either
import Data.String
import Data.Maybe
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Foldable hiding (foldr)
import Data.Traversable
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Applicative
import Control.Arrow hiding ((<+>))
import Text.Parsec.Pos
import Text.Parsec.Error
import GHC.Exts (Constraint)
import Debug.Trace

import ParserUtil (ParseError)
import Pretty

trace' x = trace (ppShow x) x

(<&>) = flip (<$>)

-------------------------------------------------------------------------------- literals

data Lit
    = LInt    Integer
    | LNat    Int
    | LChar   Char
    | LString String
    | LFloat  Double
    deriving (Eq, Ord)

pattern EInt a = ELit (LInt a)
pattern ENat a = ELit (LNat a)
pattern EChar a = ELit (LChar a)
pattern EString a = ELit (LString a)
pattern EFloat a = ELit (LFloat a)

-------------------------------------------------------------------------------- patterns

data Pat_ t c v b
    = PLit_ Lit
    | PVar_ t v
    | PCon_ t c [b]
    | PTuple_ [b]
    | PRecord_ [(Name, b)]
    | PAt_ v b
    | Wildcard_ t
    -- aux
    | PPrec_ b [(b{-TODO: Name?-}, b)]     -- before precedence calculation
    deriving (Functor,Foldable,Traversable)

-- TODO: remove
instance Eq Pat where (==) = error "Eq Pat"
instance Ord Pat where compare = error "Ord Pat"

mapPat :: (t -> t') -> (c -> c') -> (v -> v') -> Pat_ t c v b -> Pat_ t' c' v' b
mapPat tf f g = \case
    PLit_ l -> PLit_ l
    PVar_ t v -> PVar_ (tf t) $ g v
    PCon_ t c p -> PCon_ (tf t) (f c) p
    PTuple_ p -> PTuple_ p
    PRecord_ p -> PRecord_ p -- $ map (g *** id) p
    PAt_ v p -> PAt_ (g v) p
    Wildcard_ t -> Wildcard_ (tf t)

--------------------------------------------

data PatR = PatR Range (Pat_ ExpR Name Name PatR)

pattern PatR' a <- PatR _ a where
    PatR' a = PatR mempty a

pattern PVar' a b = PatR a (PVar_ TWildcard b)
pattern PCon' a b c = PatR a (PCon_ TWildcard b c)

--------------------------------------------

newtype Pat = Pat (Pat_ Exp Name Name Pat)

pattern PAt v l = Pat (PAt_ v l)
pattern PLit l = Pat (PLit_ l)
pattern PVar t l = Pat (PVar_ t l)
pattern PCon t c l = Pat (PCon_ t c l)
pattern PTuple l = Pat (PTuple_ l)
pattern Wildcard t = Pat (Wildcard_ t)

patternVars :: Pat -> [(Name, Exp)]
patternVars (Pat p) = case p of
    PVar_ t v -> [(v, t)]
    PAt_ v p -> [(v, tyOfPat p)]
    p -> foldMap patternVars p

-------------------------------------------------------------------------------- expressions

data Exp_ v p b
    = Star_
    | ELit_     Lit

    | EVar_     b v
    | TCon_     b v
    | TWildcard_            -- star kinded type variable
    | ENext_    b           -- go to next alternative
    -- | TFun_    v [a]     -- TODO

    | Forall_   Visibility (Maybe v) b b
    | ELam_     (Maybe b){-Just:hidden + type-} p b
    | EApp_     b b b
    | ETyApp_   b b b
    | EPrec_    b [(b, b)]      -- aux: used only before precedence calculation
    | ELet_     p b b

    | TRecord_  (Map v b)
    | ERecord_  [(Name, b)]
    | EFieldProj_ b Name

    | TTuple_   [b]
    | ETuple_   [b]
    | ENamedRecord_ Name [(Name, b)]

    | WRefl_    b
    | CEq_      b (TypeFun v b) -- unification between a type and a fully applied type function; CEq t f:  t ~ f
                                -- TODO: merge with CUnify?
    | CUnify_   b b             -- unification between (non-type-function) types; CUnify t s:  t ~ s
    | Split_    b b b           -- Split x y z:  x, y, z are records; fields of x = disjoint union of the fields of y and z

    | ETypeSig_ b b
    | EAlts_    [b]             -- function alternatives
    | PrimFun   b Name [b] Int  -- type, name, collected args, arity

    deriving (Eq,Ord,Functor,Foldable,Traversable) -- TODO: elim Eq instance

data Visibility = Visible | Hidden | Irrelevant deriving (Eq, Ord)

data ExpR = ExpR Range (Exp_ Name PatR ExpR)

expR = ExpR mempty
pattern EVarR' a b = ExpR a (EVar_ TWildcard b)
pattern EAppR' a b c = ExpR a (EApp_ TWildcard b c)
--pattern ELamR' a b c = ExpR a (ELam_ False b c)

pattern ExpR' a <- ExpR _ a where
    ExpR' a = ExpR mempty a

pattern TWildcard = ExpR' TWildcard_

data Exp = ExpTh Subst Exp'
type Exp' = Exp_ Name Pat Exp

type Ty = Exp

pattern Exp a <- (peelThunk -> a) where
    Exp a = thunk a

thunk = ExpTh mempty

-- TODO: eliminate
instance Eq Exp where Exp a == Exp b = a == b
instance Ord Exp where Exp a `compare` Exp b = a `compare` b

pattern TCon k a <- Exp (TCon_ k (TypeIdN a)) where
    TCon k a = Exp (TCon_ k (TypeIdN' a "typecon"))

pattern Star = Exp Star_

pattern TRecord b = Exp (TRecord_ b)
pattern TTuple b = Exp (TTuple_ b)
pattern TUnit = TTuple []
pattern CEq a b = Exp (CEq_ a b)
pattern CUnify a b = Exp (CUnify_ a b)
pattern Split a b c = Exp (Split_ a b c)
pattern Forall a b c = Exp (Forall_ Visible (Just a) b c)
pattern TArr a b = Exp (Forall_ Visible Nothing a b)
pattern ELit a = Exp (ELit_ a)
pattern EVar a <- Exp (EVar_ _ a)
pattern TVar k b = Exp (EVar_ k b)
pattern EApp a b <- Exp (EApp_ _ a b)
pattern TApp k a b = Exp (EApp_ k a b)
pattern ETyApp k a b = Exp (ETyApp_ k a b)
pattern ELam a b = Exp (ELam_ Nothing a b)
pattern ELet a b c = Exp (ELet_ a b c)
pattern ETuple a = Exp (ETuple_ a)
pattern ERecord b = Exp (ERecord_ b)
pattern EFieldProj k a = Exp (EFieldProj_ k a)
pattern EAlts b = Exp (EAlts_ b)
pattern ENext k = Exp (ENext_ k)
pattern WRefl k = Exp (WRefl_ k)

pattern A0 x <- EVar (ExpIdN x)
pattern A1 f x <- EApp (A0 f) x
pattern A2 f x y <- EApp (A1 f x) y
pattern A3 f x y z <- EApp (A2 f x y) z
pattern A4 f x y z v <- EApp (A3 f x y z) v
pattern A5 f x y z v w <- EApp (A4 f x y z v) w
pattern A6 f x y z v w q <- EApp (A5 f x y z v w) q
pattern A7 f x y z v w q r <- EApp (A6 f x y z v w q) r
pattern A8 f x y z v w q r s <- EApp (A7 f x y z v w q r) s
pattern A9 f x y z v w q r s t <- EApp (A8 f x y z v w q r s) t
pattern A10 f x y z v w q r s t a <- EApp (A9 f x y z v w q r s t) a
pattern A11 f x y z v w q r s t a b <- EApp (A10 f x y z v w q r s t a) b

infixr 7 ~>, ~~>
a ~> b = TArr a b

(~~>) :: [Exp] -> Exp -> Exp
args ~~> res = foldr (~>) res args

infix 4 ~~, ~~~
(~~) = CEq
(~~~) = CUnify

buildApp :: (Exp -> Exp) -> Exp -> [Exp] -> Exp
buildApp n restype args = f restype $ reverse args
  where
    f ty [] = n ty
    f ty (a:as) = TApp ty (f (tyOf a ~> ty) as) a


mapExp_ :: (PShow v, PShow p, PShow b, Ord v') => (v -> v') -> (p -> p') -> Exp_ v p b -> Exp_ v' p' b
mapExp_ vf f = \case
    ELit_      x       -> ELit_ x
    EVar_      k x     -> EVar_ k $ vf x
    EApp_      k x y   -> EApp_ k x y
    ELam_ h    x y     -> ELam_ h (f x) y
    ELet_      x y z   -> ELet_ (f x) y z
    ETuple_    x       -> ETuple_ x
    ERecord_   x       -> ERecord_ $ x --map (vf *** id) x
    ENamedRecord_ n x  -> ENamedRecord_ n x --(vf n) $ map (vf *** id) x
    EFieldProj_ k x    -> EFieldProj_ k x -- $ vf x
    ETypeSig_  x y     -> ETypeSig_ x y
    EAlts_     x       -> EAlts_ x
    ENext_ k           -> ENext_ k
    ETyApp_ k b t      -> ETyApp_ k b t
    PrimFun k a b c    -> PrimFun k a b c
    Star_              -> Star_
    TCon_    k v       -> TCon_ k (vf v)
    -- | TFun_    f [a]
    Forall_ h mv b1 b2  -> Forall_ h (vf <$> mv) b1 b2
    TTuple_  bs        -> TTuple_ bs
    TRecord_ m         -> TRecord_ $ Map.fromList $ map (vf *** id) $ Map.toList m -- (Map v b)
    CEq_ a (TypeFun n as) -> CEq_ a (TypeFun (vf n) as)
    CUnify_ a1 a2      -> CUnify_ a1 a2
    Split_ a1 a2 a3    -> Split_ a1 a2 a3
    WRefl_ k           -> WRefl_ k
    TWildcard_         -> TWildcard_
    x                  -> error $ "mapExp: " ++ ppShow x

--traverseExp :: (Applicative m, Ord v') => (v -> v') -> (t -> m t') -> Exp_ v p t -> m (Exp_ v' p t')
traverseExp nf f = fmap (mapExp_ nf id) . traverse f

----------------

data TypeFun n a = TypeFun n [a]
    deriving (Eq,Ord,Functor,Foldable,Traversable)

type TypeFunT = TypeFun IdN Exp

-------------------------------------------------------------------------------- cached type inference 

inferLit :: Lit -> Exp
inferLit a = thunk $ TCon_ (thunk Star_) $ flip TypeIdN' "typecon" $ case a of
    LInt _    -> "Int"
    LChar _   -> "Char"
    LFloat _  -> "Float"
    LString _ -> "String"
    LNat _    -> "Nat"

tyFunRes :: Exp -> Exp
tyFunRes = \case
  TArr a b -> b
  x -> error $ "tyFunRes: not implemented " ++ ppShow x

tyOf :: Exp -> Exp
tyOf = \case
    Exp t -> case t of
        ELit_ l -> inferLit l
        EVar_ k _ -> k
        EApp_ k _ _ -> k
        ETyApp_ k _ _ -> k
        ETuple_ es -> TTuple $ map tyOf es 
        ELam_ (Just k) _ _ -> k
        ELam_ Nothing (tyOfPat -> a) (tyOf -> b) -> Exp $ Forall_ Visible Nothing{-TODO-} a b
        ETypeSig_ b t -> t -- tyOf b
        ELet_ _ _ e -> tyOf e
        ERecord_ (unzip -> (fs, es)) -> TRecord $ Map.fromList $ zip fs $ map tyOf es
        EFieldProj_ k _ -> k
        EAlts_ bs -> tyOf $ head bs
        ENext_ k -> k
        PrimFun k _ _ _ -> k
        -- was types
        Star_ -> Star
        TCon_ k _ -> k
        Forall_ _ _ _ _ -> Star
        TTuple_ _ -> Star
        TRecord_ _ -> Star
        CEq_ _ _ -> Star
        CUnify_ _ _ -> Star
        Split_ _ _ _ -> Star
        WRefl_ k -> k
        e -> error $ "tyOf " ++ ppShow e

tyOfPat :: Pat -> Exp
tyOfPat = \case
    PCon t _ _ -> t
    PVar t _ -> t
    Wildcard t -> t
    PLit l -> inferLit l
    PTuple xs -> thunk $ TTuple_ $ map tyOfPat xs
--    PRecord xs ->  [(Name, b)]
    PAt _ p -> tyOfPat p
    e -> error $ "tyOfPat " ++ ppShow e

isStar = \case
    Star -> True
    _ -> False

-------------------------------------------------------------------------------- tag handling

class GetTag c where
    type Tag c
    getTag :: c -> Tag c

instance GetTag ExpR where
    type Tag ExpR = Range
    getTag (ExpR a _) = a
instance GetTag PatR where
    type Tag PatR = Range
    getTag (PatR a _) = a

-------------------------------------------------------------------------------- names

data NameSpace = TypeNS | ExpNS
    deriving (Eq, Ord)

-- TODO: more structure instead of Doc
data NameInfo = NameInfo (Maybe Fixity) Doc

data N = N
    { nameSpace :: NameSpace
    , qualifier :: [String]
    , nName :: String
    , nameInfo :: NameInfo
    }

instance Eq N where N a b c d == N a' b' c' d' = (a, b, c) == (a', b', c')
instance Ord N where N a b c d `compare` N a' b' c' d' = (a, b, c) `compare` (a', b', c')

type Fixity = (Maybe FixityDir, Int)
data FixityDir = FDLeft | FDRight

pattern ExpN n <- N ExpNS [] n _ where
    ExpN n = N ExpNS [] n (NameInfo Nothing "exp")
pattern ExpN' n i = N ExpNS [] n (NameInfo Nothing i)
pattern TypeN n <- N TypeNS [] n _ where
    TypeN n = N TypeNS [] n (NameInfo Nothing "type")
pattern TypeN' n i = N TypeNS [] n (NameInfo Nothing i)

addPrefix :: String -> Name -> Name
addPrefix s (N a b c d) = N a b (s ++ c) d

-- TODO: rename/eliminate
type Name = N
type TName = N
type TCName = N    -- type constructor name; if this turns out to be slow use Int or ADT instead of String
type EName = N
type FName = N
type MName = N     -- module name
type ClassName = N

toExpN (N _ a b i) = N ExpNS a b i
toTypeN (N _ a b i) = N TypeNS a b i
isTypeVar (N ns _ _ _) = ns == TypeNS
isConstr (N _ _ (c:_) _) = isUpper c || c == ':'

-------------------------------------------------------------------------------- error handling

-- TODO: add more structure to support desugaring
data Range
    = Range SourcePos SourcePos
    | NoRange

instance Monoid Range where
    mempty = NoRange
    Range a1 a2 `mappend` Range b1 b2 = Range (min a1 a2) (max b1 b2)
    NoRange `mappend` a = a
    a `mappend` b = a

type WithRange = (,) Range
pattern WithRange a b = (a, b)

--------------------------------------------------------------------------------

type WithExplanation = (,) Doc

pattern WithExplanation d x = (d, x)

-- TODO: add more structure
data ErrorMsg
    = AddRange Range ErrorMsg
    | InFile String ErrorMsg
    | ErrorCtx Doc ErrorMsg
    | ErrorMsg Doc
    | EParseError ParseError
    | UnificationError Exp Exp [WithExplanation [Exp]]

instance Monoid ErrorMsg where
    mempty = ErrorMsg "<<>>"
    mappend a b = a

instance Show ErrorMsg where
    show = show . f Nothing Nothing Nothing where
        f d file rng = \case
            InFile s e -> f d (Just s) Nothing e
            AddRange NoRange e -> {- showRange file (Just r) <$$> -} f d file rng e
            AddRange r e -> {- showRange file (Just r) <$$> -} f d file (Just r) e
            ErrorCtx d e -> {-"during" <+> d <$$> -} f (Just d) file rng e
            EParseError pe -> text $ show pe
            ErrorMsg e -> maybe "" ("during" <+>) d <$$> (showRange file rng) <$$> e
            UnificationError a b tys -> maybe "" ("during" <+>) d <$$> (showRange file rng) <$$> "cannot unify" <+> pShow a </> "with" <+> pShow b
                <$$> "----------- equations"
                <$$> vcat (map (\(s, l) -> s <$$> vcat (map pShow l)) tys)

dummyPos = newPos "" 0 0

showErr :: ErrorMsg -> (SourcePos, SourcePos, String)
showErr e = (i, j, show msg)
  where
    (r, msg) = f Nothing e
    (i, j) = case r of
        Just (Range i j) -> (i, j)
        _ -> (dummyPos, dummyPos)
    f rng = \case
        InFile s e -> f Nothing e
        AddRange r e -> f (Just r) e
        ErrorCtx d e -> {-(("during" <+> d) <+>) <$> -} f rng e
        EParseError pe -> (Just $ Range p (incSourceColumn p 1), {-vcat $ map (text . messageString) $ errorMessages-} text $ show pe)
            where p = errorPos pe
        ErrorMsg d -> (rng, d)
        UnificationError a b tys -> (rng, "cannot unify" <+> pShow a </> "with" <+> pShow b)

type ErrorT = ExceptT ErrorMsg

throwParseError = throwError . EParseError

mapError f m = catchError m $ throwError . f

addCtx d = mapError (ErrorCtx d)

addRange :: MonadError ErrorMsg m => Range -> m a -> m a
addRange NoRange = id
addRange r = mapError $ AddRange r

--throwErrorTCM :: Doc -> TCM a
throwErrorTCM = throwError . ErrorMsg

showRange :: Maybe String -> Maybe Range -> Doc
showRange Nothing Nothing = "no file position"
showRange Nothing (Just _) = "no file"
showRange (Just _) Nothing = "no position"
showRange (Just src) (Just (Range s e)) = str
    where
      startLine = sourceLine s - 1
      endline = sourceLine e - if sourceColumn e == 1 then 1 else 0
      len = endline - startLine
      str = vcat $ ("position:" <+> text (show s) <+> "-" <+> text (show e)):
                   map text (take len $ drop startLine $ lines src)
                ++ [text $ replicate (sourceColumn s - 1) ' ' ++ replicate (sourceColumn e - sourceColumn s) '^' | len == 1]

-------------------------------------------------------------------------------- parser output

data ValueDef p e = ValueDef Bool{-recursive-} p e
data TypeSig n t = TypeSig n t

data ModuleR
  = Module
  { extensions    :: [Extension]
  , moduleImports :: [Name]    -- TODO
  , moduleExports :: Maybe [Export]
  , definitions   :: [DefinitionR]
  }

type DefinitionR = WithRange Definition
data Definition
    = DValueDef Bool{-True: use in instance search-} (ValueDef PatR ExpR)
    | DAxiom (TypeSig Name ExpR)
    | DDataDef Name [(Name, ExpR)] [WithRange ConDef]      -- TODO: remove, use GADT
    | GADT Name [(Name, ExpR)] [WithRange (Name, ConDef')]
    | ClassDef [ExpR] Name [(Name, ExpR)] [TypeSig Name ExpR]
    | InstanceDef [ExpR] Name [ExpR] [ValueDef PatR ExpR]
    | TypeFamilyDef Name [(Name, ExpR)] ExpR
    | PrecDef Name Fixity
-- used only during parsing
    | PreValueDef (Range, EName) [PatR] WhereRHS
    | DTypeSig (TypeSig EName ExpR)
    | ForeignDef Name ExpR

-- used only during parsing
data WhereRHS = WhereRHS GuardedRHS (Maybe [DefinitionR])

-- used only during parsing
data GuardedRHS
    = Guards Range [(ExpR, ExpR)]
    | NoGuards ExpR

data ConDef = ConDef Name [FieldTy]
data ConDef' = ConDef' [(Maybe Name, ExpR)] [FieldTy] ExpR
data FieldTy = FieldTy {fieldName :: Maybe (Name, Bool{-True: context projection-}), fieldType :: ExpR}

type TypeFunR = TypeFun Name ExpR
type ValueDefR = ValueDef PatR ExpR

data Extension
    = NoImplicitPrelude
    deriving (Eq, Ord, Show)

data Export
    = ExportModule Name
    | ExportId Name

-------------------------------------------------------------------------------- names with unique ids

type IdN = N
pattern IdN a = a
--newtype IdN = IdN N deriving (Eq, Ord)
{- TODO
data IdN = IdN !Int N

instance Eq IdN where IdN i _ == IdN j _ = i == j
instance Ord IdN where IdN i _ `compare` IdN j _ = i `compare` j
-}

pattern TypeIdN n <- IdN (TypeN n)
pattern TypeIdN' n i = IdN (TypeN' n i)
pattern ExpIdN n <- IdN (ExpN n)
pattern ExpIdN' n i = IdN (ExpN' n i)

type FreshVars = [String]     -- fresh typevar names

type VarMT = StateT FreshVars

show5 :: Int -> String
show5 i = replicate (5 - length s) '0' ++ s where s = show i

freshTypeVars :: FreshVars
freshTypeVars = map ('t':) $ map show5 [0..]

resetVars :: MonadState FreshVars m => m ()
resetVars = put freshTypeVars

newName :: MonadState FreshVars m => Doc -> m IdN
newName info = do
    i <- gets head
    modify tail
    return $ TypeN' i info

newEName = do
    i <- gets head
    modify tail
    return $ ExpN $ "e" ++ i


-------------------------------------------------------------------------------- environments

type Env' a = Map Name a
type Env a = Map IdN a

data Item = ISubst Bool{-True: found & replaced def-}  Exp | ISig Bool{-True: Rigid-} Exp

tyOfItem = eitherItem (const tyOf) $ const id

eitherItem f g (ISubst r x) = f r x
eitherItem f g (ISig r x) = g r x

pureSubst se = null [x | ISig rigid x <- Map.elems $ getTEnv se]
onlySig (TEnv x) = TEnv $ Map.filter isSig x
isSig = eitherItem (\_ -> const False) (\rigid -> const True)

newtype Subst = Subst {getSubst :: Env Exp}

instance Monoid Subst where
    mempty = Subst mempty
    -- semantics: subst (m1 <> m2) = subst m1 . subst m2
    -- example:  subst ({y -> z} <> {x -> y}) = subst {y -> z} . subst {x -> y} = subst {y -> z, x -> z}
    -- example2: subst ({x -> z} <> {x -> y}) = subst {x -> z} . subst {x -> y} = subst {x -> y}
    m1@(Subst y1) `mappend` Subst y2 = Subst $ (subst_ m1 <$> y2) <> y1

subst_ = subst
singSubst' a b = Subst $ Map.singleton a b

nullSubst (Subst s) = Map.null s
toTEnv (Subst s) = TEnv $ ISubst False <$> s
toSubst (TEnv s) = Subst $ Map.map (\(ISubst _ e) -> e) $ Map.filter (eitherItem (\_ -> const True) (\_ -> const False)) s

newtype TEnv = TEnv {getTEnv :: Env Item}  -- either substitution or bound name

instance Monoid TEnv where
    mempty = TEnv mempty
    -- semantics: apply (m1 <> m2) = apply m1 . apply m2
    -- example:  subst ({y -> z} <> {x -> y}) = subst {y -> z} . subst {x -> y} = subst {y -> z, x -> z}
    -- example2: subst ({x -> z} <> {x -> y}) = subst {x -> z} . subst {x -> y} = subst {x -> y}
    m1@(TEnv y1) `mappend` TEnv y2 = TEnv $ Map.unionWith mergeSubsts (subst (toSubst m1) <$> y2) y1

mergeSubsts (ISubst _ s) (ISig _ _) = ISubst True s
mergeSubsts (ISubst b s) (ISubst b' _) = ISubst (b || b') s
mergeSubsts (ISig _ _) (ISubst _ s) = ISubst True s
mergeSubsts a _ = a

singSubst a b = TEnv $ Map.singleton a $ ISubst False b
singSubstTy_ a b = TEnv $ Map.singleton a $ ISig False b

-- build recursive environment  -- TODO: generalize
recEnv :: Pat -> Exp -> Exp
recEnv (PVar _ v) th_ = th where th = subst (singSubst' v th) th_
recEnv _ th = th

mapExp' f nf pf e = mapExp_ nf pf $ f <$> e

peelThunk :: Exp -> Exp'
peelThunk (ExpTh env@(Subst m) e)
--  | Map.null m = e
  | otherwise = case e of
    Forall_ h (Just n) a b -> Forall_ h (Just n) (f a) $ subst_ (delEnv n (f a) env) b
    ELam_ h x y -> ELam_ (f <$> h) (mapPat' x) $ subst_ (delEnvs (patternVars x) env) y
    ELet_ x y z -> ELet_ (mapPat' x) (g y) (g z) where
        g = subst_ (delEnvs (patternVars x) env)
    EVar_ k v -> case Map.lookup v m of
        Just e -> case peelThunk e of
            PrimFun _ a b c -> PrimFun (f k) a b c -- hack!
            x -> x
        _ -> EVar_ (f k) v
    _ -> mapExp' f id (error "peelT") e
  where
    f = subst_ env

    mapPat' :: Pat -> Pat
    mapPat' (Pat p) = Pat $ mapPat f id id $ mapPat' <$> p

    delEnvs xs (Subst env) = Subst $ foldr Map.delete env $ map fst xs
    delEnv n x = delEnvs [(n, x)]

subst1 :: Subst -> Exp -> Exp
subst1 s@(Subst m) = \case
    TVar k v -> case Map.lookup v m of
        Just e -> subst1 s e
        _ -> TVar k v
    e -> e

--------------------------------------------------------------------------------
--  fix :: forall (a :: *) . (a -> a) -> a
--  fix = \{a :: *} (f :: a -> a) -> [ x |-> f x ]  x :: a

fixName = ExpN "fix"

fixBody :: Exp
fixBody = Exp $ ELam_ (Just ty) (PVar Star an) $ Exp $ ELam_ Nothing (PVar a fn) fx
  where
    ty = Exp $ Forall_ Hidden (Just an) Star $ (a ~> a) ~> a

    fx = ExpTh (singSubst' x $ TApp a f fx) $ EVar_ a x

    an = TypeN "a"
    a = TVar Star an
    fn = ExpN "f"
    f = TVar (a ~> a) fn
    x = ExpN "x"

--------------------------------------------------------------------------------

data PolyEnv = PolyEnv
    { instanceDefs :: InstanceDefs
    , getPolyEnv :: Env' Item
    , precedences :: PrecMap
    , typeFamilies :: InstEnv
    , infos :: Infos
    }

type Info = (SourcePos, SourcePos, String)
type Infos = [Info]

type InstEnv = Env' Exp

type PrecMap = Env' Fixity

type InstanceDefs = Env' (Map Name ())

emptyPolyEnv :: PolyEnv
emptyPolyEnv = PolyEnv mempty mempty mempty mempty mempty

startPolyEnv = emptyPolyEnv {getPolyEnv = Map.singleton fixName $ ISubst True fixBody}

joinPolyEnvs :: forall m. MonadError ErrorMsg m => Bool -> [PolyEnv] -> m PolyEnv
joinPolyEnvs allownameshadow ps = PolyEnv
    <$> mkJoin' instanceDefs
    <*> mkJoin allownameshadow getPolyEnv
    <*> mkJoin False precedences
    <*> mkJoin False typeFamilies
    <*> pure (concatMap infos ps)
  where
    mkJoin :: Bool -> (PolyEnv -> Env a) -> m (Env a)
    mkJoin True f = return $ Map.unions $ map f ps
    mkJoin False f = case filter (not . Map.null) . map f $ ps of
        [m] -> return m
        ms -> case filter (not . null . drop 1 . snd) $ Map.toList ms' of
            [] -> return $ fmap head $ Map.filter (not . null) ms'
            xs -> throwErrorTCM $ "Definition clash:" <+> pShow (map fst xs)
          where
            ms' = Map.unionsWith (++) $ map ((:[]) <$>) ms

    mkJoin' f = case [(n, x) | (n, s) <- Map.toList ms', (x, is) <- Map.toList s, not $ null $ drop 1 is] of
        _ -> return $ fmap head . Map.filter (not . null) <$> ms'
--        xs -> throwErrorTCM $ "Definition clash':" <+> pShow xs
       where
        ms' = Map.unionsWith (Map.unionWith (++)) $ map ((((:[]) <$>) <$>) . f) ps

addPolyEnv pe m = do
    env <- ask
    env <- joinPolyEnvs True [pe, env]
    local (const env) m

-- reversed order!
getApp (Exp x) = case x of
    EApp_ _ f x -> (id *** (x:)) <$> getApp f
    TCon_ _ n -> Just (n, [])
    _ -> Nothing

withTyping ts = addPolyEnv $ emptyPolyEnv {getPolyEnv = ISig False <$> ts}

-------------------------------------------------------------------------------- monads

nullTEnv (TEnv m) = Map.null m

type TypingT = WriterT' TEnv

type EnvType = (TEnv, Exp)

hidden = \case
    Visible -> False
    _ -> True

toEnvType :: Exp -> ([(Visibility, (Name, Exp))], Exp)
toEnvType = \case
    Exp (Forall_ v@(hidden -> True) (Just n) t x) -> ((v, (n, t)):) *** id $ toEnvType x
    x -> (mempty, x)

envType d = TEnv $ Map.fromList $ map ((id *** ISig False) . snd) d

addInstance n ((envType *** id) . toEnvType -> (_, getApp -> Just (c, _)))
    = addPolyEnv $ emptyPolyEnv {instanceDefs = Map.singleton c $ Map.singleton n ()}

monoInstType v k = Map.singleton v k

toTCMS :: Exp -> TCMS ([Exp], Exp)
toTCMS (toEnvType -> (typ@(envType -> TEnv se), ty)) = WriterT' $ do
    let fv = map (fst . snd) typ
    newVars <- forM fv $ \case
        TypeN' n i -> newName $ "instvar" <+> text n <+> i
        v -> error $ "instT: " ++ ppShow v
    let s = Map.fromList $ zip fv newVars
    return (TEnv $ repl s se, (map (repl s . uncurry (flip TVar)) $ hiddenVars typ, repl s ty))

hiddenVars ty = [x | (Hidden, x) <- ty]

instantiateTyping_ vis info se ty = do
    ambiguityCheck ("ambcheck" <+> info) se ty --(subst su se) (subst su ty)
    typingToTy_ vis ".." (se, ty)
  where
    su = toSubst se

splitEnv (TEnv se) = TEnv *** TEnv $ cycle (f gr') (se', gr')
  where
    (se', gr') = flip Map.partition se $ \case
        ISubst False _ -> False
        _ -> True
    f = foldMap (\(k, ISubst False x) -> Set.insert k $ freeVars x) . Map.toList
    f' = foldMap (\(k, ISig False x) -> Set.insert k $ freeVars x) . Map.toList
    cycle acc (se, gr) = (if Set.null s then id else cycle (acc <> s)) (se', gr <> gr')
      where
        (se', gr') = flip Map.partitionWithKey se $ \k -> \case
            ISig False t -> not $ Set.insert k (freeVars t) `hasSame` acc
            _ -> True
        s = f' gr'

hasSame a b = not $ Set.null $ a `Set.intersection` b

instantiateTyping_' :: Bool -> Doc -> TEnv -> Exp -> TCM ([(IdN, Exp)], Exp)
instantiateTyping_' typ info se ty = do
    ty <- instantiateTyping_ (if typ then Hidden else Irrelevant) info se ty
    return (hiddenVars $ fst $ toEnvType ty, ty)

-- Ambiguous: (Int ~ F a) => Int
-- Not ambiguous: (Show a, a ~ F b) => b
--ambiguityCheck :: Doc -> TCMS Exp -> TCMS Exp
ambiguityCheck msg se ty = do
    pe <- asks getPolyEnv
    let defined = dependentVars (Map.toList $ getTEnv se) $ Map.keysSet pe <> freeVars ty
    case [(n, c) | (n, ISig rigid c) <- Map.toList $ getTEnv se, not $ any (`Set.member` defined) $ Set.insert n $ freeVars c] of
        [] -> return ()
        err -> do
            tt <- typingToTy' (se, ty)
            throwErrorTCM $
                "during" <+> msg </> "ambiguous type:" <$$> pShow tt <$$> "problematic vars:" <+> pShow err

-- compute dependent type vars in constraints
-- Example:  dependentVars [(a, b) ~ F b c, d ~ F e] [c] == [a,b,c]
dependentVars :: [(IdN, Item)] -> Set TName -> Set TName
dependentVars ie s = cycle mempty s
  where
    cycle acc s
        | Set.null s = acc
        | otherwise = cycle (acc <> s) (grow s Set.\\ acc)

    grow = flip foldMap ie $ \case
      (n, ISig rigid t) -> (Set.singleton n <-> freeVars t) <> case t of
        CEq ty f -> freeVars ty <-> freeVars f
        Split a b c -> freeVars a <-> (freeVars b <> freeVars c)
--        CUnify{} -> mempty --error "dependentVars: impossible" 
        _ -> mempty
--      (n, ISubst False x) -> (Set.singleton n <-> freeVars x)
      _ -> mempty
      where
        a --> b = \s -> if Set.null $ a `Set.intersection` s then mempty else b
        a <-> b = (a --> b) <> (b --> a)

--typingToTy' :: EnvType -> Exp
typingToTy' (s, t) = typingToTy "typingToTy" s t

--typingToTy :: Doc -> TEnv -> Exp -> Exp
typingToTy msg env ty = removeStar . renameVars <$> typingToTy_ Hidden msg (env, ty)
  where
    removeStar (Exp (Forall_ (hidden -> True) _ Star t)) = removeStar t
    removeStar t = t

    renameVars :: Exp -> Exp
    renameVars = flip evalState (map (:[]) ['a'..]) . f mempty
      where
        f m (Exp e) = Exp <$> case e of
            Forall_ h (Just n) k e -> do
                n' <- gets (TypeN . head)
                modify tail
                Forall_ h (Just n') <$> f m k <*> f (Map.insert n n' m) e
            e -> traverseExp nf (f m) e
          where
            nf n = fromMaybe n $ Map.lookup n m

--typingToTy_ :: Visibility -> Doc -> EnvType -> Exp
typingToTy_ vs msg (env, ty) = do
    pe <- asks getPolyEnv
    return $ f (Map.keysSet pe) l
  where
    l = sortBy (compare `on` constrKind . snd) [(n, t) | (n, ISig rigid t) <- Map.toList $ getTEnv env]
    forall_ n k t
--        | n `Set.notMember` freeVars t = TArrH k t
        | otherwise = Exp $ Forall_ vs (Just n) k t

    constrKind = \case
        Star -> 0
        _ -> 2

    -- TODO: make more efficient?
    f s [] = ty
    f s ts = case [x | x@((n, t), ts') <- getOne ts, let fv = freeVars t, fv `Set.isSubsetOf` s] of
        (((n, t), ts): _) -> forall_ n t $ f (Set.insert n s) ts
        _ -> error $ show $ "orderEnv:" <+> msg <$$> pShow ts <$$> pShow l <$$> pShow ty

getOne xs = [(b, a ++ c) | (a, b: c) <- zip (inits xs) (tails xs)]

instance PShow Subst where
    pShowPrec p (Subst t) = "Subst" <+> pShow t

-- type checking monad transformer
type TCMT m = ReaderT PolyEnv (ErrorT (WriterT Infos (VarMT m)))

type TCM = TCMT Identity

type TCMS = TypingT TCM

catchExc :: TCM a -> TCM (Maybe a)
catchExc = mapReaderT $ lift . fmap (either (const Nothing) Just) . runExceptT

-------------------------------------------------------------------------------- free variables

class FreeVars a where freeVars :: a -> Set IdN

instance FreeVars Exp where
    freeVars = \case
        Exp x -> case x of
            ELam_ h x y -> error "freev elam" --freeVars y Set.\\ freeVars x
            ELet_ x y z -> error "freeVars ELet"
            EVar_ k a -> Set.singleton a <> freeVars k
            Forall_ h (Just v) k t -> freeVars k <> Set.delete v (freeVars t)
            x -> foldMap freeVars x

instance FreeVars a => FreeVars [a]                 where freeVars = foldMap freeVars
instance FreeVars a => FreeVars (TypeFun n a)       where freeVars = foldMap freeVars
instance FreeVars a => FreeVars (Env a)         where freeVars = foldMap freeVars

-------------------------------------------------------------------------------- replacement

type Repl = Map IdN IdN

-- TODO: express with Substitute?
class Replace a where repl :: Repl -> a -> a

-- TODO: make more efficient
instance Replace Exp where
    repl st = \case
        ty | Map.null st -> ty -- optimization
        Exp s -> Exp $ case s of
            ELam_ h _ _ -> error "repl lam"
            ELet_ _ _ _ -> error "repl let"
            Forall_ h (Just n) a b -> Forall_ h (Just n) (f a) (repl (Map.delete n st) b)
            t -> mapExp' f rn (error "repl") t
      where
        f = repl st
        rn a
            | Just t <- Map.lookup a st = t
            | otherwise = a

instance Replace a => Replace (Env a) where
    repl st e = Map.fromList $ map (r *** repl st) $ Map.toList e
      where
        r x = fromMaybe x $ Map.lookup x st

instance (Replace a, Replace b) => Replace (Either a b) where
    repl st = either (Left . repl st) (Right . repl st)
instance Replace Item where
    repl st = eitherItem (\r -> ISubst r . repl st) (\r -> ISig r . repl st)

-------------------------------------------------------------------------------- substitution

-- TODO: review usage (use only after unification)
class Substitute x a where subst :: x -> a -> a

--instance Substitute a => Substitute (Constraint' n a)      where subst = fmap . subst
instance Substitute x a => Substitute x [a]                    where subst = fmap . subst
instance (Substitute x a, Substitute x b) => Substitute x (a, b) where subst s (a, b) = (subst s a, subst s b)
instance (Substitute x a, Substitute x b) => Substitute x (Either a b) where subst s = subst s +++ subst s
instance Substitute x Exp => Substitute x Item where subst s = eitherItem (\r -> ISubst r . subst s) (\r -> ISig r . subst s)
{-
instance Substitute Pat where
    subst s = \case
        PVar t v -> PVar $ subst s v
        PCon t n l -> PCon (VarE n $ subst s ty) $ subst s l
        Pat p -> Pat $ subst s <$> p
-}
--instance Substitute TEnv Exp where subst = subst . toSubst --m1 (ExpTh m exp) = ExpTh (toSubst m1 <> m) exp
instance Substitute Subst Exp where subst m1 (ExpTh m exp) = ExpTh (m1 <> m) exp
--instance Substitute TEnv TEnv where subst s (TEnv m) = TEnv $ subst s <$> m
instance Substitute Subst TEnv where subst s (TEnv m) = TEnv $ subst s <$> m

-------------------------------------------------------------------------------- LambdaCube specific definitions
-- TODO: eliminate most of these

pattern StarStar = TArr Star Star

pattern TCon0 a = TCon Star a
pattern TCon1 a b = TApp Star (TCon StarStar a) b
pattern TCon2 a b c = TApp Star (TApp StarStar (TCon (TArr Star StarStar) a) b) c
pattern TCon2' a b c = TApp Star (TApp StarStar (TCon VecKind a) b) c
pattern TCon3' a b c d = TApp Star (TApp StarStar (TApp VecKind (TCon (TArr Star VecKind) a) b) c) d

pattern TVec a b = TCon2' "Vec" (ENat a) b
pattern TMat a b c = TApp Star (TApp StarStar (TApp VecKind (TCon MatKind "Mat") (ENat a)) (ENat b)) c
pattern TSingRecord x t <- TRecord (singletonView -> Just (x, t))
singletonView m = case Map.toList m of
    [a] -> Just a
    _ -> Nothing

-- basic types
pattern TChar = TCon0 "Char"
pattern TString = TCon0 "String"
pattern TBool = TCon0 "Bool"
pattern TWord = TCon0 "Word"
pattern TInt = TCon0 "Int"
pattern TNat = TCon0 "Nat"
pattern TFloat = TCon0 "Float"
pattern VecKind = TArr TNat StarStar
pattern MatKind = TArr TNat (TArr TNat StarStar)
pattern TList a = TCon1 "List" a

-- Semantic
pattern Depth a = TCon1 "Depth" a
pattern Stencil a = TCon1 "Stencil" a
pattern Color a = TCon1 "Color" a

-- GADT
pattern TFragmentOperation b = TCon1 "FragmentOperation" b
pattern TImage b c = TCon2' "Image" b c
pattern TInterpolated b = TCon1 "Interpolated" b
pattern TFrameBuffer b c = TCon2' "FrameBuffer" b c
pattern TSampler = TCon0 "Sampler"

pattern ClassN n <- TypeN n where
    ClassN n = TypeN' n "class"
pattern IsValidOutput = ClassN "ValidOutput"
pattern IsTypeLevelNatural = ClassN "TNat"
pattern IsValidFrameBuffer = ClassN "ValidFrameBuffer"
pattern IsAttributeTuple = ClassN "AttributeTuple"

pattern TypeFunS a b <- TypeFun (TypeN a) b where
    TypeFunS a b = TypeFun (TypeN' a "typefun") b
pattern TFMat a b               = TypeFunS "TFMat" [a, b]      -- may be data family
pattern TFVec a b               = TypeFunS "TFVec" [a, b]      -- may be data family
pattern TFMatVecElem a          = TypeFunS "MatVecElem" [a]
pattern TFMatVecScalarElem a    = TypeFunS "MatVecScalarElem" [a]
pattern TFVecScalar a b         = TypeFunS "VecScalar" [a, b]
pattern TFFTRepr' a             = TypeFunS "FTRepr'" [a]
pattern TFColorRepr a           = TypeFunS "ColorRepr" [a]
pattern TFFrameBuffer a         = TypeFunS "TFFrameBuffer" [a]
pattern TFFragOps a             = TypeFunS "FragOps" [a]
pattern TFJoinTupleType a b     = TypeFunS "JoinTupleType" [a, b]

-------------------------------------------------------------------------------- reduce to Head Normal Form

type ReduceM = ExceptT String (State Int)

isNext (Exp a) = case a of
    ENext_ _ -> Nothing
    e -> Just $ Exp e

e &. f = maybe e f $ isNext e
e >>=. f = isNext e >>= f

msum' (x: xs) = fromMaybe (msum' xs) $ isNext x
msum' _ = error "pattern match failure."

reduceFail' msg = Nothing

-- full reduction
-- TODO! reduction under lambda needs alpha-conversion!
reduce :: Exp -> Exp
reduce e = reduceHNF e & \(Exp e) -> Exp $ reduce <$> e

-- don't reduce under lambda
reduce' :: Exp -> Exp
reduce' e = reduceHNF e & \(Exp e) -> case e of
    ELam_ _ _ _ -> Exp e
    ELet_ a b c -> Exp e -- TODO: reduce b?
    Forall_ a b c d -> Exp e -- TODO: reduce c?
    _ -> Exp $ reduce' <$> e

reduceHNF :: Exp -> Exp       -- Left: pattern match failure
reduceHNF e_@(Exp exp) = case exp of

    ELet_ p x e -> reduceHNF $ TApp (tyOf e_) (ELam p e) x

    PrimFun k (ExpN f) acc 0 -> evalPrimFun keep id k f $ map reduceHNF (reverse acc)

    EAlts_ (map reduceHNF -> es) -> msum' es -- ++ error ("pattern match failure " ++ show [err | Left err <- es])
    EApp_ _ f x -> reduceHNF f &. \(Exp f) -> case f of

        PrimFun (TArr _ k) f acc i
            | i > 0 -> reduceHNF $ Exp $ PrimFun k f (x: acc) (i-1)
--            | otherwise -> error $ "too much argument for primfun " ++ ppShow f ++ ": " ++ ppShow exp

        EFieldProj_ _ fi -> reduceHNF x &. \case
            ERecord fs -> case [e | (fi', e) <- fs, fi' == fi] of
                [e] -> reduceHNF e
            e -> case fi of
                ExpN "x" -> case e of
                    A4 "V4" x y z w -> x
                    A3 "V3" x y z -> x
                    A2 "V2" x y -> x
                    _ -> keep
                ExpN "y" -> case e of
                    A4 "V4" x y z w -> y
                    A3 "V3" x y z -> y
                    A2 "V2" x y -> y
                    _ -> keep
                ExpN "z" -> case e of
                    A4 "V4" x y z w -> z
                    A3 "V3" x y z -> z
                    _ -> keep
                ExpN "w" -> case e of
                    A4 "V4" x y z w -> w
                    _ -> keep
                _ -> keep

        ELam_ _ p e -> matchPattern (reduce' x) p >>=.. \case
            Just m' -> reduceHNF $ subst m' e
            _ -> keep
        _ -> keep
    _ -> keep
  where
    keep = Exp exp

    e >>=.. f = maybe (Exp $ ENext_ $ tyOf keep) f e

    -- TODO: make this more efficient (memoize reduced expressions)
    matchPattern :: Exp -> Pat -> Maybe (Maybe Subst)       -- Left: pattern match failure; Right Nothing: can't reduce
    matchPattern e = \case
        Wildcard _ -> return $ Just mempty
        PLit l -> e >>=. \case
            ELit l'
                | l == l' -> return $ Just mempty
                | otherwise -> reduceFail' $ "literals doesn't match:" <+> pShow (l, l')
            _ -> return Nothing
        PVar _ v -> return $ Just $ singSubst' v e
        PTuple ps -> e >>=. \e -> case e of
            ETuple xs -> fmap mconcat . sequence <$> sequence (zipWith matchPattern xs ps)
            _ -> return Nothing
        PCon t c ps -> getApp [] e >>= \case
            Just (c', xs)
                | c == c' && length xs == length ps -> fmap mconcat . sequence <$> sequence (zipWith matchPattern xs ps)
                | otherwise -> reduceFail' $ "constructors doesn't match:" <+> pShow (c, c')
            _ -> return Nothing
        p -> error $ "matchPattern: " ++ ppShow p
      where
        getApp acc e = e >>=. \e -> case e of
            EApp a b -> getApp (b: acc) a
            EVar n | isConstr n -> return $ Just (n, acc)
            _ -> return Nothing

evalPrimFun :: Exp -> (Exp -> Exp) -> Exp -> String -> [Exp] -> Exp
evalPrimFun keep red k = f where
    f "primIntToFloat" [EInt i] = EFloat $ fromIntegral i
    f "primNegateFloat" [EFloat i] = EFloat $ negate i
    f "PrimSin" [EFloat i] = EFloat $ sin i
    f "PrimCos" [EFloat i] = EFloat $ cos i
    f "PrimExp" [EFloat i] = EFloat $ exp i
    f "PrimLog" [EFloat i] = EFloat $ log i
    f "PrimAbs" [EFloat i] = EFloat $ abs i
    f "PrimAddS" [EFloat i, EFloat j] = EFloat $ i + j
    f "PrimSubS" [EFloat i, EFloat j] = EFloat $ i - j
    f "PrimSubS" [EInt i, EInt j] = EInt $ i - j
    f "PrimMulS" [EFloat i, EFloat j] = EFloat $ i * j
    f "PrimDivS" [EFloat i, EFloat j] = EFloat $ i / j
    f "PrimIfThenElse" [A0 "True",t,_] = red t
    f "PrimIfThenElse" [A0 "False",_,e] = red e
    f "PrimGreaterThan" [EFloat i, EFloat j] = if i > j then TVar TBool (ExpN "True") else TVar TBool (ExpN "False")
    f _ _ = keep

pattern Prim a b <- Exp (PrimFun _ (ExpN a) b 0)
pattern Prim1 a b <- Prim a [b]
pattern Prim2 a b c <- Prim a [c, b]
pattern Prim3 a b c d <- Prim a [d, c, b]

-------------------------------------------------------------------------------- Pretty show instances

-- TODO: eliminate
showN :: N -> String
showN (N _ qs s _) = show $ hcat (punctuate (pShow '.') $ map text $ qs ++ [s])

showVar (N q _ n (NameInfo _ i)) = pShow q <> text n <> "{" <> i <> "}"

instance PShow N where
    pShowPrec p = \case
        N _ qs s (NameInfo _ i) -> hcat (punctuate (pShow '.') $ map text $ qs ++ [s]) -- <> "{" <> i <> "}"

instance PShow NameSpace where
    pShowPrec p = \case
        TypeNS -> "'"
        ExpNS -> ""

--instance PShow IdN where pShowPrec p (IdN n) = pShowPrec p n

instance PShow Lit where
    pShowPrec p = \case
        LInt    i -> pShow i
        LChar   i -> text $ show i
        LString i -> text $ show i
        LFloat  i -> pShow i
        LNat    i -> pShow i

--        Exp k i -> pInfix (-2) "::" p i k
instance (PShow v, PShow p, PShow b) => PShow (Exp_ v p b) where
    pShowPrec p = \case
        EPrec_ e es -> pApps p e $ concatMap (\(a, b) -> [a, b]) es
        ELit_ l -> pShowPrec p l
        EVar_ k v -> pShowPrec p v
        EApp_ k a b -> pApp p a b
        ETyApp_ k a b -> pTyApp p a b
        ETuple_ a -> tupled $ map pShow a
        ELam_ Nothing p b -> pParens True ("\\" <> pShow p </> "->" <+> pShow b)
        ELam_ _ p b -> pParens True ("\\" <> braces (pShow p) </> "->" <+> pShow b)
        ETypeSig_ b t -> pShow b </> "::" <+> pShow t
        ELet_ a b c -> "let" <+> pShow a </> "=" <+> pShow b </> "in" <+> pShow c
        ENamedRecord_ n xs -> pShow n <+> showRecord xs
        ERecord_ xs -> showRecord xs
        EFieldProj_ k n -> "." <> pShow n
        EAlts_ b -> braces (vcat $ punctuate (pShow ';') $ map pShow b)
        ENext_ k -> "SKIP"
        PrimFun k a b c -> "primfun" <+> pShow a <+> pShow b <+> pShow c

        Star_ -> "*"
        TCon_ k n -> pShow n
        Forall_ Visible Nothing a b -> pInfixr' (-1) "->" p a b
        Forall_ Irrelevant Nothing a b -> pInfixr' (-1) "==>" p a b
        Forall_ Hidden Nothing a b -> pInfixr' (-1) "=>" p a b
        Forall_ Visible (Just n) a b -> "forall" <+> pParens True (pShow n </> "::" <+> pShow a) <> "." <+> pShow b
        Forall_ Irrelevant (Just n) a b -> "forall" <+> "." <> braces (pShow n </> "::" <+> pShow a) <> "." <+> pShow b
        Forall_ Hidden (Just n) a b -> "forall" <+> braces (pShow n </> "::" <+> pShow a) <> "." <+> pShow b
        TTuple_ a -> tupled $ map pShow a
        TRecord_ m -> "Record" <+> showRecord (Map.toList m)
        CEq_ a b -> pShow a <+> "~" <+> pShow b
        CUnify_ a b -> pShow a <+> "~" <+> pShow b
        Split_ a b c -> pShow a <+> "<-" <+> "(" <> pShow b <> "," <+> pShow c <> ")"
        WRefl_ k -> "refl" <+> pShow k
        TWildcard_ -> "twildcard"

getConstraints = \case
    Exp (Forall_ (hidden -> True) n c t) -> ((n, c):) *** id $ getConstraints t
    t -> ([], t)

showConstraints cs x
    = (case cs of [(Nothing, c)] -> pShow c; _ -> tupled (map pShow' cs)) 
    </> "=>" <+> pShowPrec (-2) x
  where
    pShow' (Nothing, x) = pShow x
    pShow' (Just n, x) = pShow n <+> "::" <+> pShow x

instance PShow Exp where
    pShowPrec p = \case
      (getConstraints -> (cs@(_:_), t)) -> showConstraints cs t
      t -> case getLams t of
        ([], Exp e) -> pShowPrec p e
        (ps, Exp e) -> pParens (p > 0) $ "\\" <> hsep (map (pShowPrec 10) ps) </> "->" <+> pShow e
      where
        getLams (ELam p e) = (p:) *** id $ getLams e
        getLams e = ([], e)

instance PShow ExpR where
    pShowPrec p e = case getLamsR e of
        ([], ExpR _ e) -> pShowPrec p e
        (ps, ExpR _ e) -> "\\" <> hsep (map pShow ps) </> "->" <+> pShow e
      where
        getLamsR (ExpR' (ELam_ Nothing p e)) = (p:) *** id $ getLamsR e
        getLamsR e = ([], e)

instance (PShow c, PShow v, PShow b) => PShow (Pat_ t c v b) where
    pShowPrec p = \case
        PLit_ l -> pShow l
        PVar_ t v -> pShow v
        PCon_ t s xs -> pApps p s xs
        PTuple_ a -> tupled $ map pShow a
        PRecord_ xs -> "Record" <+> showRecord xs
        PAt_ v p -> pShow v <> "@" <> pShow p
        Wildcard_ t -> "_"
        PPrec_ e es -> pApps p e $ concatMap (\(a, b) -> [a, b]) es

instance PShow PatR where
    pShowPrec p (PatR _ e) = pShowPrec p e

instance PShow Pat where
    pShowPrec p (Pat e) = pShowPrec p e

instance (PShow n, PShow a) => PShow (TypeFun n a) where
    pShowPrec p (TypeFun s xs) = pApps p s xs


instance PShow TEnv where
    pShowPrec p (TEnv e) = showRecord $ Map.toList e

instance PShow Item where
    pShowPrec p = eitherItem (\r -> (("Subst" <> if r then "!" else "") <+>) . pShow) (\rigid -> (("Sig" <> if rigid then "!" else "") <+>) . pShow)

instance PShow Range where
    pShowPrec p = \case
        Range a b -> text (show a) <+> "--" <+> text (show b)
        NoRange -> ""

instance PShow Definition where
    pShowPrec p = \case
        DValueDef False (ValueDef False x _) -> "ValueDef" <+> pShow x
        DValueDef False (ValueDef rec x _) -> "ValueDef rec" <+> pShow x
        DValueDef True (ValueDef False x _) -> "ValueDef [instance]" <+> pShow x
        DAxiom (TypeSig x _) -> "axiom" <+> pShow x
        DDataDef n _ _ -> "data" <+> pShow n
        GADT n _ _ -> "gadt" <+> pShow n
        ClassDef _ n _ _ -> "class" <+> pShow n
        InstanceDef _ n _ _ -> "instance" <+> pShow n
        TypeFamilyDef n _ _ -> "type family" <+> pShow n
    -- used only during parsing
        PreValueDef (_, n) _ _ -> "pre valuedef" <+> pShow n
        DTypeSig (TypeSig n _) -> "typesig" <+> pShow n
        ForeignDef n _ -> "foreign" <+> pShow n
        PrecDef n p -> "precdef" <+> pShow n

instance PShow FixityDir where
    pShowPrec p = \case
        FDLeft -> "infixl"
        FDRight -> "infixr"

-------------------------------------------------------------------------------- WriterT'

class Monoid' e where
    type MonoidConstraint e :: * -> *
    mempty' :: e
    mappend' :: e -> e -> MonoidConstraint e e

newtype WriterT' e m a
  = WriterT' {runWriterT' :: m (e, a)}
    deriving (Functor,Foldable,Traversable)

instance (Monoid' e) => MonadTrans (WriterT' e) where
    lift m = WriterT' $ (,) mempty' <$> m

instance forall m e . (Monoid' e, MonoidConstraint e ~ m, Monad m) => Applicative (WriterT' e m) where
    pure a = WriterT' $ pure (mempty' :: e, a)
    a <*> b = join $ (<$> b) <$> a

instance (Monoid' e, MonoidConstraint e ~ m, Monad m) => Monad (WriterT' e m) where
    WriterT' m >>= f = WriterT' $ do
            (e1, a) <- m
            (e2, b) <- runWriterT' $ f a
            e <- mappend' e1 e2
            return (e, b)

instance (Monoid' e, MonoidConstraint e ~ m, MonadReader r m) => MonadReader r (WriterT' e m) where
    ask = lift ask
    local f (WriterT' m) = WriterT' $ local f m

instance (Monoid' e, MonoidConstraint e ~ m, MonadWriter w m) => MonadWriter w (WriterT' e m) where
    tell = lift . tell
    listen = error "WriterT' listen"
    pass = error "WriterT' pass"

instance (Monoid' e, MonoidConstraint e ~ m, MonadState s m) => MonadState s (WriterT' e m) where
    state f = lift $ state f

instance (Monoid' e, MonoidConstraint e ~ m, MonadError err m) => MonadError err (WriterT' e m) where
    catchError (WriterT' m) f = WriterT' $ catchError m $ runWriterT' <$> f
    throwError e = lift $ throwError e

mapWriterT' f (WriterT' m) = WriterT' $ f m

