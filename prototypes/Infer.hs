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
  deriving (Eq)

instance Show Lit where
    show = \case
        LInt i -> show i
        LChar c -> show c

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

newtype Additional a = Additional a
instance Eq   (Additional a) where _ == _ = True
instance Ord  (Additional a) where _ `compare` _ = EQ
instance Show (Additional a) where show a = ""

pattern Lam h a b = Bind (BLam h) a b
pattern Pi  h a b = Bind (BPi h) a b
pattern Meta  a b = Bind BMeta a b

pattern App a b     = Prim FApp [a, b]
--pattern FApp <- FunName "app" _ where FApp = FunName "app" $ Additional $ pi_ Type $ pi_ Type 
pattern Cstr a b    = Prim FCstr [a, b]
pattern Coe a b w x = Prim FCoe [a,b,w,x]
pattern FCoe        <- FunName "coe" _ where FCoe = FunName "coe" $ Additional $ pi_ Type $ pi_ Type $ pi_ (Cstr (Var 1) (Var 0)) $ pi_ (Var 2) (Var 2)  -- forall a b . (a ~ b) => a -> b
pattern PrimName a  <- FunName a _
pattern PrimName' a b = FunName a (Additional b)

pattern Con a i b   = ConName a i (Additional b)
pattern Type        = Prim CType []
pattern Sigma a b   <- Prim BSigma [a, Lam _ _ b] where Sigma a b = Prim BSigma [a, Lam Visible a{-todo: don't duplicate-} b]
pattern Unit        = Prim CUnit []
pattern TT          = Prim CTT []
pattern T2T a b     = Prim CT2T [a, b]
pattern T2 a b      <- Prim CT2 [_, _, a, b] where T2 a b = Prim CT2 [error "t21", error "t22", a, b]   -- TODO
pattern Empty       = Prim CEmpty []

pattern Con0 a b    = Con a 0 b
pattern ConN a      <- Con0 a _
pattern BSigma      <- ConN "Sigma" where BSigma = Con0 "Sigma" $ pi_ Type $ pi_ (pi_ (Var 0) Type) $ Type
pattern CType       <- ConN "Type"  where CType = Con0 "Type" Type
pattern CUnit       <- ConN "Unit"  where CUnit = Con0 "Unit" Type
pattern CTT         <- ConN "TT"    where CTT = Con0 "TT" Unit
pattern CT2T        <- ConN "T2"    where CT2T = Con0 "T2" $ pi_ Type $ pi_ Type Type
pattern CT2         <- ConN "T2C"   where CT2 = Con0 "T2C" $ pi_ Type $ pi_ Type $ pi_ (Var 1) $ pi_ (Var 1) $ T2T (Var 1) (Var 0)
pattern CEmpty      <- ConN "Empty" where CEmpty = Con0 "Empty" Type

-------------------------------------------------------------------------------- environments

-- SExp zippers
data Env
    = EBind Binder Exp Env     -- zoom into second parameter of SBind
    | EBind1 Binder Env SExp           -- zoom into first parameter of SBind
    | EApp1 Visibility Env SExp
    | EApp2 Visibility Exp Env
    | EGlobal GlobalEnv [Stmt]
    | ELet Int Exp Env
    | CheckType Exp Env
  deriving Show

type GlobalEnv = Map.Map SName Exp

pattern EEnd a <- EGlobal a _ where EEnd a = EGlobal a mempty

extractEnv = extract where
    extract (ELet _ _ x)    = extract x
    extract (EBind _ _ x)   = extract x
    extract (EBind1 _ x _)  = extract x
    extract (EApp2 _ _ x)   = extract x
    extract (EApp1 _ x _)   = extract x
    extract (CheckType _ x) = extract x
    extract (EGlobal x _)   = x

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

upS__ i n = mapS (\i -> upE i n) (+1) i $ \i k -> SVar $ if k >= i then k+n else k
upS = upS__ 0 1

up1E = g where
    g i = \case
        Var k -> Var $ if k >= i then k+1 else k
        Bind h a b -> Bind h (g i a) (g (i+1) b)
        Prim s as  -> Prim s $ map (g i) as
        CLet j a b -> handleLet i j $ \i' j' -> CLet j' (g i' a) (g i' b)

upE i n e = iterate (up1E i) e !! n

substS j x = mapS (uncurry substE) ((+1) *** up1E 0) (j, x)
            (\(i, x) k -> case compare k i of GT -> SVar (k-1); LT -> SVar k; EQ -> STyped x)

substE i x = \case
    Var k -> case compare k i of GT -> Var $ k - 1; LT -> Var k; EQ -> x
    Bind h a b -> Bind h (substE i x a) (substE (i+1) (up1E 0 x) b)
    Prim s as  -> eval . Prim s $ map (substE i x) as
    CLet j a b -> mergeLets (Meta (cstr x a) $ up1E 0 b) CLet substE (\i j -> substE i j b) i x j a

unVar (Var i) = i

-----------xabcdQ
-----------abcdQ
downE t x | usedE t x = Nothing
          | otherwise = Just $ substE t (error "downE") x

varType :: String -> Int -> Env -> (Binder, Exp)
varType err n_ env = f n_ env where
    f n (ELet i x es)  = id *** substE i x $ f (if n < i then n else n+1) es
    f 0 (EBind b t _)  = (b, up1E 0 t)
    f n (EBind _ _ es) = id *** up1E 0 $ f (n-1) es
    f n (EBind1 _ es _) = f n es
    f n (EApp2 _ _ es) = f n es
    f n (EApp1 _ es _) = f n es
    f n (CheckType _ es) = f n es
    f n xx = error $ "varType: " ++ err ++ "\n" ++ show n_ ++ "\n" ++ show env ++ "\n" ++ show xx

-------------------------------------------------------------------------------- reduction

infixl 1 `app_`

app_ :: Exp -> Exp -> Exp
app_ (Lam _ _ x) a = substE 0 a x
app_ (Prim (Con s n t) xs) a = Prim (Con s (n-1) t) (xs ++ [a])
app_ f a = App f a

eval (App a b) = app_ a b
eval (Cstr a b) = cstr a b
eval (Coe a b c d) = coe a b c d
-- todo: elim
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
--cstr (App x@(Var j) y) b@(Var i) | j /= i, Nothing <- downE i y = cstr x (Lam (expType' y) $ up1E 0 b)
cstr a@Var{} b = Cstr a b
cstr a b@Var{} = Cstr a b
--cstr (App x@Var{} y) b@Prim{} = cstr x (Lam (expType' y) $ up1E 0 b)
--cstr b@Prim{} (App x@Var{} y) = cstr (Lam (expType' y) $ up1E 0 b) x
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

tInt = Prim (Con0 "Int" Type) []

primitiveType = \case
    CLit (LInt _)  -> tInt
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

check env x t = checkN (EEnd env) x t
infer env x = inferN (EEnd env) x

inferN :: Env -> SExp -> Exp
inferN te exp = (if tr then trace ("infer: " ++ showEnvSExp te exp) else id) $ recheck_ te $ case exp of
    SLit l      -> focus te $ Prim (CLit l) []
    STyped e    -> expand focus te e
    SVar i      -> expand focus te $ Var i
    SGlobal s   -> uncurry focus $ zoomMeta te $ fromMaybe (error "can't found") $ Map.lookup s $ extractEnv te
    SApp  h a b -> inferN (EApp1 h te b) a
    SBind h a b -> inferN ((if h /= BMeta then CheckType Type else id) $ EBind1 h te $ (if isPi h then tyType else id) b) a
  where
    isPi (BPi _) = True
    isPi _ = False
    tyType = SApp Visible $ STyped $ Lam Visible Type $ Var 0

expand focus te e
    | Pi Hidden a b <- expType_ te e
    = expand focus (EBind BMeta a te) (app_ (up1E 0 e) $ Var 0)
    | otherwise = focus te e

checkN te (SLam h a b) (Pi h' x y)
    | h == h'  = if checkSame te a x then checkN (EBind (BLam h) x $ te) b y else error "checkN"
checkN te e (Pi Hidden a b) = checkN (EBind (BLam Hidden) a te) (upS e) b
checkN te e t = inferN (CheckType t te) e

-- todo
checkSame te (Wildcard (Wildcard SType)) a = True
checkSame te (Wildcard SType) a = case expType_ te a of
    Type -> True
checkSame te a b = error $ "checkSame: " ++ show (a, b)

cstr' h x y e = EApp2 h (coe (up1E 0 x) (up1E 0 y) (Var 0) (up1E 0 e)) . EBind BMeta (cstr x y)

focus :: Env -> Exp -> Exp
focus env e = (if tr then trace $ "focus: " ++ showEnvExp env e else id) $ case env of
    EApp1 h te b
        | Pi Visible x y <- expType_ env e -> checkN (EApp2 h e te) b x
        | Pi Hidden x y  <- expType_ env e -> error "todo"
        | otherwise -> inferN (CheckType (Var 2) $ cstr' h (upE 0 2 $ expType_ env e) (Pi Visible (Var 1) (Var 1)) (upE 0 2 e) $ EBind BMeta Type $ EBind BMeta Type te) (upS__ 0 3 b)
    CheckType t te      -> expand (\te e -> focus (EBind BMeta (cstr t (expType_ te e)) te) $ up1E 0 e) te e
    EApp2 Visible a te  -> focus te $ app_ a e
    EBind1 h te b       -> inferN (EBind h e te) b
    EBind BMeta tt te
        | Unit <- tt    -> focus te $ substE 0 TT e
        | T2T x y <- tt -> focus (EBind BMeta (up1E 0 y) $ EBind BMeta x te) $ substE 2 (T2 (Var 1) (Var 0)) $ upE 0 2 e
        | Cstr a b <- tt -> case (cst a b, cst b a) of
            (Just (i, r), Just (j, _)) | i < j -> r
            (Just (_, r), _) -> r
            (_, Just (_, r)) -> r
        | EBind h@((/= BMeta) -> True) x te' <- te, Just b' <- downE 0 tt
                        -> refocus (EBind h (up1E 0 x) $ EBind BMeta b' te') (substE 2 (Var 0) $ up1E 0 e)
        | EBind1 h te' x  <- te -> refocus (EBind1 h (EBind BMeta tt te') $ upS__ 1 1 x) e
        | EApp1 h te' x   <- te -> refocus (EApp1 h (EBind BMeta tt te') $ upS x) e
        | EApp2 h x te'   <- te -> refocus (EApp2 h (up1E 0 x) $ EBind BMeta tt te') e
        | CheckType t te' <- te -> refocus (CheckType (up1E 0 t) $ EBind BMeta tt te') e
      where
        cst x = \case
            Var i | fst (varType "X" i te) == BMeta -> fmap (\x -> (i, focus (ELet i x te) $ substE i x $ substE 0 TT e)) $ downE i x
            _ -> Nothing
    EBind h a te -> focus te $ Bind h a e
    ELet i b te -> case te of
        EBind h x te' | i > 0, Just b' <- downE 0 b
                          -> refocus' (EBind h (substE (i-1) b' x) (ELet (i-1) b' te')) e
        EBind1 h te' x    -> refocus' (EBind1 h (ELet i b te') $ substS (i+1) (up1E 0 b) x) e
        EApp1 h te' x     -> refocus' (EApp1 h (ELet i b te') $ substS i b x) e
        EApp2 h x te'     -> refocus' (EApp2 h (substE i b x) $ ELet i b te') e
        CheckType t te'   -> refocus' (CheckType (substE i b t) $ ELet i b te') e
        te                -> maybe (focus te $ CLet i b e) (flip refocus' e) $ pull i te
      where
        pull i = \case
            EBind BMeta _ te | i == 0 -> Just te
            EBind h x te    -> EBind h <$> downE (i-1) x <*> pull (i-1) te
            ELet j b te     -> ELet (if j <= i then j else j-1) <$> downE i b <*> pull (if j <= i then i+1 else i) te
            _               -> Nothing
    EGlobal{} -> e
    _ -> error $ "focus: " ++ show env

refocus e (Bind BMeta x a) = focus (EBind BMeta x e) a
refocus e (CLet i x a) = focus (ELet i x e) a
refocus e a = focus e a

refocus' e (Bind BMeta x a) = refocus' (EBind BMeta x e) a
refocus' e (CLet i x a) = focus (ELet i x e) a
refocus' e a = focus e a

zoomMeta :: Env -> Exp -> (Env, Exp)
zoomMeta env = \case
    Meta t e -> zoomMeta (EBind BMeta t env) e
    CLet i t e -> zoomMeta (ELet i t env) e
    e -> (env, e)

-------------------------------------------------------------------------------- debug support

{-
evv (env, e) y = sum [case t of Type -> 1; _ -> error $ "evv: " ++ showEnvExp e x ++ "\n"  ++ showEnvExp e t | (e, x, t) <- checkEnv env] `seq` 
    (length $ show $ checkInfer env e) `seq` y

checkEnv ENil = []
checkEnv (EBind _ t e) = (e, t, checkInfer e t): checkEnv e
checkEnv (ELet i t e) = (e, t', checkInfer e (checkInfer e t')): checkEnv e  where t' = up1E i t
-}
recheck :: Exp -> Exp
recheck e = length (show $ checkInfer te e') `seq` e  where (te, e') = zoomMeta (EEnd env) e

recheck_ e' x = if debug then length (show $ checkInfer e'' x') `seq` x else x
  where
    (e'', x') = zoomMeta e' x

checkInfer lu x = flip runReader [] (infer x)  where
    infer = \case
        Pi _ a b -> ch Type a !>> local (a:) (ch Type b) !>> return Type
        Type -> return Type
        Var k -> asks $ \env -> ([upE 0 (k + 1) e | (k, e) <- zip [0..] env] ++ [upE 0 (length env) $ snd $ varType "?" i lu | i<- [0..]]) !! k
        Lam h a b -> ch Type a !>> Pi h a <$> local (a:) (infer b)
        App a b -> ask >>= \env -> appf env <$> infer a <*> infer' b
        Prim s as -> ask >>= \env -> foldl (appf env) (primitiveType s) <$> mapM infer' as
        Meta a b -> {-ch Type a !>> Pi Hidden a <$> local (a:) (infer b)-} error $ "checkInfer: meta"
    infer' a = (,) a <$> infer a
    appf _ (Pi h x y) (v, x') | x == x' = substE 0 v y
    appf en a (_, b) = error $ "recheck:\n" ++ show a ++ "\n" ++ show b ++ "\n" ++ show en ++ "\n" ++ showEnvExp lu x
    ch x e = infer e >>= \case
        z | z == x -> return ()
          | otherwise -> error $ "recheck':\n" ++ show z ++ "\n" ++ show x ++ "\n" ++ showEnvExp lu x

infixl 1 !>>
a !>> b = a >>= \x -> x `seq` b

-------------------------------------------------------------------------------- statements

infer' t = gets $ (\env -> (if debug_light then recheck else id) $ infer env t) . fst
checkP t e = gets $ (\env -> check env e t) . fst

expType'' :: Exp -> String
expType'' e = showEnvExp ev $ expType_ ev e'
  where
    (ev, e') = zoomMeta (EEnd env) e

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
          tt = pis' (upS__ 0 en ct)
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

tracee' x = trace (showDoc $ showSExp x) x

mkPrim c n t = f' 0 t
  where
    f' i (Meta a t) = Meta a $ f' (i+1) t
    f' i (Pi Hidden a b) = Meta a $ f' (i+1) b
    f' i x | c = Prim (Con n (ar x) $ toExp' t) $ map Var [i-1, i-2 .. 0]
           | otherwise = f i x
    f i (Pi h a b) = Lam h a $ f (i+1) b
    f i _ = Prim (if c then Con n 0 t' else PrimName' n t') $ map Var [i-1, i-2 .. 0]
    t' = toExp' t
    toExp' (Meta x e) = Pi Hidden x $ toExp' e
    toExp' a = a
    ar (Pi _ _ b) = 1 + ar b
    ar _ = 0

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
 <|> do SLit . LInt . fromIntegral <$ P.char '#' <*> natural lang
 <|> do toNat <$> natural lang
 <|> do reserved lang "fix"
        i <- P.getState
        P.setState (i+1)
        return $ sApp Visible{-Hidden-} (SGlobal "primFix") (SLit $ LInt i)
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

showEnvExp :: Env -> Exp -> String
showEnvExp e c = showDoc $ showEnv e $ epar <$> showExp c

showEnvSExp :: Env -> SExp -> String
showEnvSExp e c = showDoc $ showEnv e $ epar <$> showSExp c

showDoc :: Doc -> String
showDoc = str . flip runReader [] . flip evalStateT (flip (:) <$> iterate ('\'':) "" <*> ['a'..'z'])

type Doc = StateT [String] (Reader [String]) PrecString

showEnv :: Env -> Doc -> Doc
showEnv x m = case x of
    EGlobal{}           -> m
    EBind1 h ts b       -> showEnv ts $ shLam (usedS 0 b) h m (showSExp b)
    EBind  h a ts       -> showEnv ts $ shLam True h (showExp a) m
    EApp1 Visible ts b  -> showEnv ts $ shApp <$> m <*> showSExp b
    EApp2 Visible a ts  -> showEnv ts $ shApp <$> showExp a <*> m
    ELet i x ts         -> showEnv ts $ shLet i (showExp x) m
    CheckType t ts      -> showEnv ts $ shAnn False <$> m <*> showExp t

showExp :: Exp -> Doc
showExp = \case
    Var k           -> shVar k
    App a b         -> shApp <$> showExp a <*> showExp b
    Bind h a b      -> shLam (usedE 0 b) h (showExp a) (showExp b)
    Cstr a b        -> shCstr <$> showExp a <*> showExp b
    Prim s xs       -> foldl shApp (shAtom $ showPrimN s) <$> mapM showExp xs
    CLet i x e      -> shLet i (showExp x) (showExp e)

showSExp :: SExp -> Doc
showSExp = \case
    SVar k          -> shVar k
    SGlobal s       -> pure $ shAtom s
    SLit i          -> pure $ shAtom $ show i
    SAnn a b        -> shAnn False <$> showSExp a <*> showSExp b
    SApp h a b      -> shApp <$> showSExp a <*> showSExp b
    SBind h a b     -> shLam (usedS 0 b) h (showSExp a) (showSExp b)
    Wildcard t      -> shAnn True (shAtom "_") <$> showSExp t
    STyped e        -> showExp e

showPrimN :: PrimName -> String
showPrimN = \case
    CLit i      -> show i
    ConName s _ _ -> s
    FunName s _ -> s
    x           -> show x

shVar k = asks $ shAtom . lookupVarName k
shLet i a b = asks (lookupVarName i) >>= \i' -> local (dropNth i) $ shLam' <$> (cpar . shLet' (shAtom i') <$> a) <*> b
shLam used h a b = newVar >>= \i ->
    let lam = case h of
            BLam _ -> shLam'
            _ -> shArr
        p = case h of
            BMeta -> cpar . shAnn True (shAtom i)
            BLam h -> vpar h
            BPi h -> vpar h
        vpar Hidden = brace . shAnn True (shAtom i)
        vpar Visible = ann (shAtom i)
        ann | used = shAnn True
            | otherwise = const id
    in lam <$> (p <$> a) <*> addVar i b

newVar = gets head <* modify tail
addVar v = local (v:)

lookupVarName i xs | i < length xs && i >= 0 = xs !! i
lookupVarName i _ = "V" ++ show i

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
    | PrecLam       --  \ _ -> _            {accum-left}
    deriving (Eq, Ord)

lpar, rpar :: PrecString -> Prec -> String
lpar (PS i s) j = par (i >. j) s  where
    PrecLam >. i = i > PrecAtom
    i >. PrecLam = i >= PrecArr
    PrecApp >. PrecApp = False
    i >. j  = i >= j
rpar (PS i s) j = par (i >. j) s where
    PrecLam >. _ = False
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

id_test = slam $ SVar 0
id_test' = slam $ sapp id_test $ SVar 0
id_test'' = sapp id_test id_test
const_test = slam $ slam $ SVar 1

test xx = putStrLn $ length s `seq` ("result:\n" ++ s)
    where x = infer env xx
          s = showEnvExp (EEnd env) x

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

