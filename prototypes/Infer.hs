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
    deriving (Show, Read)

data SExp
    = SLit Lit
    | SVar !Int                     -- De Bruijn variable
    | SGlobal SName
    | SBind Binder SExp SExp
    | SApp Visibility SExp SExp
    | STyped Exp
  deriving (Eq, Show, Read)

data Lit
    = LInt !Int
    | LChar Char
  deriving (Eq, Show, Read)

data Binder
    = BPi  Visibility
    | BLam Visibility
    | BMeta      -- a metavariable is like a floating hidden lambda
  deriving (Eq, Show, Read)

data Visibility = Hidden | Visible    | {-not used-} Irr
  deriving (Eq, Show, Read)

pattern SPi  h a b = SBind (BPi  h) a b
pattern SLam h a b = SBind (BLam h) a b
pattern SType = SGlobal "Type"
pattern Wildcard t = SBind BMeta t (SVar 0)
pattern SAnn a b = SApp Visible (SApp Visible (SGlobal "typeAnn") b) a

isPi (BPi _) = True
isPi _ = False
tyType = SApp Visible $ STyped $ Lam Visible Type $ Var 0

-------------------------------------------------------------------------------- destination data

data Exp
    = Bind Binder Exp Exp
    | Prim FunName [Exp]
    | Var  !Int                 -- De Bruijn variable
    | CLet !Int Exp Exp         -- De Bruijn index decreasing let only for metavariables (non-recursive)
  deriving (Eq, Show, Read)

data FunName
    = ConName SName Int{-free arity-}
    | CLit Lit
    | FunName SName
  deriving (Eq, Show, Read)

pattern Lam h a b = Bind (BLam h) a b
pattern Pi  h a b = Bind (BPi h) a b
pattern Meta  a b = Bind BMeta a b
pattern PiV a b = Pi Visible a b

pattern App a b     = Prim (FunName "app") [a, b]
pattern Cstr a b    = Prim (FunName "cstr") [a, b]
pattern Coe a b w x = Prim FCoe [a,b,w,x]
pattern FCoe        = FunName "coe"

pattern ConN0 a x   = Prim (ConName a 0) x
pattern ConN n x   <- Prim (ConName n _) x
pattern Type        = ConN0 "Type" []
pattern Sigma a b  <- ConN0 "Sigma" [a, Lam _ _ b] where Sigma a b = ConN0 "Sigma" [a, Lam Visible a{-todo: don't duplicate-} b]
pattern Unit        = ConN0 "Unit" []
pattern TT          = ConN0 "TT" []
pattern T2T a b     = ConN0 "T2" [a, b]
pattern T2 a b     <- ConN0 "T2C" [_, _, a, b] where T2 a b = ConN0 "T2C" [error "t21", error "t22", a, b]   -- TODO
pattern Empty       = ConN0 "Empty" []
pattern TInt        = ConN0 "Int" []


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

type GlobalEnv = Map.Map SName (Exp, Exp)

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

-- a b c d <a3 := d0> -> d0,c1,b2     ->   a b c d <d0 := a2> -> a2,c0,b1     -- 0:=2  up1E 2  (0,1,2)
cLet i (Var j) b | i > j = CLet j (Var (i-1)) $ substE j (Var (i-1)) $ up1E i b
cLet i a b = CLet i a b

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
{-
elet 0 _ (EBind _ _ xs) = xs
--elet i (downE 0 -> Just e) (EBind b x xs) = EBind b (substE (i-1) e x) (elet (i-1) e xs)
--elet i e (ELet j x xs) = mergeLets (error "ml") ELet substE (\i e -> elet i e xs) i e j x
elet i e xs = ELet i e xs
-}
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
        CLet j a b -> handleLet i j $ \i' j' -> cLet j' (g i' a) (g i' b)

upE i n e = iterate (up1E i) e !! n

substS j x = mapS (uncurry substE) ((+1) *** up1E 0) (j, x)
            (\(i, x) k -> case compare k i of GT -> SVar (k-1); LT -> SVar k; EQ -> STyped x)

substE i x = \case
    Var k -> case compare k i of GT -> Var $ k - 1; LT -> Var k; EQ -> x
    Bind h a b -> Bind h (substE i x a) (substE (i+1) (up1E 0 x) b)
    Prim s as  -> eval . Prim s $ map (substE i x) as
    CLet j a b -> mergeLets (Meta (cstr x a) $ up1E 0 b) cLet substE (\i j -> substE i j b) i x j a

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
app_ (Prim (ConName s n) xs) a = Prim (ConName s (n-1)) (xs ++ [a])
app_ f a = App f a

eval (App a b) = app_ a b
eval (Cstr a b) = cstr a b
eval (Coe a b c d) = coe a b c d
-- todo: elim
--eval x@(Prim (FunName "primFix") [_, _, f]) = app_ f x
eval (Prim p@(FunName "natElim") [a, z, s, ConN "Succ" [x]]) = s `app_` x `app_` (eval (Prim p [a, z, s, x]))
eval (Prim (FunName "natElim") [_, z, s, ConN "Zero" []]) = z
eval (Prim p@(FunName "finElim") [m, z, s, n, ConN "FSucc" [i, x]]) = s `app_` i `app_` x `app_` (eval (Prim p [m, z, s, i, x]))
eval (Prim (FunName "finElim") [m, z, s, n, ConN "FZero" [i]]) = z `app_` i
eval (Prim (FunName "eqCase") [_, _, f, _, _, ConN "Refl" []]) = error "eqC"
eval (Prim p@(FunName "Eq") [ConN "List" [a]]) = eval $ Prim p [a]
eval (Prim (FunName "Eq") [ConN "Int" []]) = Unit
eval (Prim (FunName "Monad") [ConN "IO" []]) = Unit
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
cstr (ConN a [x]) (ConN a' [x']) | a == a' = cstr x x'
--cstr a@(Prim aa [_]) b@(App x@Var{} _) | constr' aa = Cstr a b
cstr (Prim (ConName a n) xs) (App b@Var{} y) = T2T (cstr (Prim (ConName a (n+1)) (init xs)) b) (cstr (last xs) y)
cstr (App b@Var{} y) (Prim (ConName a n) xs) = T2T (cstr b (Prim (ConName a (n+1)) (init xs))) (cstr y (last xs))
cstr (App b@Var{} a) (App b'@Var{} a') = T2T (cstr b b') (cstr a a')     -- TODO: injectivity check
cstr (Prim a@ConName{} xs) (Prim a' ys) | a == a' = foldl1 T2T $ zipWith cstr xs ys
--cstr a b = Cstr a b
cstr a b = error ("!----------------------------! type error: \n" ++ show a ++ "\n" ++ show b) Empty

cstr' h x y e = EApp2 h (coe (up1E 0 x) (up1E 0 y) (Var 0) (up1E 0 e)) . EBind BMeta (cstr x y)

-------------------------------------------------------------------------------- simple typing

primitiveType te = \case
    CLit (LInt _)  -> TInt
    FunName s -> snd $ fromMaybe (error "can't found") $ Map.lookup s $ extractEnv te
    ConName s _ -> snd $ fromMaybe (error "can't found") $ Map.lookup s $ extractEnv te

expType_ te = \case
    Lam h t x -> Pi h t $ expType_ (EBind (BLam h) t te) x
    App f x -> app (expType_ te f) x
    Var i -> snd $ varType "C" i te
    Pi{} -> Type
    Prim t ts -> foldl app (primitiveType te t) ts
    Meta{} -> error "meta type"
    CLet{} -> error "let type"
  where
    app (Pi _ a b) x = substE 0 x b

-------------------------------------------------------------------------------- inference

inferN :: Env -> SExp -> Exp
inferN te exp = (if tr then trace ("infer: " ++ showEnvSExp te exp) else id) $ recheck__ te $ case exp of
    SLit l      -> focus te $ Prim (CLit l) []
    STyped e    -> expand focus te e
    SVar i      -> expand focus te $ Var i
    SGlobal s   -> expand focus te $ fst $ fromMaybe (error "can't found") $ Map.lookup s $ extractEnv te
    SApp  h a b -> inferN (EApp1 h te b) a
    SBind h a b -> inferN ((if h /= BMeta then CheckType Type else id) $ EBind1 h te $ (if isPi h then tyType else id) b) a

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

focus :: Env -> Exp -> Exp
focus env e = (if tr then trace $ "focus: " ++ showEnvExp env e else id) $ case env of
    EApp1 h@Visible te b
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
        te                -> maybe (focus te $ cLet i b e) (flip refocus' e) $ pull i te
      where
        pull i = \case
            EBind BMeta _ te | i == 0 -> Just te
            EBind h x te    -> EBind h <$> downE (i-1) x <*> pull (i-1) te
            ELet j b te     -> ELet (if j <= i then j else j-1) <$> downE i b <*> pull (if j <= i then i+1 else i) te
            _               -> Nothing
    EGlobal{} -> e
    _ -> error $ "focus: " ++ show env
  where
    refocus e (Bind BMeta x a) = focus (EBind BMeta x e) a
    refocus e (CLet i x a) = focus (ELet i x e) a
    refocus e a = focus e a

    refocus' e (Bind BMeta x a) = refocus' (EBind BMeta x e) a
    refocus' e (CLet i x a) = focus (ELet i x e) a
    refocus' e a = focus e a

-------------------------------------------------------------------------------- debug support

recheck :: Env -> Exp -> Exp
recheck e = if debug_light then recheck' e else id
recheck__ e = if debug then recheck' e else id

recheck' e x = recheck_ (checkEnv e) x

checkEnv :: Env -> Env
checkEnv = \case
    e@EGlobal{} -> e
    EBind h t e -> EBind h (recheck' e t) $ checkEnv e
    EBind1 h e b -> EBind1 h (checkEnv e) b
    EApp1 h e b -> EApp1 h (checkEnv e) b
    EApp2 h a e -> EApp2 h (recheck' e a) $ checkEnv e
    ELet i x e -> ELet i (recheck' e $ up1E i x) $ checkEnv e                -- __ <i := x>
    CheckType x e -> CheckType x $ checkEnv e

recheck_ :: Env -> Exp -> Exp
recheck_ te = \case
    Var k -> Var k
    Bind h a b -> Bind h (ch (h /= BMeta) (EBind1 h te (STyped b)) a) $ ch (isPi h) (EBind h a te) b
    App a b -> appf (recheck'' (EApp1 Visible te (STyped b)) a) (recheck'' (EApp2 Visible a te) b)
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
mkPrim False n t = f t
  where
    f (Pi h a b) = Lam h a $ f b
    f _ = eval $ Prim (FunName n) $ map Var $ reverse [0..arity t - 1]

arity :: Exp -> Int
arity (Pi _ _ b) = 1 + arity b
arity _ = 0

arityS (SPi _ _ x) = 1 + arityS x
arityS x = 0

finalize = \case
    Meta a t -> Lam Hidden a $ finalize t
    t -> checkMetas t

finalize' = \case
    Meta a t -> Pi Hidden a $ finalize' t
    t -> checkMetas t

checkMetas = \case
    x@Meta{} -> error $ "checkMetas: " ++ show x
    x@CLet{} -> error $ "checkMetas: " ++ show x
    Bind h a b -> Bind h (checkMetas a) (checkMetas b)
    x@Prim{} -> x
    x@Var{}  -> x

infer' t = gets $ (\env -> recheck (EEnd env) $ finalize $ inferN (EEnd env) t) . fst
checkP e = gets $ (\env -> recheck (EEnd env) $ finalize' $ checkN (EEnd env) e Type) . fst

addToEnv :: Monad m => String -> (Exp, Exp) -> AddM m ()
addToEnv s (x, t) = (if tr_light then trace (s ++ "  ::  " ++ showExp t) else id) $ modify $ Map.insert s (x, t) *** id

addToEnv_ s x = gets fst >>= \env -> addToEnv s (x, expType_ (EEnd env) x)
addToEnv' b s t = addToEnv s (mkPrim b s t, t)

handleStmt :: MonadFix m => Stmt -> AddM m ()
handleStmt (Let n t) = infer' t >>= addToEnv_ n
handleStmt (Primitive s t) = checkP t >>= addToEnv' False s
handleStmt (Data s ps t_ cs) = do
    let addParams ps t = foldr (uncurry SPi) t ps
    vty <- checkP (addParams ps t_)
    let

      pnum = length ps
      pnum' = length $ filter ((== Visible) . fst) ps
      cnum = length cs
      inum = arity vty - pnum

      dropArgs' (SPi _ _ x) = dropArgs' x
      dropArgs' x = x
      getApps (SApp h a b) = id *** (b:) $ getApps a
      getApps x = (x, [])

      arityh (SPi Hidden _ x) = 1 + arityh x
      arityh x = 0

      apps a b = foldl sapp (SGlobal a) b
      downTo n m = map SVar [n+m-1, n+m-2..n]

      pis 0 e = e
      pis n e = SPi Visible ws $ pis (n-1) e

      pis' (SPi h a b) e = SPi h a $ pis' b e
      pis' _ e = e

      ws = Wildcard $ Wildcard SType

    addToEnv' True s vty -- $ (({-pure' $ lams'' (rels vty) $ VCon cn-} error "pvcon", lamsT'' vty $ VCon cn), vty)

    let
      mkCon i (cs, ct_) = do
          ty <- checkP (addParams [(Hidden, x) | (Visible, x) <- ps] ct_)
          return (i, cs, ct_, ty, arityS ct_, arityS ct_ - arityh ct_)

    cons <- zipWithM mkCon [0..] cs

    mapM_ (\(_, s, _, t, _, _) -> addToEnv' True s t) cons

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
    caseTy <- checkP
            $ addParams [(Hidden, x) | (Visible, x) <- ps]
            $ SPi Visible tt
            $ addConstr 1 cons
            $ pis (1 + inum)
            $ foldl sapp (SVar $ cnum + inum + 1) $ downTo 1 inum ++ [SVar 0]

    addToEnv' False cn caseTy

env :: GlobalEnv
env = Map.fromList
        [ (,) "Int"  (TInt, Type)
        , (,) "Type" (Type, Type)
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

showExp :: Exp -> String
showExp = showDoc . expDoc

showEnvExp :: Env -> Exp -> String
showEnvExp e c = showDoc $ envDoc e $ epar <$> expDoc c

showEnvSExp :: Env -> SExp -> String
showEnvSExp e c = showDoc $ envDoc e $ epar <$> sExpDoc c

showDoc :: Doc -> String
showDoc = str . flip runReader [] . flip evalStateT (flip (:) <$> iterate ('\'':) "" <*> ['a'..'z'])

type Doc = StateT [String] (Reader [String]) PrecString

envDoc :: Env -> Doc -> Doc
envDoc x m = case x of
    EGlobal{}           -> m
    EBind1 h ts b       -> envDoc ts $ shLam (usedS 0 b) h m (sExpDoc b)
    EBind  h a ts       -> envDoc ts $ shLam True h (expDoc a) m
    EApp1 Visible ts b  -> envDoc ts $ shApp <$> m <*> sExpDoc b
    EApp2 Visible a ts  -> envDoc ts $ shApp <$> expDoc a <*> m
    ELet i x ts         -> envDoc ts $ shLet i (expDoc x) m
    CheckType t ts      -> envDoc ts $ shAnn False <$> m <*> expDoc t

expDoc :: Exp -> Doc
expDoc = \case
    Var k           -> shVar k
    App a b         -> shApp <$> expDoc a <*> expDoc b
    Bind h a b      -> shLam (usedE 0 b) h (expDoc a) (expDoc b)
    Cstr a b        -> shCstr <$> expDoc a <*> expDoc b
    Prim s xs       -> foldl shApp (shAtom $ showPrimN s) <$> mapM expDoc xs
    CLet i x e      -> shLet i (expDoc x) (expDoc e)

sExpDoc :: SExp -> Doc
sExpDoc = \case
    SVar k          -> shVar k
    SGlobal s       -> pure $ shAtom s
    SLit i          -> pure $ shAtom $ showLit i
    SAnn a b        -> shAnn False <$> sExpDoc a <*> sExpDoc b
    SApp h a b      -> shApp <$> sExpDoc a <*> sExpDoc b
    Wildcard t      -> shAnn True (shAtom "_") <$> sExpDoc t
    SBind h a b     -> shLam (usedS 0 b) h (sExpDoc a) (sExpDoc b)
    STyped e        -> expDoc e

showLit = \case
    LInt i -> show i
    LChar c -> show c

showPrimN :: FunName -> String
showPrimN = \case
    CLit i      -> show i
    ConName s _ -> s
    FunName s   -> s

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
        ann | used = shAnn False
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

id_test = slam $ SVar 0
id_test' = slam $ sapp id_test $ SVar 0
id_test'' = sapp id_test id_test
const_test = slam $ slam $ SVar 1

test xx = putStrLn $ length s `seq` ("result:\n" ++ s)
    where x = inferN (EEnd env) xx
          s = showEnvExp (EEnd env) x

test' n = test $ iterate (\x -> sapp x (slam $ SVar 0)) (slam $ SVar 0) !! n
test'' n = test $ iterate (\x -> sapp (slam $ SVar 0) x) (slam $ SVar 0) !! n

tr = False
tr_light = True
debug = False --True--tr
debug_light = True --False

parse s = 
    case P.runParser (whiteSpace lang >> {-many (parseStmt_ []-}parseITerm 0 [] >>= \ x -> eof >> return x) 0 "<interactive>" s of
      Left e -> error $ show e
      Right stmts -> do
        test stmts --runExceptT $ flip evalStateT (tenv, 0) $ mapM_ handleStmt stmts >> m

main = do
    let f = "prelude.inf"
        f' = "prelude.elab"
    s <- readFile f 
    case P.runParser (whiteSpace lang >> many (parseStmt_ []) >>= \ x -> eof >> return x) 0 f s of
      Left e -> error $ show e
      Right stmts -> runExceptT (flip runStateT (env, 0) $ mapM_ handleStmt stmts) >>= \case
            Left e -> putStrLn e
            Right (x, (s, _)) -> do
                putStrLn "----------------------"
                s' <- Map.fromList . read <$> readFile f'
                sequence_ $ map (either (error "xxx") id) $ Map.elems $ Map.unionWithKey check (Left <$> s') (Left <$> s)
--                writeFile f' $ show $ Map.toList s
                print x
  where
    check k (Left (x, t)) (Left (x', t'))
        | t /= t' = Right $ putStrLn $ "!!! type diff: " ++ k ++ "\n  old:   " ++ showExp t ++ "\n  new:   " ++ showExp t'
        | x /= x' = Right $ putStrLn $ "!!! def diff: " ++ k
        | otherwise = Right $ return ()

-------------------------------------------------------------------------------- utils

dropNth i xs = take i xs ++ drop (i+1) xs

