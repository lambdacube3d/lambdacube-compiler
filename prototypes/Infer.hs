{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

import Data.Monoid
import Data.Maybe
import Data.List
import Data.Char
import qualified Data.Map as Map

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Identity
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

pattern Nat n <- (ensureNat -> n)
ensureNat n = if n < 0 then error "negative" else n

-------------------------------------------------------------------------------- source data

data SExp
    = SV !Int
    | Global String
    | SStar
    | SAnn SExp SExp
    | SPi  SExp SExp
    | SLam SExp SExp
    | SApp SExp SExp
    | IInt Int
    | Wildcard SExp
  deriving (Eq, Show)

-------------------------------------------------------------------------------- destination data

data Exp
    = Star
    | Lam Exp Exp
    | Pi  Exp Exp
    | App Exp Exp
    | V !Int
    | Prim Pr [Exp]
  deriving (Eq, Show)

data Pr
    = Pr_ String (Additional Exp)
    | PInt Int
    | CstrN | UnitN | TTN | EmptyN | T2TN | T2N | CoeN
  deriving (Eq, Show)

pattern Pr a b = Pr_ a (Additional b)
pattern Cstr a b    = Prim CstrN [a, b]
pattern Unit        = Prim UnitN []
pattern TT          = Prim TTN []
pattern T2T a b     = Prim T2TN [a, b]
pattern T2 a b      = Prim T2N [a, b]
pattern Coe a b w x = Prim CoeN [a,b,w,x]
pattern Empty       = Prim EmptyN []

newtype Additional a = Additional a
instance Eq (Additional a) where _ == _ = True
instance Ord (Additional a) where _ `compare` _ = EQ
instance Show (Additional a) where show _ = ""

-------------------------------------------------------------------------------- constraints (intermediate)

data CExp
    = CLam Exp CExp
    | CLet Int Exp CExp
    | CExp Exp
  deriving (Show)

-------------------------------------------------------------------------------- environments

type LocalEnv = [EnvItem]
data EnvItem
    = ELet Int Exp
    | ELam Exp
    | ECLam Exp
    deriving (Show)

type GlobalEnv = Map.Map String CExp

-------------------------------------------------------------------------------- De Bruijn machinery

foldS f i = \case
    SV k     -> f i k
    SApp a b -> foldS f i a <> foldS f i b
    SLam a b -> foldS f i a <> foldS f (i+1) b
    SPi  a b -> foldS f i a <> foldS f (i+1) b
    Wildcard a -> foldS f i a
    _ -> mempty

foldE f i = \case
    V k     -> f i k
    App a b -> foldE f i a <> foldE f i b
    Lam a b -> foldE f i a <> foldE f (i+1) b
    Pi  a b -> foldE f i a <> foldE f (i+1) b
    Prim s as -> foldMap (foldE f i) as
    Star    -> mempty

countS (Nat i) = length . filter id . foldS (\i k -> [i == k]) i
countE (Nat i) = length . filter id . foldE (\i k -> [i == k]) i

mapS f = g 0 where
    g i = \case
        SV k     -> f i k
        SApp a b -> SApp <$> g i a <*> g i b
        SAnn a b -> SAnn <$> g i a <*> g i b
        SLam a b -> SLam <$> g i a <*> g (i+1) b
        SPi  a b -> SPi  <$> g i a <*> g (i+1) b
        Wildcard a -> Wildcard <$> g i a
        x        -> pure x

mapE :: (Applicative f) => (Int -> Int -> f Exp) -> Exp -> f Exp
mapE f = g 0 where
    g i = \case
        V k     -> f i k
        App a b -> app_ <$> g i a <*> g i b
        Lam a b -> Lam  <$> g i a <*> g (i+1) b
        Pi  a b -> Pi   <$> g i a <*> g (i+1) b
        Prim s as -> eval . Prim s <$> traverse (g i) as 
        Star    -> pure Star

upS t (Nat n) = runIdentity . mapS (\i k -> return $ SV $ if k >= i + t then k+n else k)
upE j (Nat n) = runIdentity . mapE (\i k -> return $ V  $ if k >= i + j then k+n else k)

downS (Nat t) = mapS $ \i k -> case compare k $ i + t of GT -> return $ SV $ k-1; LT -> return $ SV $ k; _ -> Nothing
downE (Nat t) = mapE $ \i k -> case compare k $ i + t of GT -> return $ V  $ k-1; LT -> return $ V  $ k; _ -> Nothing

upC :: Int -> Int -> CExp -> CExp
upC (Nat i0) (Nat n) = f i0 n where
  f i n = \case
    CLam a b -> CLam (upE i n a) $ f (i+1) n b
    CLet j a b
        | j >= i -> CLet (j+n) (upE i n a) $ f i n b
--        | j < i, Just a' <- downE (i-1) a -> CLet j a' <$> f (i-1) (substE j a' x) b
--        | otherwise -> Nothing
    CExp a -> CExp $ upE i n a

substE :: Int -> Exp -> Exp -> Exp
substE (Nat t) x = (runIdentity .) . mapE $ \i k -> return $ case compare k $ i + t of GT -> V $ k - 1; LT -> V k; EQ -> upE 0 i x

substC :: Int -> Exp -> CExp -> Maybe CExp
substC (Nat i0) x = f i0 x where
  f i x = \case
    CLam a b -> CLam (substE i x a) <$> f (i+1) (upE 0 1 x) b
    CLet j a b
        | j > i, Just a' <- downE i a -> CLet (j-1) a' <$> f i (substE (j-1) a' x) b
        | j < i, Just a' <- downE (i-1) a -> CLet j a' <$> f (i-1) (substE j a' x) b
        | otherwise -> Nothing
    CExp a -> pure $ CExp $ substE i x a

exch :: Int -> Exp -> Exp
exch (Nat n) = (runIdentity .) . mapE $ \i k -> return $ V $ case () of
    _ | k == i + n -> i
      | k <  i + n && k >= i -> k + 1
      | otherwise -> k

-------------------------------------------------------------------------------- De Bruijn #2

type LiftInfo = [Maybe (Int, Exp)]

bind :: MT CExp -> (LiftInfo -> Exp -> MT CExp) -> MT CExp
bind x g = x >>= ff [] where
    ff n (CLam t f)   = clam t $ ff (Nothing: n) f
    ff n (CLet i x e) = clet i x $ ff (Just (i, x): n) e
    ff n (CExp a)     = g n a

liftS q = foldr (\x n -> maybe (upS q 1) (\(i, _) -> fromJust . downS (i + q)) x . n) id
liftE q = foldr (\x n -> maybe (upE q 1) (\(i, x) -> substE (i+q) (upE 0 q x)) x . n) id

withItem b m = local (id *** (b:)) m

binder lam t m = withItem (ELam t) m >>= ff 0 t
  where
    ff n lt = \case
        CLam (downE n -> Just t) f -> clam t $ ff (1 + n) (upE 0 1 lt) f
        CLet i x e
            | i > n, Just x' <- downE n x -> clet (i-1) x' $ ff n (substE (i-1) x' lt) e
            | i < n, Just x' <- downE (n-1) x -> clet i x' $ ff (n-1) (substE i x' lt) e
        CExp a -> return $ CExp $ lam lt $ exch n a
--        z -> CCLam lt $ exchC n z
        z -> asks snd >>= \env -> error $ "can't infer type: " ++ show (n, lt) ++ "\n" ++ ppshow'' (ELam lt: env) ({-exch n-} z)

clet :: Int -> Exp -> MT CExp -> MT CExp
clet i x m = withItem (ELet i x) $ CLet i x <$> m

clam :: Exp -> MT CExp -> MT CExp
clam t m = asks snd >>= \te -> cLam te t <$> withItem (ECLam t) m   where

    cLam te t (kill (ECLam t: te) 0 -> Just e) = e
    cLam te Unit (substC 0 TT -> Just x) = x
    cLam te (T2T x y) e
        | Just e' <- substC 0 (T2 (V 1) (V 0)) $ upC 0 2 e = cLam te x $ cLam (ECLam x: te) (upE 0 1 y) e'
    cLam te (Cstr a b) y
        | Just i <- cst te a, Just j <- cst te b, i < j, Just e <- downE i b, Just x <- substC (i+1) (upE 0 1 e) y = CLet i e $ cunit x
        | Just i <- cst te b, Just e <- downE i a, Just x <- substC (i+1) (upE 0 1 e) y = CLet i e $ cunit x
        | Just i <- cst te a, Just e <- downE i b, Just x <- substC (i+1) (upE 0 1 e) y = CLet i e $ cunit x
    cLam te t e = CLam t e

    cst te = \case
        V i | fst $ varType "X" i te -> Just i
        _ -> Nothing

    cunit (substC 0 TT -> Just x) = x
    cunit x = CLam Unit x

    kill te i = \case
        CLam t'@(downE i -> Just t) (kill (ECLam t': te) (i+1) -> Just e) -> Just $ CLam t e
        (pull te i -> Just (_, e)) -> Just e
        _ -> Nothing

    pull te i = \case
        CLet j z y
            | j == i   -> Just (z, y)
            | j > i, Just (x, e) <- pull (ELet j z: te) i y   -> Just (upE (j-1) 1 x,  CLet (j-1) (substE i x z) e)
            | j < i, Just (x, e) <- pull (ELet j z: te) i y   -> Just (upE j 1 x,  CLet j (substE i x z) e)
        -- CLet j (V i') y | i' == i   -- TODO
        CLam t (pull (ECLam t: te) (i+1) -> Just (downE 0 -> Just x, e)) -> Just (x, cLam te (substE i x t) e)
        x -> Nothing

-------------------------------------------------------------------------------- reduction

infixl 1 `app_`

app_ :: Exp -> Exp -> Exp
app_ (Lam _ x) a = substE 0 a x
app_ f a = App f a

eval (Cstr a b) = cstr a b
eval (Coe a b c d) = coe a b c d
--eval x@(Prim (Pr "primFix" _) [_, _, f]) = app_ f x
eval (Prim p@(Pr "natElim" _) [a, z, s, Prim (Pr "Succ" _) [x]]) = s `app_` x `app_` (eval (Prim p [a, z, s, x]))
eval (Prim (Pr "natElim" _) [_, z, s, Prim (Pr "Zero" _) []]) = z
eval (Prim p@(Pr "finElim" _) [m, z, s, n, Prim (Pr "FSucc" _) [i, x]]) = s `app_` i `app_` x `app_` (eval (Prim p [m, z, s, i, x]))
eval (Prim (Pr "finElim" _) [m, z, s, n, Prim (Pr "FZero" _) [i]]) = z `app_` i
eval (Prim (Pr "eqCase" _) [_, _, f, _, _, Prim (Pr "Refl" _) _]) = error "eqC"
eval (Prim p@(Pr "Eq" _) [Prim (Pr "List" _) [a]]) = eval $ Prim p [a]
eval (Prim (Pr "Eq" _) [Prim (Pr "Int" _) _]) = Unit
eval (Prim (Pr "Monad" _) [Lam _ (Prim (Pr "IO" _) [V 0])]) = Unit
eval x = x

-- todo
coe _ _ TT x = x
coe a b c d = Coe a b c d

cstr a b | a == b = Unit
--cstr (App x@(V j) y) b@(V i) | j /= i, Nothing <- downE i y = cstr x (Lam (expType' y) $ upE 0 1 b)
cstr a@V{} b = Cstr a b
cstr a b@V{} = Cstr a b
--cstr (App x@V{} y) b@Prim{} = cstr x (Lam (expType' y) $ upE 0 1 b)
--cstr b@Prim{} (App x@V{} y) = cstr (Lam (expType' y) $ upE 0 1 b) x
cstr (Pi a (downE 0 -> Just b)) (Pi a' (downE 0 -> Just b')) = T2T (cstr a a') (cstr b b') 
cstr (Prim a [x]) (Prim a' [x']) | a == a' && constr' a = cstr x x'
--cstr a@(Prim aa [_]) b@(App x@V{} _) | constr' aa = Cstr a b
cstr (Prim a [x]) (App b@V{} y) | constr' a = T2T (cstr (Lam (expType' x) $ Prim a [V 0]) b) (cstr x y)
cstr (Prim a [x, y]) (Prim a' [x', y']) | a == a' && constr' a = T2T (cstr x x') (cstr y y')
cstr (Prim a [x, y, z]) (Prim a' [x', y', z']) | a == a' && constr' a = T2T (cstr x x') (T2T (cstr y y') (cstr z z'))
cstr a b = trace ("---------- type error: \n" ++ show a ++ "\n" ++ show b) Empty

constr' (Pr s _) = constr s

-- todo
constr n = n `elem` ["List", "Bool'", "True'", "False'", "Nil'", "Cons'", "Int", "Nat", "Vec", "Nil", "Cons", "Eq", "Refl", "Nat", "Zero", "Succ", "Fin", "FZero", "FSucc", "MonadD", "IO"]

-------------------------------------------------------------------------------- simple typing

primitiveType = \case
    Pr _ t  -> t
    PInt _  -> Prim (Pr "Int" Star) []
    CstrN   -> Pi (error "cstrT0") $ Pi (error "cstrT1") Star       -- todo
    UnitN   -> Star
    TTN     -> Unit
    EmptyN  -> Star
    T2TN    -> Pi Star $ Pi Star Star
    T2N     -> Pi Star $ Pi Star $ T2T (V 1) (V 0)
    CoeN    -> Pi Star $ Pi Star $ Pi (Cstr (V 1) (V 0)) $ Pi (V 2) (V 2)  -- forall a b . (a ~ b) => a -> b

varType :: String -> Int -> LocalEnv -> (Bool, Exp)
varType err n' env = traceShow' (n', env) $ varType_ n' env where
    varType_ n (ELet i x: es)
        | n < i     =  id *** substE i x $ varType_ n es
        | otherwise =  id *** substE i x $ varType_ (n+1) es
    varType_ 0 (ELam t: _) = (False, upE 0 1 t)
    varType_ 0 (ECLam t: _) = (True, upE 0 1 t)
    varType_ n (_: es) = id *** upE 0 1 $ varType_ (n-1) es
    varType_ n [] = error $ "varType: " ++ err ++ "\n" ++ show n' ++ "\n" ++ show env

expType = \case
    Lam t x -> Pi t <$> withItem (ELam t) (expType x)
    App f x -> app <$> expType f <*> pure x
    V i -> asks $ snd . varType "C" i . snd
    Star -> return Star
    Pi{} -> return Star
    Prim t ts -> return $ foldl app (primitiveType t) ts
  where
    app (Pi a b) x = substE 0 x b

-- todo
expType' = \case
    Prim t ts -> foldl (\(Pi _ b) x -> substE 0 x b) (primitiveType t) ts

-------------------------------------------------------------------------------- inference

type MT = ReaderT (GlobalEnv, LocalEnv) (Except String)

infer = infer_ Nothing
check = infer_ . Just

infer_ :: Maybe Exp -> SExp -> MT CExp
infer_ mt aa = case aa of
    SStar   -> return' $ CExp Star
    IInt i  -> return' $ CExp $ Prim (PInt i) []
    SV i    -> return' $ CExp $ V i
    Wildcard t -> ch' $ infer t `bind` \_ t -> clam t $ return $ CExp $ V 0
    Global s -> ch' $ asks (Map.lookup s . fst) >>= maybe (throwError $ s ++ " is not defined") return
    SAnn a b -> ch $ infer b `bind` \nb b -> check b (liftS 0 nb a)
    SPi  a b -> ch $ check Star a `bind` \na a -> binder Pi a $ check Star $ liftS 1 na b
    SLam a b | Just (Pi x y) <- mt -> checkSame x a `bind` \nx x -> binder Lam x $ check (liftE 1 nx y) (liftS 1 nx b)
    SLam a b -> ch $ check Star a `bind` \na a -> binder Lam a $ infer $ liftS 1 na b
    SApp a b -> ch $ infer a `bind` \na a -> expType a >>= \case
        Pi x _ -> check x (liftS 0 na b) `bind` \nb b' -> return $ CExp $ app_ (liftE 0 nb a) b'
        ta -> infer (liftS 0 na b) `bind` \nb b -> expType b >>= \tb -> case mt of
--            Just t -> 
            _ -> 
                let
                nb' = Nothing: nb
                nb'' = Nothing: nb'
                in clam Star $ clam (cstr (liftE 0 nb' ta) $ Pi (upE 0 1 tb) (V 1)) $ return $
                    CExp $ coe (liftE 0 nb'' ta) (Pi (upE 0 2 tb) (V 2)) (V 0) (liftE 0 nb'' a) `app_` upE 0 2 b
  where
    return' = ch . return
    ch z = maybe (trs "infer" aa mt z) (\t -> trs "infer" aa mt $ trs "infer" aa Nothing z `bind` \nz z -> expType z >>= \tz -> clam (cstr (liftE 0 nz t) tz) $ return $ CExp $ upE 0 1 z) mt
    ch' z = maybe z (\t -> z `bind` \nz z -> expType z >>= \tz -> clam (cstr (liftE 0 nz t) tz) $ return $ CExp $ upE 0 1 z) mt

-- todo
checkSame :: Exp -> SExp -> MT CExp
checkSame a (Wildcard SStar) = expType a >>= \case
    Star -> return $ CExp a
checkSame a b = error $ "checkSame: " ++ show (a, b)

-------------------------------------------------------------------------------- debug support

return' :: CExp -> MT CExp
return' x = if debug then apps x >>= \y -> evv y $ return x else return x

apps :: CExp -> MT (LocalEnv, Exp)
apps x = asks $ add x . snd
add (CLam t e) env = add e (ECLam t: env)
add (CLet i t e) env = add e (ELet i t: env)
add (CExp e) env = (env, e)

addEnv :: LocalEnv -> CExp -> CExp
addEnv env x = foldr f x env where
    f (ELam t) x = CLam t x
    f (ECLam t) x = CLam t x
    f (ELet i t) x = CLet i t x

evv (env, e) y = sum [case t of Star -> 1; _ -> error $ "evv: " ++ ppshow'' e (CExp x) ++ "\n"  ++ ppshow'' e (CExp t) | (e, x, t) <- checkEnv env] `seq` 
    (length $ show $ checkInfer env e) `seq` y

checkEnv [] = []
checkEnv (ELam t: e) = (e, t, checkInfer e t): checkEnv e
checkEnv (ECLam t: e) = (e, t, checkInfer e t): checkEnv e
checkEnv (ELet i t: e) = (e, t', checkInfer e (checkInfer e t')): checkEnv e  where t' = upE i 1 t

recheck :: CExp -> CExp
recheck e = length (show $ checkInfer te e') `seq` e  where (te, e') = add e []

checkInfer lu x = flip runReader [] (infer x)  where
    infer = \case
        Pi a b -> ch Star a !>> local (a:) (ch Star b) !>> return Star
        Star -> return Star
        V k -> asks $ \env -> ([upE 0 (k + 1) e | (k, e) <- zip [0..] env] ++ [upE 0 (length env) $ snd $ varType "?" i lu | i<- [0..]]) !! k
        Lam a b -> ch Star a !>> Pi a <$> local (a:) (infer b)
        App a b -> ask >>= \env -> appf env <$> infer a <*> infer' b
        Prim s as -> ask >>= \env -> foldl (appf env) (primitiveType s) <$> mapM infer' as
    infer' a = (,) a <$> infer a
    appf _ (Pi x y) (v, x') | x == x' = substE 0 v y
    appf en a (_, b) = error $ "recheck:\n" ++ show a ++ "\n" ++ show b ++ "\n" ++ show en ++ "\n" ++ ppshow'' lu (CExp x)
    ch x e = infer e >>= \case
        z | z == x -> return ()
          | otherwise -> error $ "recheck':\n" ++ show z ++ "\n" ++ show x

infixl 1 !>>
a !>> b = a >>= \x -> x `seq` b

-------------------------------------------------------------------------------- statements

data Stmt
    = Let String SExp
    | Data String [SExp] SExp [(String, SExp)]
    | Primitive String SExp
    deriving Show

type AddM m = StateT (GlobalEnv, Int) (ExceptT String m)

expType'' :: CExp -> CExp
expType'' e = either error id . runExcept . flip runReaderT (mempty :: GlobalEnv, [] :: LocalEnv) $ apps e >>= \(ev, e) -> local (id *** (ev ++)) $ addEnv (reverse ev) . CExp <$> expType e

addToEnv :: Monad m => String -> CExp -> AddM m ()
addToEnv s x = trace' (s ++ "     " ++ pshow (expType'' x)) $ modify $ Map.insert s x *** id

tost m = gets fst >>= \e -> lift $ mapExceptT (return . runIdentity) $ flip runReaderT (e, []) m

toExp (CExp a) = a
toExp (CLam Star e) = Lam Star $ toExp e
toExp e = error $ "toExp:\n" ++ pshow e

infer' t = (if debug_light then recheck else id) <$> infer t

handleStmt :: MonadFix m => Stmt -> AddM m ()
handleStmt (Let n t) = tost (infer' t) >>= addToEnv n
handleStmt (Primitive s t) = tost (infer' t) >>= addToEnv s . CExp . mkPrim s . toExp


mkPrim n t = f 0 t
  where
    f i (Pi a b) = Lam a $ f (i+1) b
    f i _ = Prim (Pr n t) $ map V [i-1, i-2 .. 0]

env :: GlobalEnv
env = Map.fromList
        [ (,) "Int" $ CExp $ Prim (Pr "Int" Star) []
        ]

-------------------------------------------------------------------------------- parser

slam a = SLam (Wildcard SStar) a
sapp = SApp
sPi _ = SPi
sApp _ = SApp
sLam _ = SLam

lang = makeTokenParser (haskellStyle { identStart = letter <|> P.char '_',
                                       reservedNames = ["forall", "let", "data", "primitive", "fix", "Type"] })

parseType vs = (reserved lang "::" *> parseCTerm 0 vs) <|> return (Wildcard SStar)
parseType' vs = (reserved lang "::" *> parseCTerm 0 vs)
typedId vs = (,) <$> identifier lang <*> parseType vs

type Pars = CharParser Int

data Vis = Hidden | Visible | Irr

parseStmt_ :: [String] -> Pars Stmt
parseStmt_ e = do
     do Let <$ reserved lang "let" <*> identifier lang <* reserved lang "=" <*> parseITerm 0 e
 <|> do uncurry Primitive <$ reserved lang "primitive" <*> typedId []
 <|> do
      x <- reserved lang "data" *> identifier lang
      let params vs = option [] $ parens lang (typedId vs) >>= \xt -> (xt:) <$> params (fst xt: vs)
      (nps, ts) <- unzip <$> params []
      let parseCons = option [] $ (:) <$> typedId nps <*> option [] (reserved lang ";" *> parseCons)
      Data x ts <$> parseType nps <* reserved lang "=" <*> parseCons

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
     {-do (ILam Cstr SStar $ ILam Cstr (Bound 0) (Bound 0)) <$ reserved lang "_"
 <|> -}do SStar <$ reserved lang "Type"
 <|> do IInt . fromIntegral <$ P.char '#' <*> natural lang
 <|> do toNat <$> natural lang
 <|> do reserved lang "fix"
        i <- P.getState
        P.setState (i+1)
        return $ sApp Hidden (Global "primFix") (IInt i)
 <|> parseILam e
 <|> do identifier lang >>= \case
            "_" -> return $ Wildcard (Wildcard SStar)
            x -> return $ maybe (Global x) SV $ findIndex (== x) e
 <|> parens lang (parseITerm 0 e)
  
parseCTerm :: Int -> [String] -> Pars SExp
parseCTerm 0 e = parseLam e <|> parseITerm 0 e
parseCTerm p e = try (parens lang $ parseLam e) <|> parseITerm p e
  
parseLam :: [String] -> Pars SExp
parseLam e = do
    xs <- reservedOp lang "\\" *> many1 (identifier lang) <* reservedOp lang "->"
    t <- parseCTerm 0 (reverse xs ++ e)
    return $ iterate slam t !! length xs

parseILam :: [String] -> Pars SExp
parseILam e = do
    reservedOp lang "\\"
    (fe, ts) <- rec (e, []) <|> xt Visible (e, [])
    reserved lang "->"
    t' <- parseITerm 0 fe
    return $ foldl (\p (r, t) -> sLam r t p) t' ts
 where
    rec b = (parens lang (xt Visible b) <|> braces lang (braces lang (xt Irr b) <|> xt Hidden b)) >>= \x -> option x $ rec x
    xt r (e, ts) = ((:e) *** (:ts) . (,) r) <$> typedId e

toNat 0 = Global "Zero"
toNat n = sapp (Global "Succ") $ toNat (n-1)

-------------------------------------------------------------------------------- pretty print

newVar = gets head <* modify tail
addVar v = local (v:)

pshow :: CExp -> String
pshow = snd . flip runReader [] . flip evalStateT vars . showCExp

vars = flip (:) <$> iterate ('\'':) "" <*> ['a'..'z']

infixl 4 <**>

m <**> n = StateT $ \s -> (\(a, _) (b, _) -> (a b, error "<**>")) <$> flip runStateT s m <*> flip runStateT s n

trs s a c f = if tr then   asks snd >>= \env -> f >>= \x -> trace ("# " ++ ppshow' env a c x) $ return' x else f >>= return'

ppshow'' :: LocalEnv -> CExp -> String
ppshow'' e c = flip runReader [] . flip evalStateT vars $ showEnv e $ (\(_, s') -> "\n    " ++ s') <$> showCExp c

ppshow' e s t c = flip runReader [] . flip evalStateT vars $ showEnv e $ (\(_, s) mt (_, s') -> "\n    " ++ s ++ maybe "" (\(_, t) -> "   ::  " ++ t) mt ++ "\n    " ++ s') <$> showSExp s <**> traverse showExp t <**> showCExp c

showCExp = \case
    CLam t e -> newVar >>= \i -> lam i "\\" ("->") "::" (cpar True) <$> showExp t <*> addVar i (f e)
    CLet j t e -> asks (ind "pshow" j) >>= \j' -> local (dropNth j) $ lam j' "\\" ("->") ":=" (cpar True) <$> showExp t <*> f e
    CExp e -> exp <$> showExp e
  where
    f = showCExp
    exp (i, s) = (i, s) 
    lam i s s' s'' p (_, s1) (_, s2) = (1, s ++ p (i ++ " " ++ s'' ++ " " ++ s1) ++ " " ++ s' ++ " " ++ s2)

showEnv :: LocalEnv -> StateT [String] (Reader [String]) String -> StateT [String] (Reader [String]) String
showEnv en m = f $ reverse en
  where
    f = \case
        [] -> m
        (ELam t: ts) -> newVar >>= \i -> lam i "\\" ("->") "::" (par True) <$> showExp t <*> addVar i (f ts)
        (ECLam t: ts) -> newVar >>= \i -> lam i "\\" ("->") "::" (cpar True) <$> showExp t <*> addVar i (f ts)
        (ELet i t: ts) -> asks (ind "showEnv" i) >>= \i' -> local (dropNth i) $ lam i' "\\" ("->") ":=" (cpar True) <$> showExp t <*> f ts

    lam i s s' s'' p (_, s1) s2 = s ++ p (i ++ " " ++ s'' ++ " " ++ s1) ++ " " ++ s' ++ " " ++ s2

showExp :: Exp -> StateT [String] (Reader [String]) (Int, String)
showExp = \case
    Star -> pure $ atom "Type"
    Cstr a b -> cstr <$> f a <*> f b
    V k -> asks $ \env -> atom $ if k >= length env || k < 0 then "V" ++ show k else env !! k
    App a b -> (.$) <$> f a <*> f b
    Lam t e -> newVar >>= \i -> lam i "\\" ("->") (par True) <$> f t <*> addVar i (f e)
    Pi t e | countE 0 e == 0 -> arr ("->") <$> f t <*> addVar "?" (f e)
    Pi t e -> newVar >>= \i -> lam i "" ("->") (par True) <$> f t <*> addVar i (f e)
    Prim s xs -> ff (atom $ sh s) <$> mapM f xs
  where
    f = showExp
    ff x [] = x
    ff x (y:ys) = ff (x .$ y) ys
    atom s = (0, s)
    lam i s s' p (_, s1) (_, s2) = (1, s ++ p (i ++ " :: " ++ s1) ++ " " ++ s' ++ " " ++ s2)
    (i, x) .$ (j, y) = (2, par (i == 1 || i > 2) x ++ " " ++ par (j == 1 || j >= 2) y)
--        (i, x) ..$ (j, y) = (2, par (i == 1 || i > 2) x ++ " " ++ brace True y)
    arr s (i, x) (j, y) = (3, par (i == 1 || i >= 3) x ++ " " ++ s ++ " " ++ par (j == 1 || j > 3) y)
    (i, x) `cstr` (j, y) = (4, par (i == 1 || i >= 4) x ++ " ~ " ++ par (j == 1 || j >= 4) y)

    sh = \case
        PInt i -> show i
        Pr s _ -> s
        x -> show x

showSExp :: SExp -> StateT [String] (Reader [String]) (Int, String)
showSExp = \case
    SStar -> pure $ atom "*"
    SV k -> asks $ \env -> atom $ if k >= length env || k < 0 then "V" ++ show k else env !! k
    SApp a b -> (.$) <$> f a <*> f b
    SLam t e -> newVar >>= \i -> lam i "\\" ("->") (par True) <$> f t <*> addVar i (f e)
    SPi t e | countS 0 e == 0 -> arr ("->") <$> f t <*> addVar "?" (f e)
    SPi t e -> newVar >>= \i -> lam i "" ("->") (par True) <$> f t <*> addVar i (f e)
    Global s -> pure $ atom s
    SAnn a b -> sann <$> f a <*> f b
    IInt i -> pure $ atom $ show i
    Wildcard SStar -> pure $ atom "_"
    Wildcard t -> sann (atom "_") <$> f t
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

id_test = slam $ SV 0
id_test' = slam $ sapp (slam $ SV 0) $ SV 0
id_test'' = sapp (slam $ SV 0) $ slam $ SV 0
const_test = slam $ slam $ SV 1

test x = putStrLn $ either id pshow $ runExcept $ flip runReaderT mempty $ infer x

test' n = test $ iterate (\x -> sapp x (slam $ SV 0)) (slam $ SV 0) !! n
test'' n = test $ iterate (\x -> sapp (slam $ SV 0) x) (slam $ SV 0) !! n

tr = False
debug = False --True--tr
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

