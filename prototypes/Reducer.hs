-- efficient lazy evaluation for lambda calculus with constructors and delta functions
-- eliminators are used instead of case expressions
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
import Control.Monad.ST
import Control.Monad.Fix
import System.Environment
import Data.STRef

--------------------------------------------------------------------------------

data Exp s
    = Ref !(STRef s (Exp s))
    | Lam !(Exp s -> Exp s)
    | App (Exp s) (Exp s)
    | Fun !FunName [Exp s]
    | Con !ConName [Exp s]
    | Int !Int
    | LetRec (Exp s -> Exp s) (Exp s -> Exp s)

infixl 1 `App`

type VarName = Int
data ConName = T2 | CTrue | CFalse | Nil | Cons
    deriving (Eq, Show)
data FunName = ElimT2 | ElimBool | ElimList | Feq | GEq | LEq | NEq | Mod | Add | Sub | ISqrt | Undef
    deriving (Eq, Show)

instance Show (Exp s) where
    show = \case
        Int i -> show i

--------------------------------------------------------------------------------

pureEval :: (forall s . Exp s) -> String
pureEval e = runST (show <$> evalN e)

-- eval to some normal form (not needed in the current test case)
evalN :: Exp s -> ST s (Exp s)
evalN x = eval x >>= \case
    Con f es -> Con f <$> mapM evalN es
    c -> return c

-- eval to weak head normal form
eval :: Exp s -> ST s (Exp s)
eval = \case
    App (Lam f) x -> eval . f =<< addHeap x     -- optimization
    App l x -> eval l >>= \(Lam f) -> eval . f =<< addHeap x
    Fun ElimT2 (t: f:_) -> eval t >>= eval . \(Con _ (x: y:_)) -> f `App` x `App` y
    Fun ElimList (xs: f: g:_) -> eval xs >>= eval . \case
        Con Nil _ -> f
        Con Cons (x: y:_) -> g `App` x `App` y
    Fun ElimBool (xs: f: g:_) -> eval xs >>= eval . \case
        Con CFalse _ -> f
        Con CTrue _ -> g
    Fun f es -> case f of
        ISqrt -> mapM (eval) es >>= \(Int n:_) -> return $ Int (iSqrt n)
        Mod -> ff mod es
        Add -> ff (+) es
        Sub -> ff (-) es
        Feq -> gg (==) es
        NEq -> gg (/=) es
        LEq -> gg (<=) es
        GEq -> gg (>=) es
        f -> error $ "eval: " ++ show f
      where
        ff g (a: b:_) = do
            Int x <- eval a
            Int y <- eval b
            return $ Int $ g x y
        gg g (a: b:_) = do
            Int x <- eval a
            Int y <- eval b
            return $ if g x y then true else false
    Ref i -> do
        x <- readSTRef i
        if reduced x then return x else do          -- optimization
            -- writeSTRef i $ error "cycle in spine"    -- optional test
            z <- eval x
            writeSTRef i z
            return z
    LetRec f g -> eval . g =<< mfix (fmap Ref . newSTRef . f)
    x -> return x

reduced = \case
    App{} -> False
    Fun{} -> False
    _ -> True

addHeap :: Exp s -> ST s (Exp s)
addHeap e = if reduced e then return e else Ref <$> newSTRef e

iSqrt :: Int -> Int
iSqrt = round . sqrt . fromIntegral

-------------------------------------------------------------------------------- example codes

infixl 1 @@, @@.

(@@), (@@.) :: Exp s -> Exp s -> Exp s
(@@) = App
(@@.) = (@@)

f0 s = Fun s []
f1 s = Lam $ \v0 -> Fun s [v0]
f2 s = Lam $ \v0 -> Lam $ \v1 -> Fun s [v0, v1]
f3 s = Lam $ \v0 -> Lam $ \v1 -> Lam $ \v2 -> Fun s [v0, v1, v2]
c0 s = Con s []
c1 s = Lam $ \v0 -> Con s [v0]
c2 s = Lam $ \v0 -> Lam $ \v1 -> Con s [v0, v1]
c3 s = Lam $ \v0 -> Lam $ \v1 -> Lam $ \v2 -> Con s [v0, v1, v2]

undef = f0 Undef

-- tuples
t2 = c2 T2
elimT2 = f2 ElimT2

-- booleans
false = c0 CFalse
true = c0 CTrue
elimBool = f3 ElimBool
and' = Lam $ \v0 -> Lam $ \v1 -> elimBool @@ v0 @@ false @@ v1

-- lists
nil = c0 Nil
cons = c2 Cons
elimList = f3 ElimList

-- integers
zero = Int 0
one = Int 1
two = Int 2
add = f2 Add
sub = f2 Sub
eq = f2 Feq
neq = f2 NEq
leq = f2 LEq
geq = f2 GEq
mod' = f2 Mod
iSqrt' = f1 ISqrt

nthPrime n =
    LetRec (\r -> Lam $ \v0 -> cons @@. v0 @@. (r @@ (add @@. one @@. v0))) $ \from ->
    LetRec (\r -> Lam $ \v0 -> Lam $ \v1 -> Lam $ \v2 ->
        elimList @@. v2 @@. v1 @@. (Lam $ \v3 -> Lam $ \v4 -> v0 @@ v3 @@ (r @@ v0 @@ v1 @@ v4))) $ \foldr' ->
    LetRec (\r -> Lam $ \v0 -> Lam $ \v1 ->
        elimList @@. v1 @@. nil @@. (Lam $ \v2 -> Lam $ \v3 -> elimBool @@. (v0 @@ v2) @@. nil @@. (cons @@. v2 @@. (r @@ v0 @@ v3)))) $ \takeWhile' ->
    LetRec (\r -> Lam $ \v0 -> Lam $ \v1 ->
        elimList @@. v0 @@. undef @@. (Lam $ \v2 -> Lam $ \v3 -> elimBool @@. (eq @@. v1 @@. zero) @@. (r @@ v3 @@ (sub @@. v1 @@. one)) @@. v2)) $ \nth ->
    let
        map_ = Lam $ \v0 -> foldr' @@ (Lam $ \v1 -> Lam $ \v2 -> cons @@. (v0 @@ v1) @@. v2) @@ nil
        and'' = foldr' @@ and' @@ true
        filter' = Lam $ \v0 -> foldr' @@ (Lam $ \v1 -> Lam $ \v2 -> elimBool @@. (v0 @@ v1) @@. v2 @@. (cons @@. v1 @@. v2)) @@ nil

    in LetRec (\r -> cons @@. Int 2 @@. (cons @@. Int 3 @@. (filter' @@ (Lam $ \v0 -> and'' @@ (map_ @@. (Lam $ \v1 -> neq @@. zero @@. (mod' @@. v0 @@. v1)) @@ (takeWhile' @@ (geq @@ (iSqrt' @@. v0)) @@ r))) @@ (from @@ Int 5)))) $ \primes ->
        nth @@ primes @@ Int n

main = getArgs >>= \case
    [n] -> putStrLn $ pureEval $ nthPrime $ read n
    [_, n] -> print $ primes !! read n

primes = 2:3: filter (\n -> and $ map (\p -> n `mod` p /= 0) (takeWhile (<= iSqrt n) primes)) [5..]

