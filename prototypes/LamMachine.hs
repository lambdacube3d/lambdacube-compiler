{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module LamMachine where

import Data.List
import Data.Maybe
import Control.Arrow
import Control.Category hiding ((.), id)
--import Debug.Trace

import LambdaCube.Compiler.Pretty

--------------------------------------------------------------------- data structures

data Exp_
    = Var_
    | Int_ !Int     -- ~ constructor with 0 args
    | Lam_ Exp
    | Con_ String Int [Exp]
    | Case_ [String]{-for pretty print-} Exp [Exp]  -- --> simplify
    | Op1_ !Op1 Exp
    | Op2_ !Op2 Exp Exp

data Op1 = YOp | Round
    deriving (Eq, Show)

data Op2 = AppOp | SeqOp | Add | Sub | Mod | LessEq | EqInt
    deriving (Eq, Show)

-- cached and compressed free variables set
type FV = [Int]

data Exp = Exp !FV Exp_

-- state of the machine
data MSt = MSt Exp Exp [Exp]

--------------------------------------------------------------------- toolbox: pretty print

instance PShow Exp where
    pShow e@(Exp _ x) = case e of -- shUps' u t $ case Exp [] t x of
        Var i       -> DVar i
        Let a b     -> shLet (pShow a) $ pShow b
        App a b     -> DApp (pShow a) (pShow b)
        Seq a b     -> DOp "`seq`" (Infix 1) (pShow a) (pShow b)
        Lam e       -> shLam $ pShow e
        Con s i xs  -> foldl DApp (text s) $ pShow <$> xs
        Int i       -> pShow i
        Op1 o x     -> text (show o) `DApp` pShow x
        Op2 EqInt x y -> DOp "==" (Infix 4) (pShow x) (pShow y)
        Op2 Add x y -> DOp "+" (InfixL 6) (pShow x) (pShow y)
        Op2 o x y   -> text (show o) `DApp` pShow x `DApp` pShow y
        Y e         -> "Y" `DApp` pShow e
        Case cn e xs -> DPreOp (-20) (ComplexAtom "case" (-10) (pShow e) (SimpleAtom "of"))
                        $ foldr1 DSemi [DArr_ "->" (text a) (pShow b) | (a, b) <- zip cn xs]

instance PShow MSt where
    pShow (MSt as b bs) = case foldl (flip (:)) (DBrace (pShow b): [pShow x |  x <- bs]) $ [pShow as] of
        x: xs -> foldl (flip shLet) x xs

shUps a b = DPreOp (-20) (SimpleAtom $ show a) b
shUps' a x b = DPreOp (-20) (SimpleAtom $ show a ++ show x) b

shLam b = DFreshName True $ showLam (DVar 0) b

showLam x (DFreshName u d) = DFreshName u $ showLam (DUp 0 x) d
showLam x (DLam xs y) = DLam (DSep (InfixR 11) x xs) y
showLam x y = DLam x y

shLet a b = DFreshName True $ showLet (DLet "=" (shVar 0) $ DUp 0 a) b

showLet x (DFreshName u d) = DFreshName u $ showLet (DUp 0 x) d
showLet x (DLet' xs y) = DLet' (DSemi x xs) y
showLet x y = DLet' x y


--------------------------------------------------------------------- pattern synonyms

pattern Int i       <- Exp _ (Int_ i)
  where Int i       =  Exp [0] $ Int_ i
pattern Op2 op a b  <- Exp u (Op2_ op (upp u -> a) (upp u -> b))
  where Op2 op a b  =  Exp s $ Op2_ op az bz where (s, az, bz) = delta2 a b
pattern Op1 op a    <- Exp u (Op1_ op (upp u -> a))
  where Op1 op a    =  dup1 (Op1_ op) a
pattern Var i       <- Exp (varIndex -> i) Var_
  where Var 0       =  Exp [1] Var_
        Var i       =  Exp [0, i, i+1] Var_
pattern Lam i       <- Exp u (Lam_ (upp ((+1) <$> u) -> i))
  where Lam i       =  dupLam i
pattern Con a b i   <- Exp u (Con_ a b (map (upp u) -> i))
  where Con a b []  =  Exp [0] $ Con_ a b []
        Con a b [x]  =  dup1 (Con_ a b . (:[])) x
        Con a b [x, y] = Exp s $ Con_ a b [xz, yz] where (s, xz, yz) = delta2 x y
        Con a b x   =  Exp s $ Con_ a b bz where (s, bz) = deltas x
pattern Case a b c  <- Exp u (Case_ a (upp u -> b) (map (upp u) -> c))
  where Case cn a b =  Exp s $ Case_ cn az bz where (s, az: bz) = deltas $ a: b

pattern Let i x     = App (Lam x) i
pattern Y a         = Op1 YOp a
pattern App a b     = Op2 AppOp a b
pattern Seq a b     = Op2 SeqOp a b

infixl 4 `App`

varIndex (_: i: _) = i
varIndex _ = 0

dupLam (Exp vs ax) = Exp (f vs) $ Lam_ $ Exp (g vs) ax
  where
    f (0: nus) = 0 .: map (+(-1)) nus
    f us = map (+(-1)) us

    g xs@(0: _) = [0, 1, altersum xs + 1]
    g xs = [altersum xs]

dup1 f (Exp ab x) = Exp ab $ f $ Exp [altersum ab] x

altersum [x] = x
altersum (a: b: cs) = a - b + altersum cs

initSt :: Exp -> MSt
initSt e = MSt (Var 0) e []

-- for statistics
size :: MSt -> Int
size (MSt xs _ ys) = length (getLets xs) + length ys
  where
    getLets (Let x y) = x: getLets y
    getLets x = [x]

--------------------------------------------------------------------- toolbox: de bruijn index shifting

upp [k] ys = ys
upp (x: y: xs) ys = upp xs (up x (y - x) ys)

up i 0 e = e
up i num (Exp us x) = Exp (f i (i + num) us) x
  where
    f l n [s]
        | l >= s    = [s]
        | otherwise = [l, n, s+n-l]
    f l n us_@(l': n': us)
        | l <  l'   = l : n: map (+(n-l)) us_
        | l <= n'   = l': n' + n - l: map (+(n-l)) us
        | otherwise = l': n': f l n us

-- free variables set
fvs (Exp us _) = gen 0 us  where
    gen i (a: xs) = [i..a-1] ++ gen' xs
    gen' [] = []
    gen' (a: xs) = gen a xs

(.:) :: Int -> [Int] -> [Int]
a .: (x: y: xs) | a == x = y: xs
a .: xs = a: xs

usedVar i (Exp us _) = f us where
    f [fv] = i < fv
    f (l: n: us) = i < l || i >= n && f us

down i (Exp us e) = Exp <$> f us <*> pure e where
    f [fv]
        | i < fv = Nothing
        | otherwise = Just [fv]
    f vs@(j: vs'@(n: us))
        | i < j  = Nothing
        | i < n  = Just $ j .: map (+(-1)) vs'
        | otherwise = (j:) . (n .:) <$> f us

delta2 (Exp (add0 -> ua) a) (Exp (add0 -> ub) b) = (add0 s, Exp (dLadders 0 ua s) a, Exp (dLadders 0 ub s) b)
  where
    s = iLadders ua ub

deltas [] = ([0], [])
deltas es = (add0 s, [Exp (dLadders 0 u s) e | (u, Exp _ e) <- zip xs es])
  where
    xs = [add0 ue | Exp ue _ <- es]

    s = foldr1 iLadders xs

iLadders :: [Int] -> [Int] -> [Int]
iLadders x [] = x
iLadders [] x = x
iLadders x@(a: b: us) x'@(a': b': us')
    | b <= a' = addL a b $ iLadders us x'
    | b' <= a = addL a' b' $ iLadders x us'
    | otherwise = addL (min a a') c $ iLadders (addL c b us) (addL c b' us')
  where
    c = min b b'

addL a b cs | a == b = cs
addL a b (c: cs) | b == c = a: cs
addL a b cs = a: b: cs

add0 [] = [0]
add0 (0: cs) = cs
add0 cs = 0: cs

dLadders :: Int -> [Int] -> [Int] -> [Int]
dLadders s [] x = [s]
dLadders s x@(a: b: us) x'@(a': b': us')
    | b' <= a  = addL s (s + b' - a') $ dLadders (s + b' - a') x us'
    | a' <  a  = addL s (s + a - a') $ dLadders (s + a - a') x (addL a b' us')
    | a' == a  = dLadders (s + b - a) us (addL b b' us')

---------------------------

tryRemoves xs = tryRemoves_ (Var <$> xs)

tryRemoves_ [] dt = dt
tryRemoves_ (Var i: vs) dt = maybe (tryRemoves_ vs dt) (tryRemoves_ $ catMaybes $ down i <$> vs) $ tryRemove_ i dt

tryRemove_ i (MSt xs e es) = MSt <$> down (i+1) xs <*> down i e <*> downDown i es

downDown i [] = Just []
downDown 0 (_: xs) = Just xs
downDown i (x: xs) = (:) <$> down (i-1) x <*> downDown (i-1) xs

----------------------------------------------------------- machine code begins here

justResult :: MSt -> MSt
justResult = steps id (const ($)) (const (.))

hnf = justResult . initSt

----------------

type GenSteps e
    = (MSt -> e)
    -- -> (StepTag -> e)
    -> (StepTag -> (MSt -> e) -> MSt -> e)
    -> (StepTag -> (MSt -> e) -> (MSt -> e) -> MSt -> e)
    -> MSt -> e

type StepTag = String

steps :: forall e . GenSteps e
steps nostep {-ready-} bind cont dt@(MSt t e vs) = case e of

    Int{} -> nostep dt --ready "hnf int"
    Lam{} -> nostep dt --ready "hnf lam"

    Con cn i xs
        | lz /= 0 -> step "copy con" $ MSt (up 1 lz t) (Con cn i xs') $ zs ++ vs  -- share complex constructor arguments
        | otherwise -> nostep dt --ready "hnf con"
      where
        lz = length zs
        (xs', concat -> zs) = unzip $ f 0 xs
        f i [] = []
        f i (x: xs) | simple x = (up 0 lz x, []): f i xs
                    | otherwise = (Var i, [up 0 (lz - i - 1) x]): f (i+1) xs

    Var i -> lookupHNF_ rec "var" const i dt

    Seq a b -> case a of
        Int{}   -> step "seq" $ MSt t b vs
        Lam{}   -> step "seq" $ tryRemoves (fvs a) $ MSt t b vs
        Con{}   -> step "seq" $ tryRemoves (fvs a) $ MSt t b vs
        Var i   -> lookupHNF' "seqvar" (\e (Seq _ b) -> b) i dt
        _       -> step "seqexp" $ MSt (up 1 1 t) (Seq (Var 0) $ up 0 1 b) $  a: vs

    -- TODO: handle recursive constants
    Y (Lam x)   -> step "Y" $ MSt (up 1 1 t) x $ e: vs

    App a b -> case a of
        Lam x | usedVar 0 x
                -> step "app"    $ MSt (up 1 1 t) x $ b: vs
        Lam x   -> step "appdel" $ tryRemoves (fvs b) $ MSt t x vs
        Var i   -> lookupHNF' "appvar" (\e (App _ y) -> App e y) i dt
        _       -> step "appexp" $ MSt (up 1 1 t) (App (Var 0) $ up 0 1 b) $  a: vs

    Case cn a cs -> case a of
        Con cn i es -> step "case" $ tryRemoves (nub $ foldMap fvs $ delElem i cs) $ (MSt t (foldl App (cs !! i) es) vs)
        Var i   -> lookupHNF' "casevar" (\e (Case cn _ cs) -> Case cn e cs) i dt
        _       -> step "caseexp" $ MSt (up 1 1 t) (Case cn (Var 0) $ up 0 1 <$> cs) $ a: vs

    Op2 op x y -> case (x, y) of
        (Int e, Int f) -> step "op-done" $ MSt t (int op e f) vs
          where
            int Add a b = Int $ a + b
            int Sub a b = Int $ a - b
            int Mod a b = Int $ a `mod` b
            int LessEq a b = if a <= b then T else F
            int EqInt a b = if a == b then T else F
        (Var i, _) -> lookupHNF' "op2-1var" (\e (Op2 op _ y) -> Op2 op e y) i dt
        (_, Var i) -> lookupHNF' "op2-2var" (\e (Op2 op x _) -> Op2 op x e) i dt
        (Int{}, _) -> step "op2" $ MSt (up 1 1 t) (Op2 op x (Var 0)) $ y: vs
        (_, Int{}) -> step "op2" $ MSt (up 1 1 t) (Op2 op (Var 0) y) $ x: vs
        _          -> step "op2" $ MSt (up 1 2 t) (Op2 op (Var 0) (Var 1)) $ x: y: vs
  where
    rec = steps nostep bind cont

    step :: StepTag -> MSt -> e
    step t = bind t rec

    hnf :: (MSt -> e) -> MSt -> e
    hnf f = cont "hnf" f rec

    -- lookup var in head normal form
    lookupHNF_ :: (MSt -> e) -> StepTag -> (Exp -> Exp -> Exp) -> Int -> MSt -> e
    lookupHNF_ end msg f i dt = bind "shiftL" (hnf shiftLookup) $ iterate shiftL dt !! (i+1)
      where
        shiftLookup dt@(MSt _ e _)
            = case iterate shiftR dt !! (i+1) of
                MSt xs z es -> bind "shiftR" (tryRemove i) $ MSt xs (f (up 0 (i+1) e) z) es

        shiftL (MSt xs x (e: es)) = MSt (Let x xs) e es

        shiftR (MSt (Let x xs) e es) = MSt xs x $ e: es

        tryRemove i st = maybe (end st) (bind "remove" end) $ tryRemove_ i st

    -- lookup & step
    lookupHNF' :: StepTag -> (Exp -> Exp -> Exp) -> Int -> MSt -> e
    lookupHNF' msg f i dt = lookupHNF_ rec msg f i dt

    simple = \case
        Var{} -> True
        Int{} -> True
        _ -> False

    delElem i xs = take i xs ++ drop (i+1) xs

---------------------------------------------------------------------------------------- examples

runMachinePure = putStrLn . ppShow . hnf

pattern F = Con "False" 0 []
pattern T = Con "True" 1 []
pattern Nil = Con "[]" 0 []
pattern Cons a b = Con "Cons" 1 [a, b]

caseBool x f t = Case ["False", "True"] x [f, t]
caseList x n c = Case ["[]", "Cons"] x [n, c]

id_ = Lam (Var 0)

if_ b t f = caseBool b f t

not_ x = caseBool x T F

test = runMachinePure (id_ `App` id_ `App` id_ `App` id_ `App` Con "()" 0 [])

test' = runMachinePure (id_ `App` (id_ `App` Con "()" 0 []))

foldr_ f e = Y $ Lam $ Lam $ caseList (Var 0) (up 0 2 e) (Lam $ Lam $ up 0 4 f `App` Var 1 `App` (Var 3 `App` Var 0))

filter_ p = foldr_ (Lam $ Lam $ if_ (p `App` Var 1) (Cons (Var 1) (Var 0)) (Var 0)) Nil

and2 a b = if_ a b F

and_ = foldr_ (Lam $ Lam $ and2 (Var 1) (Var 0)) T

map_ f = foldr_ (Lam $ Lam $ Cons (f (Var 1)) (Var 0)) Nil

neq a b = not_ $ Op2 EqInt a b

from_ = Y $ Lam $ Lam $ Cons (Var 0) $ Var 1 `App` Op2 Add (Var 0) (Int 1)

idx xs n = caseList xs undefined $ Lam $ Lam $ if_ (Op2 EqInt n $ Int 0) (Var 1) $ idx (Var 0) (Op2 Sub n $ Int 1)

t = runMachinePure $ idx (from_ `App` Int 3) (Int 5)

takeWhile_ p xs = caseList xs Nil $ Lam $ Lam $ if_ (p (Var 1)) (Cons (Var 1) $ takeWhile_ p (Var 0)) Nil

sum_ = foldr_ (Lam $ Lam $ Op2 Add (Var 1) (Var 0)) (Int 0)

sum' = Y $ Lam $ Lam $ caseList (Var 0) (Int 0) $ Lam $ Lam $ Op2 Add (Var 1) $ Var 3 `App` Var 0

infixl 4 `sApp`

sApp a b = Seq b (App a b)

{-
accsum acc [] = acc
accsum acc (x: xs) = let z = acc + x `seq` accsum z xs
-}
accsum = Y $ Lam $ Lam $ Lam $ caseList (Var 0) (Var 1) $ Lam $ Lam $ Var 4 `sApp` Op2 Add (Var 3) (Var 1) `App` Var 0

fromTo = Y $ Lam $ Lam $ Lam $ Cons (Var 1) $ if_ (Op2 EqInt (Var 0) (Var 1)) Nil $ Var 2 `App` Op2 Add (Var 1) (Int 1) `App` Var 0

t' n = sum' `App` (fromTo `App` Int 0 `App` Int n) --  takeWhile_ (\x -> Op2 LessEq x $ Int 3) (from_ `App` Int 0)

t'' n = accsum `App` Int 0 `App` (fromTo `App` Int 0 `App` Int n) --  takeWhile_ (\x -> Op2 LessEq x $ Int 3) (from_ `App` Int 0)

{- TODO

primes :: [Int]
primes = 2:3: filter (\n -> and $ map (\p -> n `mod` p /= 0) (takeWhile (\x -> x <= iSqrt n) primes)) (from 5)


main = primes !! 3000
-}



-------------------------------------------------------------

{- alternative presentation

sect [] xs = xs
sect xs [] = xs
sect (x:xs) (y:ys) = (x || y): sect xs ys

diffUps a b = diffUps' 0 (back a) (back b)

diffUps' n u [] = (+(-n)) <$> u
diffUps' n [] _ = []
diffUps' n (x: xs) (y: ys)
    | x < y = (x - n): diffUps' n xs (y: ys)
    | x == y = diffUps' (n+1) xs ys

back = map fst . filter (not . snd) . zip [0..]

mkUps = f 0
  where
    f i [] = []
    f i (x: xs) = insertUp (Up (x-i) 1) $ f (i+1) xs

showUps us n = foldr f (replicate n True) us where
    f (Up l n) is = take l is ++ replicate n False ++ drop l is

deltaUps_ (map $ uncurry showUps -> us) = (mkUps $ back s, [mkUps $ u `diffUps` s | u <- us])
  where
    s = foldr1 sect $ us

joinUps a b = foldr insertUp b a

diffUpsTest xs
    | and $ zipWith (\a (b, _) -> s `joinUps` a == b) ys xs = show (s, ys)
    | otherwise = error $ unlines $ map (show . toLadder) xs ++ "----": map show xs ++ "-----": show s: show s_: "-----": map show ys ++ "------": map (show . joinUps s) ys
  where
    (s, ys) = deltaUps_ xs
    s_ = foldr1 iLadders $ toLadder <$> xs

diffUpsTest' = diffUpsTest [x,y] --diffUpsTest x y

--x = ([Up 8 2], 200)
--y = ([], 28)
x = ([Up 1 2, Up 3 4, Up 8 2], 200)
y = ([Up 2 2, Up 5 1, Up 6 2, Up 7 2], 28)

-- TODO: remove
insertUp (Up l 0) us = us
insertUp u [] = [u]
insertUp u@(Up l n) us_@(u'@(Up l' n'): us)
    | l < l' = u: us_
    | l >= l' && l <= l' + n' = Up l' (n' + n): us
    | otherwise = u': insertUp (Up (l-n') n) us
-}

