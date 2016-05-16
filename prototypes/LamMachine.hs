{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

import Data.List
import Data.Maybe
import Control.Arrow
import Control.Category hiding ((.))
import Control.Monad.Writer
import Control.Monad.Identity
import Debug.Trace
import System.Environment

import LambdaCube.Compiler.Pretty
import LambdaCube.Compiler.DeBruijn hiding (up)

-----------------

-- expression
data Exp_
    = Var_ Int
    | Y_ Exp
    | Int_ Int
    | Lam_ Exp
    | Let_ Exp Exp

    | App_ Exp Exp
    | Seq_ Exp Exp
    | Con_ String Int [Exp]
    | Case_ Exp [(String, Exp)]
    | Op1_ Op1 Exp
    | Op2_ Op2 Exp Exp

data Op1 = Round
    deriving (Eq, Show)

data Op2 = Add | Sub | Mod | LessEq | EqInt
    deriving (Eq, Show)

-- cached free variables set
data Exp = Exp {dbUps :: [Up], maxFreeVars :: Int, expexp :: Exp_ }

-- state of the machine
data MSt = MSt [(FreeVars, Exp)]  -- TODO: use finger tree instead of list
               Exp
               [Exp]  -- TODO: use finger tree instead of list

--------------------------------------------------------------------- toolbox: pretty print

instance PShow Exp where
    pShow e@(Exp u t x) = case e of -- shUps' u t $ case Exp [] t x of
        Var i -> DVar i
        App a b -> DApp (pShow a) (pShow b)
        Seq a b -> DOp "`seq`" (Infix 1) (pShow a) (pShow b)
        Lam e -> shLam_ True $ pShow e
        Let a b -> shLet_ (pShow a) $ pShow b
        Con s i xs -> foldl DApp (text s) $ pShow <$> xs
        Int i -> pShow i
        Op1 o x -> text (show o) `DApp` pShow x
        Op2 EqInt x y -> DOp "==" (Infix 4) (pShow x) (pShow y)
        Op2 Add x y -> DOp "+" (InfixL 6) (pShow x) (pShow y)
        Op2 o x y -> text (show o) `DApp` pShow x `DApp` pShow y
        Y e -> "Y" `DApp` pShow e
        Case e xs -> DPreOp (-20) (ComplexAtom "case" (-10) (pShow e) (SimpleAtom "of")) $ foldr1 DSemi [DArr_ "->" (text a) (pShow b) | (a, b) <- xs]

shUps a b = DPreOp (-20) (SimpleAtom $ show a) b
shUps' a x b = DPreOp (-20) (SimpleAtom $ show a ++ show x) b

shLam_ usedVar b = DFreshName usedVar $ showLam (DVar 0) b

showLam x (DFreshName u d) = DFreshName u $ showLam (DUp 0 x) d
showLam x (DLam xs y) = DLam (DSep (InfixR 11) x xs) y
showLam x y = DLam x y

shLet i a b = DLet' (DLet "=" (blue $ shVar i) $ DUp i a) (DUp i b)

showLet x (DFreshName u d) = DFreshName u $ showLet (DUp 0 x) d
showLet x (DLet' xs y) = DLet' (DSemi x xs) y
showLet x y = DLet' x y

shLet_ a b = DFreshName True $ showLet (DLet "=" (shVar 0) $ DUp 0 a) b

instance PShow MSt where
    pShow (MSt as b bs) = case foldl (flip (:)) (DBrace (pShow b): [pShow x |  x <- bs]) [pShow x | EPP x <- as] of
        x: xs -> foldl (flip shLet_) x xs


--------------------------------------------------------------------- toolbox: free variables

maxFreeVars' (Exp u k _) = upsFreeVars' u k

upsFreeVars xs s = foldr rearr s xs

upsFreeVars' xs s = foldr rearr' s xs
  where
    rearr' (Up l n) m
        | l >= m = m      -- TODO: remove
        | otherwise = n + m

upVarIndex xs s = foldr rearr' s xs
  where
    rearr' (Up l n) i
        | l > i = i
        | otherwise = n + i


-- TODO: remove
instance HasFreeVars Exp where
    getFreeVars (Exp us fv e) = upsFreeVars us $ FreeVars $ 2^fv - 1

fvs (Exp us fv _) = gen 0 $ foldr f [fv] us  where
    f (Up l n) xs = l: l+n: map (+n) xs
    gen i (a: xs) = [i..a-1] ++ gen' xs
    gen' [] = []
    gen' (a: xs) = gen a xs

upss u (Exp _ i e) = Exp u i e

dup2 f ax bx = Exp s (maxFreeVars' az `max` maxFreeVars' bz) $ f az bz  where
    (s, [a', b']) = deltaUps [ax, bx]
    az = upss a' ax
    bz = upss b' bx

dup1 :: (Exp -> Exp_) -> Exp -> Exp
dup1 f (Exp a b x) = Exp a b $ f $ Exp [] b x

dupCon f [] = Exp [] 0 $ f []
dupCon f bx = Exp s (maximum $ maxFreeVars' <$> bz) $ f bz  where
    (s, b') = deltaUps bx
    bz = zipWith upss b' bx

dupCase f ax (unzip -> (ss, bx))
    = Exp s (maxFreeVars' az `max` maximum (maxFreeVars' <$> bz)) $ f az $ zip ss bz
  where
    (s, a': b') = deltaUps $ ax: bx
    az = upss a' ax
    bz = zipWith upss b' bx

dupLam f e@(Exp a fv ax) = Exp (ff a) (max 0 $ fv - 1) $ f $ Exp (gg a) fv ax
  where
    gg (Up 0 n: _) = [Up 0 1]
    gg _ = []

    ff (Up 0 n: us) = insertUp (Up 0 $ n - 1) $ incUp (-1) <$> us
    ff us = incUp (-1) <$> us

-- (\x -> e) f           x = f in e
dupLet f z w = case Lam w `App` z of
    Exp a fv (App_ (Exp b fv' (Lam_ c)) d) -> Exp a fv $ Let_ d c 


pattern Int i <- Exp _ _ (Int_ i)
  where Int i =  Exp [] 0 $ Int_ i
pattern App a b <- Exp u _ (App_ (upp u -> a) (upp u -> b))
  where App a b =  dup2 App_ a b
pattern Seq a b <- Exp u _ (Seq_ (upp u -> a) (upp u -> b))
  where Seq a b =  dup2 Seq_ a b
pattern Op2 op a b <- Exp u _ (Op2_ op (upp u -> a) (upp u -> b))
  where Op2 op a b =  dup2 (Op2_ op) a b
pattern Op1 op a <- Exp u _ (Op1_ op (upp u -> a))
  where Op1 op a =  dup1 (Op1_ op) a
pattern Var i <- Exp u _ (Var_ (upVarIndex u -> i))
  where Var 0 =  Exp [] 1 $ Var_ 0
        Var i =  Exp [Up 0 i] 1 $ Var_ 0
pattern Lam i <- Exp u _ (Lam_ (upp (incUp 1 <$> u) -> i))
  where Lam i =  dupLam Lam_ i
pattern Let i x <- Exp u _ (Let_ (upp u -> i) (upp (incUp 1 <$> u) -> x))
  where Let i x =  dupLet Let_ i x
pattern Y i <- Exp u _ (Y_ (upp u -> i))
  where Y i =  dup1 Y_ i
pattern Con a b i <- Exp u _ (Con_ a b (map (upp u) -> i))
  where Con a b i =  dupCon (Con_ a b) i
pattern Case a b <- Exp u _ (Case_ (upp u -> a) (map (second $ upp u) -> b))
  where Case a b =  dupCase Case_ a b
--pattern Ups op a <- Exp _ (Ups_ op a)
--  where Ups op a =  Exp (

upp u x = foldr up x u

up :: Up -> Exp -> Exp
up u@(Up i num) e@(Exp us s x)
    | dbGE'' i e = e
    | otherwise = addUp u e


infixl 4 `App`

--------------------------------------------------------------------- toolbox: de bruijn index shifting

data Up = Up !Int{-level-} !Int{-num-}
  deriving (Eq, Show)

incUp t (Up l n) = Up (l+t) n

rearr (Up l n) = rearrangeFreeVars (RFUp n) l

showUps us n = foldr f (replicate n True) us where
    f (Up l n) is = take l is ++ replicate n False ++ drop l is

--sectUps' a b = sect (showUps a) (showUps b) -- sectUps 0 a 0 b

sect [] xs = xs
sect xs [] = xs
sect (x:xs) (y:ys) = (x || y): sect xs ys

{- TODO
sectUps _ u _ [] = []
sectUps _ [] _ u = []
sectUps k us_@(Up l n: us) k' us_'@(Up l' n': us')
    | k + l + n <= k' + l' = sectUps (k + n) us k' us_'
    | k' + l' + n' <= k + l = sectUps k us_ (k' + n') us'
    | otherwise = insertUp (Up l'' n'') $ sectUps (k + n - c) (Up b c: us) (k' + n' - c') (Up b c': us')
  where
    l'' = max l l'
    b = min (l + n) (l' + n')
    n'' = b - l''
    c = l + n - b
    c' = l' + n' - b

diffUps [] u = u
diffUps [] [] = []
diffUps (Up l n: us) (Up l' n': us') = insertUp (Up l' (l - l')) $ diffUps us (Up (l + n) (l' + n' - l - n): us')
-}

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

deltaUps = deltaUps_ . map crk

deltaUps_ (map $ uncurry showUps -> us) = (mkUps $ back s, [mkUps $ u `diffUps` s | u <- us])
  where
    s = foldr1 sect $ us

crk (Exp u e _) = (u, e)

joinUps a b = foldr insertUp b a

diffUpsTest xs | and $ zipWith (\a (b, _) -> s `joinUps` a == b) ys xs = show (s, ys)
  where
    (s, ys) = deltaUps_ xs

diffUpsTest' = diffUpsTest [x,y] --diffUpsTest x y
  where
    x = ([Up 1 2, Up 3 4, Up 8 2], 20)
    y = ([Up 2 2, Up 5 1, Up 6 2, Up 7 2], 18)

insertUp u@(Up l 0) us = us
insertUp u@(Up l n) [] = [u]
insertUp u@(Up l n) us_@(u'@(Up l' n'): us)
    | l < l' = u: us_
    | l >= l' && l <= l' + n' = Up l' (n' + n): us
    | otherwise = u': insertUp (Up (l-n') n) us

addUp u (Exp us k e) = Exp (insertUp u us) k e  -- TODO: remove excess ups?

ups' a b = ups $ Up a b

ups :: Up -> [(FreeVars, Exp)] -> [(FreeVars, Exp)]
ups l [] = []
ups l@(Up i _) xs@((s,  e): es)
    | dbGE i s = xs
    | otherwise = eP (up l e) $ ups (incUp 1 l) es

eP x [] = [(getFreeVars x,  x)]
eP x xs@((s, _):_) = (getFreeVars x <> lowerFreeVars s,  x): xs

pattern EPP x <- (_,  x)

---------------------------

down i x | usedVar i x = Nothing
down i x = Just $ down_ i x

dbGE' l m = l >= m

dbGE'' l m = dbGE' l $ maxFreeVars' m

down_ i e
    | dbGE'' i e = e
down_ i0 e0@(Exp us ii e) = f i0 us e where
    f i [] e = error $ "-- - -  -- " ++ show (i0, i) ++ "     " ++ ppShow e0  --(pushUps e) --"show down_ i e
    f i (u@(Up j n): us) e
        | i < j = addUp (Up (j-1) n) $ f i us e
        | i >= j + n = addUp u $ f (i-n) us e
        | otherwise = addUp (Up j $ n-1) $ Exp us ii e

tryRemoves xs = tryRemoves_ (Var <$> xs)
tryRemoves_ [] dt = dt
tryRemoves_ (Var i: vs) dt
    | Just dt' <- tryRemove_ i dt
    = tryRemoves_ (catMaybes $ down i <$> vs) dt'
    | otherwise = tryRemoves_ vs dt

tryRemove i x = fromMaybe x $ tryRemove_ i x

tryRemove_ i dt@(MSt xs e es)
    | Just e' <- down i e
    , Just xs' <- downUp i xs
    , Just es' <- downDown i es
    = Just $ MSt xs' e' es'
    | otherwise
    = Nothing

downEP i ( x) =  down i x
downEP_ i (s,  x) = (delVar i s, down_ i x)

downUp i [] = Just []
downUp i x@((s, _): _)
    | usedVar (i+1) s = Nothing
    | otherwise = Just $ downUp_ i x

downUp_ i [] = []
downUp_ i (x: xs)
    | x' <- downEP_ (i+1) x
    , xs' <- downUp_ (i+1) xs
    = x': xs'

downDown i [] = Just []
downDown 0 (_: xs) = Just xs
downDown i (x: xs)
    | Just x' <- downEP (i-1) x
    , Just xs' <- downDown (i-1) xs
    = Just $ x': xs'
    | otherwise = Nothing

--------------------------------------------------------------------- toolbox: machine monad

class Monad m => MachineMonad m where
    traceStep :: String -> m ()
    collectSizeStat :: Int -> m ()

instance MachineMonad Identity where
    traceStep _ = return ()
    collectSizeStat _ = return ()

instance MachineMonad IO where
    traceStep s = return ()
--    traceStep = putStrLn
    collectSizeStat s = return ()

instance MachineMonad (Writer [Int]) where
    traceStep s = return ()
    collectSizeStat s = tell [s]

runMachineStat e = putStr $ unlines $ ppShow t: "--------": show (length w, w):[]
  where
    (t, w) = runWriter (hnf e :: Writer [Int] MSt)

runMachineIO e = do
    t <- hnf e :: IO MSt
    putStr $ unlines $ ppShow t: []

runMachinePure e = putStr $ unlines $ ppShow t: []
  where
    t = runIdentity $ hnf e

----------------------------------------------------------- machine code begins here

-- big step
step :: MachineMonad m => MSt -> m MSt
step dt@(MSt t e vs) = case e of

    Int{} -> return dt

    Lam{} -> return dt

    Con cn i xs
        | lz /= 0 -> return $ MSt (ups' 1 lz t) (Con cn i xs') $ zs ++ vs  -- share complex constructor arguments
        | otherwise -> return dt
      where
        lz = length zs
        (xs', concat -> zs) = unzip $ f 0 xs
        f i [] = []
        f i (x: xs) | simple x = (up (Up 0 lz) x, []): f i xs
                    | otherwise = (Var i, [up (Up 0 (lz - i - 1)) x]): f (i+1) xs

    Var i -> lookupHNF "var" (\e _ -> e) i dt

    Seq a b -> case a of
        Int{} -> stepMsg "seq" $ MSt t b vs
        Lam{} -> stepMsg "seq" $ tryRemoves (fvs a) $ MSt t b vs
        Con{} -> stepMsg "seq" $ tryRemoves (fvs a) $ MSt t b vs
        Var i -> lookupHNF' "seqvar" (\e (Seq _ b) -> b) i dt
        _      -> stepMsg "seqexp" $ MSt (ups' 1 1 t) (Seq (Var 0) $ up (Up 0 1) b) $  a: vs

    -- TODO: handle recursive constants
    Y (Lam x) -> stepMsg "Y" $ MSt (ups' 1 1 t) x $ e: vs

    App a b -> case a of
        Lam x | usedVar 0 x
                -> stepMsg "app" $ MSt (ups' 1 1 t) x $ b: vs
        Lam x   -> stepMsg "appdel" $ tryRemoves (fvs b) $ MSt t x vs
        Var i   -> lookupHNF' "appvar" (\e (App _ y) -> App e y) i dt
        _       -> stepMsg "appexp" $ MSt (ups' 1 1 t) (App (Var 0) $ up (Up 0 1) b) $  a: vs

    Case a cs -> case a of
        Con cn i es -> stepMsg "case" $ tryRemoves (nub $ foldMap (fvs . snd) $ delElem i cs) $ (MSt t (foldl App (snd $ cs !! i) es) vs)
        Var i -> lookupHNF' "casevar" (\e (Case _ cs) -> Case e cs) i dt
        _     -> stepMsg "caseexp" $ MSt (ups' 1 1 t) (Case (Var 0) $ second (up (Up 0 1)) <$> cs) $ a: vs

    Op2 op x y -> case (x, y) of
        (Int e, Int f) -> return $ MSt t (int op e f) vs
          where
            int Add a b = Int $ a + b
            int Sub a b = Int $ a - b
            int Mod a b = Int $ a `mod` b
            int LessEq a b = if a <= b then T else F
            int EqInt a b = if a == b then T else F
        (Var i, _) -> lookupHNF' "op2-1var" (\e (Op2 op _ y) -> Op2 op e y) i dt
        (_, Var i) -> lookupHNF' "op2-2var" (\e (Op2 op x _) -> Op2 op x e) i dt
        (Int{}, _) -> stepMsg "op2" $ MSt (ups' 1 1 t) (Op2 op x (Var 0)) $ y: vs
        (_, Int{}) -> stepMsg "op2" $ MSt (ups' 1 1 t) (Op2 op (Var 0) y) $ x: vs
        _          -> stepMsg "op2" $ MSt (ups' 1 2 t) (Op2 op (Var 0) (Var 1)) $ x: y: vs

stepMsg :: MachineMonad m => String -> MSt -> m MSt
stepMsg msg dt = do
    traceStep $ ((msg ++ "\n") ++) $ show $ pShow dt
    collectSizeStat $ size dt
    step dt

hnf e = stepMsg "hnf" $ MSt [] e []

size (MSt xs _ ys) = length xs + length ys

shiftL (MSt xs x (e: es)) = MSt (eP x xs) e es
shiftR (MSt (EPP x: xs) e es) = MSt xs x $ e: es

shiftLookup f n dt@(MSt _ e _) = repl $ iterate shiftR dt !! (n+1) where
    repl (MSt xs z es) = MSt xs (f (up (Up 0 (n+1)) e) z) es

-- lookup var in head normal form
lookupHNF msg f i dt = tryRemove i . shiftLookup f i <$> stepMsg msg (iterate shiftL dt !! (i+1))

-- lookup & step
lookupHNF' msg f i dt = stepMsg ("C " ++ msg) =<< lookupHNF msg f i dt

simple = \case
    Var{} -> True
    Int{} -> True
    _ -> False

delElem i xs = take i xs ++ drop (i+1) xs

---------------------------------------------------------------------------------------- examples

id_ = Lam (Var 0)

pattern F = Con "False" 0 []
pattern T = Con "True" 1 []
pattern Nil = Con "[]" 0 []
pattern Cons a b = Con "Cons" 1 [a, b]

caseBool x f t = Case x [("False", f), ("True", t)]
caseList x n c = Case x [("[]", n), ("Cons", c)]

if_ b t f = caseBool b f t

not_ x = caseBool x T F

test = runMachinePure (id_ `App` id_ `App` id_ `App` id_ `App` Con "()" 0 [])

test' = runMachinePure (id_ `App` (id_ `App` Con "()" 0 []))

foldr_ f e = Y $ Lam $ Lam $ caseList (Var 0) (up (Up 0 2) e) (Lam $ Lam $ up (Up 0 4) f `App` Var 1 `App` (Var 3 `App` Var 0))

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

main = do
    [b, n] <- getArgs
    runMachineIO $ case b of
        "lazy" -> t' $ read n
        "seq" -> t'' $ read n

{- TODO

primes :: [Int]
primes = 2:3: filter (\n -> and $ map (\p -> n `mod` p /= 0) (takeWhile (\x -> x <= iSqrt n) primes)) (from 5)


main = primes !! 3000
-}
