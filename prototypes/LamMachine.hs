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
    = Lam_ Exp
    | Var_ Int
    | App_ Exp Exp
    | Seq_ Exp Exp
    | Con_ String Int [Exp]
    | Case_ Exp [(String, Exp)]
    | Int_ Int
    | Op1_ Op1 Exp
    | Op2_ Op2 Exp Exp
    | Y_ Exp
    | Ups_ [Up] Exp
--    deriving (Eq)

data Op1 = Round
    deriving (Eq, Show)

data Op2 = Add | Sub | Mod | LessEq | EqInt
    deriving (Eq, Show)

-- cached free variables set
data Exp = Exp FreeVars Exp_

-- state of the machine
data MSt = MSt [(FreeVars, Exp)]  -- TODO: use finger tree instead of list
               Exp
               [Exp]  -- TODO: use finger tree instead of list

--------------------------------------------------------------------- toolbox: pretty print

instance PShow Exp where
    pShow x = case {-pushUps-} x of
        Var i -> DVar i
        App a b -> DApp (pShow a) (pShow b)
        Seq a b -> DOp "`seq`" (Infix 1) (pShow a) (pShow b)
        Lam e -> shLam_ True $ pShow e
        Con s i xs -> foldl DApp (text s) $ pShow <$> xs
        Int i -> pShow i
        Op1 o x -> text (show o) `DApp` pShow x
        Op2 EqInt x y -> DOp "==" (Infix 4) (pShow x) (pShow y)
        Op2 Add x y -> DOp "+" (InfixL 6) (pShow x) (pShow y)
        Op2 o x y -> text (show o) `DApp` pShow x `DApp` pShow y
        Y e -> "Y" `DApp` pShow e
        Case e xs -> DPreOp (-20) (ComplexAtom "case" (-10) (pShow e) (SimpleAtom "of")) $ foldr1 DSemi [DArr_ "->" (text a) (pShow b) | (a, b) <- xs]
        Ups u xs -> DPreOp (-20) (SimpleAtom $ show u) $ pShow xs

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

--instance Eq Exp where Exp _ a == Exp _ b = a == b

instance HasFreeVars Exp where
    getFreeVars (Exp fv _) = fv

upss [] e = e
upss u e = Ups u e

dup2 f (Ups a ax) (Ups b bx) = Ups_ s $ Exp (getFreeVars az <> getFreeVars bz) $ f az bz  where
    (s, [a', b']) = deltaUps [a, b]
    az = upss a' ax
    bz = upss b' bx
dup2 f a b = f a b
dup1 f (Ups a ax) = Ups_ a $ Exp (getFreeVars ax) $ f ax
dup1 f x = f x

getUs (Ups x y) = (x, y)
getUs y = ([], y)

dupCon f [] = f []
dupCon f [Ups a ax] = Ups_ a $ Exp (getFreeVars ax) $ f [ax]
dupCon f (unzip . map getUs -> (b, bx)) = Ups_ s $ Exp (foldMap getFreeVars bz) $ f bz  where
    (s, b') = deltaUps b
    bz = zipWith upss b' bx

dupCase f (getUs -> (a, ax)) (unzip -> (ss, unzip . map getUs -> (b, bx)))
    = Ups_ s $ Exp (getFreeVars az <> foldMap getFreeVars bz) $ f az $ zip ss bz
  where
    (s, a': b') = deltaUps $ a: b
    az = upss a' ax
    bz = zipWith upss b' bx

dupLam f (Ups a ax) = Ups_ (ff a) $ Exp (shiftFreeVars (-1) $ getFreeVars ax') $ f ax'
  where
    ax' = case a of
        Up 0 n: _ -> up (Up 0 1) ax
        _ -> ax
    ff (Up 0 n: us) = insertUp (Up 0 $ n - 1) $ incUp (-1) <$> us
    ff us = incUp (-1) <$> us
dupLam f x = f x


pattern Int i <- Exp _ (Int_ i)
  where Int i =  Exp mempty $ Int_ i
pattern App a b <- Exp _ (App_ a b)
  where App a b =  Exp (getFreeVars a <> getFreeVars b) $ dup2 App_ a b
pattern Seq a b <- Exp _ (Seq_ a b)
  where Seq a b =  Exp (getFreeVars a <> getFreeVars b) $ dup2 Seq_ a b
pattern Op2 op a b <- Exp _ (Op2_ op a b)
  where Op2 op a b =  Exp (getFreeVars a <> getFreeVars b) $ dup2 (Op2_ op) a b
pattern Op1 op a <- Exp _ (Op1_ op a)
  where Op1 op a =  Exp (getFreeVars a) $ dup1 (Op1_ op) a
pattern Var i <- Exp _ (Var_ i)
  where Var 0 =  Exp (freeVar 0) $ Var_ 0
        Var i =  Ups [Up 0 i] $ Exp (freeVar 0) $ Var_ 0
pattern Lam i <- Exp _ (Lam_ i)
  where Lam i =  Exp (shiftFreeVars (-1) $ getFreeVars i) $ dupLam Lam_ i
pattern Y i <- Exp _ (Y_ i)
  where Y i =  Exp (getFreeVars i) $ dup1 Y_ i
pattern Con a b i <- Exp _ (Con_ a b i)
  where Con a b i =  Exp (foldMap getFreeVars i) $ dupCon (Con_ a b) i
pattern Case a b <- Exp _ (Case_ a b)
  where Case a b =  Exp (getFreeVars a <> foldMap (getFreeVars . snd) b) $ dupCase Case_ a b
pattern Ups op a <- Exp _ (Ups_ op a)
  where Ups op a =  Exp (upsFreeVars op $ getFreeVars a) $ Ups_ op a

infixl 4 `App`

--------------------------------------------------------------------- toolbox: de bruijn index shifting
-- TODO: speedup these with reification

rearr (Up l n) = rearrangeFreeVars (RFUp n) l

upsFreeVars xs s = foldr rearr s xs

pushUps (Ups us e) = foldr pushUp e us
pushUps e = e

showUps us = foldr f [] us where
    f (Up l n) is = take n [l..] ++ map (n+) is

--sectUps' a b = sect (showUps a) (showUps b) -- sectUps 0 a 0 b

sect [] _ = []
sect _ [] = []
sect (x:xs) (y:ys)
    | x == y = x: sect xs ys
    | x < y  = sect xs (y: ys)
    | x > y  = sect (x: xs) ys

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

diffUps = diffUps' 0

diffUps' n u [] = (+(-n)) <$> u
diffUps' n (x: xs) (y: ys)
    | x < y = (x - n): diffUps' n xs (y: ys)
    | x == y = diffUps' (n+1) xs ys

mkUps = f 0
  where
    f i [] = []
    f i (x: xs) = insertUp (Up (x-i) 1) $ f (i+1) xs

deltaUps us = (mkUps s, [mkUps $ showUps u `diffUps` s | u <- us])
  where
    s = foldr1 sect $ showUps <$> us

joinUps a b = foldr insertUp b a

diffUpsTest xs | and $ zipWith (\a b -> s `joinUps` a == b) ys xs = "ok"
  where
    (s, ys) = deltaUps xs

diffUpsTest' = diffUpsTest [x,y] --diffUpsTest x y
  where
    x = [Up 1 2, Up 3 4, Up 8 2]
    y = [Up 2 2, Up 5 1, Up 6 2, Up 7 2]

insertUp u@(Up l 0) us = us
insertUp u@(Up l n) [] = [u]
insertUp u@(Up l n) us_@(u'@(Up l' n'): us)
    | l < l' = u: us_
    | l >= l' && l <= l' + n' = Up l' (n' + n): us
    | otherwise = u': insertUp (Up (l-n') n) us

addUp (Up _ 0) e = e
addUp u (Exp s (Ups_ us e)) = Exp (rearr u s) $ Ups_ (insertUp u us) e
addUp u e = Ups [u] e

pushUp u@(Up i num) e@(Exp s x)
    | dbGE i s = e
    | otherwise = Exp (rearrangeFreeVars (RFUp num) i s) $ case x of
        App_ a b -> App_ (f a) (f b)
        Seq_ a b -> Seq_ (f a) (f b)
        Con_ cn s xs -> Con_ cn s (f <$> xs)
        Case_ s xs -> Case_ (f s) (second f <$> xs)
        Lam_ e -> Lam_ (up (Up (i+1) num) e)
        Var_ k | i <= k -> Var_ (k + num)
               | otherwise -> Var_ k
        x@Int_{} -> x
        Y_ a -> Y_ $ f a
        Op1_ op a -> Op1_ op (f a)
        Op2_ op a b -> Op2_ op (f a) (f b)
  where
    f = up u

data Up = Up !Int{-level-} !Int{-num-}
  deriving (Eq, Show)

up :: Up -> Exp -> Exp
up u@(Up i num) e@(Exp s x)
    | dbGE i s = e
    | otherwise = addUp u e

ups' a b = ups $ Up a b

ups :: Up -> [(FreeVars, Exp)] -> [(FreeVars, Exp)]
ups l [] = []
ups l@(Up i _) xs@((s,  e): es)
    | dbGE i s = xs
    | otherwise = eP (up l e) $ ups (incUp 1 l) es

incUp t (Up l n) = Up (l+t) n

eP x [] = [(getFreeVars x,  x)]
eP x xs@((s, _):_) = (getFreeVars x <> lowerFreeVars s,  x): xs

pattern EPP x <- (_,  x)

---------------------------

down i x | usedVar i x = Nothing
down i x = Just $ down_ i x

down_ i e@(Exp s x)
    | dbGE i s = e
down_ i (Ups us e) = f i us e where
    f i [] e = error $ "-- - -  -- " ++ show i ++ "     " ++ ppShow e ++ "\n" ++ ppShow (pushUps e) --"show down_ i e
    f i (u@(Up j n): us) e
        | i < j = addUp (Up (j-1) n) $ f i us e
        | i >= j + n = addUp u $ f (i-n) us e
        | otherwise = addUp (Up j $ n-1) $ Ups us e
down_ i e@(Exp s x) = Exp (delVar i s) $ case x of
        Var_ j | j > i  -> Var_ $ j - 1
              | otherwise -> Var_ j
        Lam_ e -> Lam_ $ down_ (i+1) e
        Y_ e -> Y_ $ down_ i e
        App_ a b -> App_ (down_ i a) (down_ i b)
        Seq_ a b -> Seq_ (down_ i a) (down_ i b)
        Con_ s k es -> Con_ s k $ (down_ i <$> es)
        Case_ e es -> Case_ (down_ i e) $ map (second $ down_ i) es
        Int_ i -> Int_ i
        Op1_ o e -> Op1_ o $ down_ i e
        Op2_ o e f -> Op2_ o (down_ i e) (down_ i f)

tryRemoves xs = tryRemoves_ (Var <$> freeVars xs)
tryRemoves_ [] dt = dt
tryRemoves_ ((pushUps -> Var i): vs) dt
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
--    traceStep s = return ()
    traceStep = putStrLn
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
step dt@(MSt t e vs) = case pushUps e of

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

    Seq a b -> case pushUps a of
        Int{} -> stepMsg "seq" $ MSt t b vs
        Lam{} -> stepMsg "seq" $ tryRemoves (getFreeVars a) $ MSt t b vs
        Con{} -> stepMsg "seq" $ tryRemoves (getFreeVars a) $ MSt t b vs
        Var i -> lookupHNF' "seqvar" (\e (pushUps -> Seq _ b) -> b) i dt
        _     -> stepMsg "seqexp" $ MSt (ups' 1 1 t) (Seq (Var 0) $ up (Up 0 1) b) $  a: vs

    -- TODO: handle recursive constants
    Y (pushUps -> Lam x) -> stepMsg "Y" $ MSt (ups' 1 1 t) x $ e: vs

    App a b -> case pushUps a of
        Lam x | usedVar 0 x
                -> stepMsg "app" $ MSt (ups' 1 1 t) x $ b: vs
        Lam x   -> stepMsg "appdel" $ tryRemoves (getFreeVars b) $ MSt t x vs
        Var i   -> lookupHNF' "appvar" (\e (pushUps -> App _ y) -> App e y) i dt
        _       -> stepMsg "appexp" $ MSt (ups' 1 1 t) (App (Var 0) $ up (Up 0 1) b) $  a: vs

    Case a cs -> case pushUps a of
        Con cn i es -> stepMsg "case" $ tryRemoves (foldMap (getFreeVars . snd) $ delElem i cs) $ (MSt t (foldl App (snd $ cs !! i) es) vs)
        Var i -> lookupHNF' "casevar" (\e (pushUps -> Case _ cs) -> Case e cs) i dt
        _     -> stepMsg "caseexp" $ MSt (ups' 1 1 t) (Case (Var 0) $ second (up (Up 0 1)) <$> cs) $ a: vs

    Op2 op x y -> case (pushUps x, pushUps y) of
        (Int e, Int f) -> return $ MSt t (int op e f) vs
          where
            int Add a b = Int $ a + b
            int Sub a b = Int $ a - b
            int Mod a b = Int $ a `mod` b
            int LessEq a b = if a <= b then T else F
            int EqInt a b = if a == b then T else F
        (Var i, _) -> lookupHNF' "op2-1var" (\e (pushUps -> Op2 op _ y) -> Op2 op e y) i dt
        (_, Var i) -> lookupHNF' "op2-2var" (\e (pushUps -> Op2 op x _) -> Op2 op x e) i dt
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
