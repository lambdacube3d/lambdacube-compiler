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
    deriving (Eq)

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
    pShow = \case
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

instance Eq Exp where Exp _ a == Exp _ b = a == b

instance HasFreeVars Exp where
    getFreeVars (Exp fv _) = fv

pattern Int i <- Exp _ (Int_ i)
  where Int i =  Exp mempty $ Int_ i
pattern App a b <- Exp _ (App_ a b)
  where App a b =  Exp (getFreeVars a <> getFreeVars b) $ App_ a b
pattern Seq a b <- Exp _ (Seq_ a b)
  where Seq a b =  Exp (getFreeVars a <> getFreeVars b) $ Seq_ a b
pattern Op2 op a b <- Exp _ (Op2_ op a b)
  where Op2 op a b =  Exp (getFreeVars a <> getFreeVars b) $ Op2_ op a b
pattern Op1 op a <- Exp _ (Op1_ op a)
  where Op1 op a =  Exp (getFreeVars a) $ Op1_ op a
pattern Var i <- Exp _ (Var_ i)
  where Var i =  Exp (freeVar i) $ Var_ i
pattern Lam i <- Exp _ (Lam_ i)
  where Lam i =  Exp (shiftFreeVars (-1) $ getFreeVars i) $ Lam_ i
pattern Y i <- Exp _ (Y_ i)
  where Y i =  Exp (getFreeVars i) $ Y_ i
pattern Con a b i <- Exp _ (Con_ a b i)
  where Con a b i =  Exp (foldMap getFreeVars i) $ Con_ a b i
pattern Case a b <- Exp _ (Case_ a b)
  where Case a b =  Exp (getFreeVars a <> foldMap (getFreeVars . snd) b) $ Case_ a b

infixl 4 `App`

--------------------------------------------------------------------- toolbox: de bruijn index shifting
-- TODO: speedup these with reification

data Up = Up !Int{-level-} !Int{-num-}

up :: Up -> Exp -> Exp
up (Up i num) e = f i e where
    f i e@(Exp s x)
        | dbGE i s = e
        | otherwise = Exp (rearrangeFreeVars (RFUp num) i s) $ case x of
            App_ a b -> App_ (f i a) (f i b)
            Seq_ a b -> Seq_ (f i a) (f i b)
            Con_ cn s xs -> Con_ cn s (f i <$> xs)
            Case_ s xs -> Case_ (f i s) (second (f i) <$> xs)
            Lam_ e -> Lam_ (f (i+1) e)
            Var_ k | i <= k -> Var_ (k + num)
                   | otherwise -> Var_ k
            x@Int_{} -> x
            Y_ a -> Y_ $ f i a
            Op1_ op a -> Op1_ op (f i a)
            Op2_ op a b -> Op2_ op (f i a) (f i b)


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
    | otherwise = Exp (delVar i s) $ case x of
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

    Var i -> lookupHNF "var" (\e (Var i) -> e) i dt

    Seq Int{}   b -> stepMsg "seq" $ MSt t b vs
    Seq a@Lam{} b -> stepMsg "seq" $ tryRemoves (getFreeVars a) $ MSt t b vs
    Seq a@Con{} b -> stepMsg "seq" $ tryRemoves (getFreeVars a) $ MSt t b vs
    Seq (Var i) _ -> lookupHNF' "seqvar" (\e (Seq _ b) -> b) i dt
    Seq a       b -> stepMsg "seqexp" $ MSt (ups' 1 1 t) (Seq (Var 0) $ up (Up 0 1) b) $  a: vs

    -- TODO: handle recursive constants
    Y (Lam x) -> stepMsg "Y" $ MSt (ups' 1 1 t) x $ e: vs

    App (Lam x) b | usedVar 0 x
                    -> stepMsg "app" $ MSt (ups' 1 1 t) x $ b: vs
    App (Lam x) b   -> stepMsg "appdel" $ tryRemoves (getFreeVars b) $ MSt t x vs
    App (Var i) _   -> lookupHNF' "appvar" (\e (App _ y) -> App e y) i dt
    App a b         -> stepMsg "appexp" $ MSt (ups' 1 1 t) (App (Var 0) $ up (Up 0 1) b) $  a: vs

    Case (Con cn i es) cs -> stepMsg "case" $ tryRemoves (foldMap (getFreeVars . snd) $ delElem i cs) $ (MSt t (foldl App (snd $ cs !! i) es) vs)
    Case (Var i) _ -> lookupHNF' "casevar" (\e (Case _ cs) -> Case e cs) i dt
    Case v cs      -> stepMsg "caseexp" $ MSt (ups' 1 1 t) (Case (Var 0) $ second (up (Up 0 1)) <$> cs) $ v: vs

    Op2 op (Int e) (Int f) -> return $ MSt t (int op e f) vs
      where
        int Add a b = Int $ a + b
        int Sub a b = Int $ a - b
        int Mod a b = Int $ a `mod` b
        int LessEq a b = if a <= b then T else F
        int EqInt a b = if a == b then T else F
    Op2 op (Var i) _       -> lookupHNF' "op2-1var" (\e (Op2 op _ y) -> Op2 op e y) i dt
    Op2 op _       (Var i) -> lookupHNF' "op2-2var" (\e (Op2 op x _) -> Op2 op x e) i dt
    Op2 op x@Int{} y       -> stepMsg "op2" $ MSt (ups' 1 1 t) (Op2 op x (Var 0)) $ y: vs
    Op2 op y       x@Int{} -> stepMsg "op2" $ MSt (ups' 1 1 t) (Op2 op (Var 0) x) $ y: vs
    Op2 op x       y       -> stepMsg "op2" $ MSt (ups' 1 2 t) (Op2 op (Var 0) (Var 1)) $ x: y: vs

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
