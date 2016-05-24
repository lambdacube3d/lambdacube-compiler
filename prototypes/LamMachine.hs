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
import Data.Word
import Data.Int
import Data.Monoid
import Data.Maybe
import Control.Arrow hiding ((<+>))
import Control.Category hiding ((.), id)
import Control.Monad
import Debug.Trace

import LambdaCube.Compiler.Pretty

import FreeVars

--------------------------------------------------------------------- data structures

data Exp_
    = Var_
    | Int_ !Int     -- ~ constructor with 0 args
    | Lam_ !Exp
    | Op1_ !Op1 !Exp
    | Con_ String !Int [Exp]
    | Case_ [String]{-for pretty print-} !Exp ![Exp]  -- --> simplify
    | Op2_ !Op2 !Exp !Exp
    deriving Eq

data Op1 = HNF_ !Int | YOp | Round
    deriving (Eq, Show)

data Op2 = AppOp | SeqOp | Add | Sub | Mod | LessEq | EqInt
    deriving (Eq, Show)

-- cached and compressed free variables set
data Exp = Exp_ !FV !Exp_
    deriving Eq

-- state of the machine
data MSt = MSt Exp ![Env]
    deriving Eq

data Env
    = ELet Exp
    | ELet1 Exp
    | EApp1 !Int Exp
    deriving Eq

--------------------------------------------------------------------- toolbox: pretty print

instance PShow Exp where
    pShow e@(Exp_ fv _) = --(("[" <> pShow fv <> "]") <+>) $
      case e of
        Var (Nat i)  -> DVar i
        Let a b     -> shLet (pShow a) $ pShow b
        App a b     -> DApp (pShow a) (pShow b)
        Seq a b     -> DOp "`seq`" (Infix 1) (pShow a) (pShow b)
        Lam e       -> shLam $ pShow e
        Con s i xs  -> foldl DApp (text s) $ pShow <$> xs
        Int i       -> pShow i
        Y e         -> "Y" `DApp` pShow e
        Op1 (HNF_ i) x -> DGlue (InfixL 40) (onred $ white $ if i == -1 then "this" else pShow i) $ DBrace (pShow x)
        Op1 o x     -> text (show o) `DApp` pShow x
        Op2 EqInt x y -> DOp "==" (Infix 4) (pShow x) (pShow y)
        Op2 Add x y -> DOp "+" (InfixL 6) (pShow x) (pShow y)
        Op2 o x y   -> text (show o) `DApp` pShow x `DApp` pShow y
        Case cn e xs -> DPreOp (-20) (ComplexAtom "case" (-10) (pShow e) (SimpleAtom "of"))
                        $ foldr1 DSemi [DArr_ "->" (text a) (pShow b) | (a, b) <- zip cn xs]

instance PShow MSt where
    pShow (MSt b bs) = pShow $ foldl f (HNF (-1) b) bs
      where
        f y = \case
            ELet x -> Let x y
            ELet1 x -> Let y x
            EApp1 i x -> HNF i $ App y x

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

pattern Int i       <- Exp_ _ (Int_ i)
  where Int i       =  Exp_ mempty $ Int_ i
pattern Op2 op a b  <- Exp_ u (Op2_ op (upp u -> a) (upp u -> b))
  where Op2 op a b  =  Exp_ s $ Op2_ op az bz where (s, az, bz) = delta2 a b
pattern Op1 op a    <- Exp_ u (Op1_ op (upp u -> a))
  where Op1 op (Exp_ ab x) = Exp_ ab $ Op1_ op $ Exp_ (delUnused ab) x
pattern Var' i      =  Exp_ (VarFV i) Var_
pattern Var i       =  Var' i
pattern Lam i       <- Exp_ u (Lam_ (upp (incFV u) -> i))
  where Lam (Exp_ vs ax) = Exp_ (del1 vs) $ Lam_ $ Exp_ (compact vs) ax
pattern Con a b i   <- Exp_ u (Con_ a b (map (upp u) -> i))
  where Con a b x   =  Exp_ s $ Con_ a b bz where (s, bz) = deltas x
pattern Case a b c  <- Exp_ u (Case_ a (upp u -> b) (map (upp u) -> c))
  where Case cn a b =  Exp_ s $ Case_ cn az bz where (s, az: bz) = deltas $ a: b

pattern Let i x     = App (Lam x) i
pattern Y a         = Op1 YOp a
pattern HNF i a     = Op1 (HNF_ i) a
pattern App a b     = Op2 AppOp a b
pattern Seq a b     = Op2 SeqOp a b

infixl 4 `App`

initSt :: Exp -> MSt
initSt e = MSt e []

-- for statistics
size :: MSt -> Int
size (MSt _ ys) = length ys

delta2 (Exp_ ua a) (Exp_ ub b) = (s, Exp_ (delFV ua s) a, Exp_ (delFV ub s) b)
  where
    s = ua <> ub

deltas [] = (mempty, [])
deltas [Exp_ x e] = (x, [Exp_ (delUnused x) e]) 
deltas [Exp_ ua a, Exp_ ub b] = (s, [Exp_ (delFV ua s) a, Exp_ (delFV ub s) b])
  where
    s = ua <> ub
deltas es = (s, [Exp_ (delFV u s) e | (u, Exp_ _ e) <- zip xs es])
  where
    xs = [ue | Exp_ ue _ <- es]

    s = mconcat xs

upp :: FV -> Exp -> Exp
upp a (Exp_ b e) = Exp_ (compFV a b) e

up l n (Exp_ us x) = Exp_ (upFV l n us) x

-- free variables set
fvs (Exp_ us _) = usedFVs us

usedVar i (Exp_ us _) = usedFV i us

down i (Exp_ us e) = Exp_ <$> downFV i us <*> pure e

---------------------------

tryRemoves xs = tryRemoves_ (Var' <$> xs)

tryRemoves_ [] dt = dt
tryRemoves_ (Var' i: vs) dt = maybe (tryRemoves_ vs dt) (\(is, st) -> tryRemoves_ (is ++ catMaybes (down i <$> vs)) st) $ tryRemove_ i dt
  where
    tryRemove_ i (MSt e es) = (\b (is, c) -> (is, MSt b c)) <$> down i e <*> downDown i es

    downDown i [] = Just ([], [])
    downDown 0 (ELet x: xs) = Just (Var' <$> fvs x, xs)
    downDown i (ELet x: xs) = (\x (is, xs) -> (up 0 1 <$> is, ELet x: xs)) <$> down (i-1) x <*> downDown (i-1) xs
    downDown i (ELet1 x: xs) = (\x (is, xs) -> (is, ELet1 x: xs)) <$> down (i+1) x <*> downDown i xs
    downDown i (EApp1 j x: xs) = (\x (is, xs) -> (is, EApp1 j x: xs)) <$> down i x <*> downDown i xs

----------------------------------------------------------- machine code begins here

justResult :: MSt -> MSt
justResult = steps 0 id (const ($)) (const (.))

hnf = justResult . initSt

----------------

type GenSteps e
    = (MSt -> e)
    -- -> (StepTag -> e)
    -> (StepTag -> (MSt -> e) -> MSt -> e)
    -> (StepTag -> (MSt -> e) -> (MSt -> e) -> MSt -> e)
    -> MSt -> e

type StepTag = String

steps :: forall e . Int -> GenSteps e
steps lev nostep {-ready-} bind cont dt@(MSt e vs) = case e of

    Int{} -> nostep dt --ready "hnf int"
    Lam{} -> nostep dt --ready "hnf lam"

    Con cn i xs
        | lz > 0 -> step "copy con" $ MSt (Con cn i xs') $ (ELet <$> zs) ++ vs  -- share complex constructor arguments
        | otherwise -> nostep dt --ready "hnf con"
      where
        lz = Nat $ length zs
        (xs', concat -> zs) = unzip $ f 0 xs
        f i [] = []
        f i (x: xs) | simple x = (up 0 lz x, []): f i xs
                    | otherwise = (Var' i, [up 0 (lz - i - 1) x]): f (i+1) xs

    Var i -> lookupHNF_ nostep "var" const i dt

    Seq a b -> case a of
        Int{}   -> step "seq" $ MSt b vs
        Lam{}   -> step "seq" $ tryRemoves (fvs a) $ MSt b vs
        Con{}   -> step "seq" $ tryRemoves (fvs a) $ MSt b vs
        Var i   -> lookupHNF' "seqvar" (\e (Seq _ b) -> b) i dt
        _       -> step "seqexp" $ MSt (Seq (Var 0) $ up 0 1 b) $ ELet a: vs

    -- TODO: handle recursive constants
    Y (Lam x)   -> step "Y" $ MSt x $ ELet e: vs

    App a b -> case a of
        Lam x | usedVar 0 x
                -> step "app"    $ MSt x $ ELet b: vs
        Lam x   -> step "appdel" $ tryRemoves (fvs b) $ MSt x vs
--        Var i   -> lookupHNF' "appvar" (\e (App _ y) -> App e y) i dt
        _       -> bind "app1" (hnf "app1 hnf" (step "appexp" . focus)) $ MSt a $ EApp1 lev b: vs
      where
        focus (MSt b xs) = MSt (App b c) xs'
          where
            (c, xs') = f xs
            f (EApp1 _ c: xs) = (c, xs)
            f (ELet x: (f -> (c, xs))) = (up 0 1 c, ELet x: xs)

    Case cn a cs -> case a of
        Con cn i es -> step "case" $ tryRemoves (nub $ foldMap fvs $ delElem i cs) $ MSt (foldl App (cs !! i) es) vs
        Var i   -> lookupHNF' "casevar" (\e (Case cn _ cs) -> Case cn e cs) i dt
        _       -> step "caseexp" $ MSt (Case cn (Var 0) $ up 0 1 <$> cs) $ ELet a: vs

    Op2 op x y -> case (x, y) of
        (Int e, Int f) -> step "op-done" $ MSt (int op e f) vs
          where
            int Add a b = Int $ a + b
            int Sub a b = Int $ a - b
            int Mod a b = Int $ a `mod` b
            int LessEq a b = if a <= b then T else F
            int EqInt a b = if a == b then T else F
        (Var i, _) -> lookupHNF' "op2-1var" (\e (Op2 op _ y) -> Op2 op e y) i dt
        (_, Var i) -> lookupHNF' "op2-2var" (\e (Op2 op x _) -> Op2 op x e) i dt
        (Int{}, _) -> step "op2" $ MSt (Op2 op x (Var 0)) $ ELet y: vs
        (_, Int{}) -> step "op2" $ MSt (Op2 op (Var 0) y) $ ELet x: vs
        _          -> step "op2" $ MSt (Op2 op (Var 0) (Var 1)) $ ELet x: ELet y: vs
  where
    rec i = steps i nostep bind cont

    step :: StepTag -> MSt -> e
    step t = bind t (rec lev)

    hnf :: StepTag -> (MSt -> e) -> MSt -> e
    hnf t f = cont t f (rec $ 1 + lev)

    hnfTag (MSt b c) = MSt (HNF lev b) c

    -- lookup var in head normal form
    lookupHNF_ :: (MSt -> e) -> StepTag -> (Exp -> Exp -> Exp) -> Nat -> MSt -> e
    lookupHNF_ end msg f i@(Nat i') dt = bind msg (hnf "lookup" shiftLookup) dt'
      where
        (path, dt') = shiftL [] i' $ hnfTag dt

        shiftLookup st
            = case boot (shiftR path . pakol') st of
                (q, MSt (HNF lev z) es) -> bind "shiftR" (tryRemove i) $ MSt (f (up 0 1 q) z) es
                st -> error $ "sl: " ++ ppShow st

        tryRemove i st = {-maybe (end st)-} (bind "remove" end) $ tryRemoves [i] st

    -- lookup & step
    lookupHNF' :: StepTag -> (Exp -> Exp -> Exp) -> Nat -> MSt -> e
    lookupHNF' msg f i dt = lookupHNF_ (rec lev) msg f i dt

    shiftL path 0 (MSt x (ELet e: es)) = (path, MSt e $ ELet1 x: es)
    shiftL path n (MSt x (ELet e: es)) = shiftL (TELet: path) (n-1) $ MSt (Let e x) es
    shiftL path n (MSt x (EApp1 i e: es)) = shiftL (TEApp1: path) n $ MSt (HNF i $ App x e) es
    shiftL path n (MSt x (ELet1 e: es)) = shiftL (TELet1: path) n $ MSt (Let x e) es
    shiftL path n st = error $ "shiftL: " ++ show (path, n) ++ "\n" ++ ppShow st

    boot c (MSt e (ELet x: xs)) = boot (c . pakol) (MSt (Let x e) xs)
    boot c st = c st

    pakol (MSt (Let x e) (ELet1 y: xs)) = MSt e (ELet1 (up 1 1 y): ELet x: xs)
    pakol' (MSt x (ELet1 y: xs)) = (x, MSt y (ELet x: xs))

    shiftR [] st = st
    shiftR (TELet: n) (y, MSt (Let e x) es) = shiftR n (up 0 1 y, MSt x $ ELet e: es)
    shiftR (TEApp1: n) (y, MSt (HNF l (App x e)) es) = shiftR n (y, MSt x $ EApp1 l e: es)
    shiftR (TELet1: n) (y, MSt (Let x e) es) = shiftR n (y, MSt x $ ELet1 e: es)
    shiftR path x = error $ "shiftR: " ++ show path ++ "\n" ++ ppShow x

    simple = \case
        Var{} -> True
        Int{} -> True
        _ -> False

    delElem i xs = take i xs ++ drop (i+1) xs

data TE = TELet | TELet1 | TEApp1
    deriving Show

---------------------------------------------------------------------------------------- examples

pPrint = putStrLn . ppShow

runMachinePure = pPrint . hnf

pattern F = Con "False" 0 []
pattern T = Con "True" 1 []
pattern Nil = Con "[]" 0 []
pattern Cons a b = Con "Cons" 1 [a, b]

caseBool x f t = Case ["False", "True"] x [f, t]
caseList x n c = Case ["[]", "Cons"] x [n, c]

id_ = Lam (Var 0)

if_ b t f = caseBool b f t

not_ x = caseBool x T F

test = id_ `App` id_ `App` id_ `App` id_ `App` Int 13

test' = id_ `App` (id_ `App` Int 14)

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

tests
    =   hnf test == hnf (Int 13)
    &&  hnf test' == hnf (Int 14)
    &&  hnf (Lam (Int 4) `App` Int 3) == hnf (Int 4)
    &&  hnf (t' 10) == hnf (Int 55)
    &&  hnf (t'' 10) == hnf (Int 55)



