{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

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

import LambdaCube.Compiler.Pretty hiding (expand)

import FreeVars

--------------------------------------------------------------------- data structures

data Exp_
    = Var_
    | Int_ !Int     -- ~ constructor with 0 args
    | Lam_ !Exp
    | Op1_ !Op1 !Exp
    | Con_   String{-for pretty print-}  !Int [Exp]
    | Case_ [String]{-for pretty print-} !Exp ![Exp]  -- TODO: simplify?
    | Op2_ !Op2 !Exp !Exp
    deriving (Eq, Show)

data Op1 = HNF_ | YOp | Round
    deriving (Eq, Show)

data Op2 = AppOp | SeqOp | Add | Sub | Mod | LessEq | EqInt
    deriving (Eq, Show)

-- cached and compressed free variables set
data Exp = Exp_ !FV !Exp_
    deriving (Eq, Show)

-------------------

data EnvPiece
    = ELet   Exp
    | EDLet1 DExp
    | ECase_  FV [String] [Exp]
    | EOp2_1 Op2 Exp
    | EOp2_2 Op2 Exp
    deriving (Eq, Show)

pattern ECase op e <- ECase_ u op (map (upp u) -> e)
  where ECase op b = ECase_ u op bz where (u, bz) = deltas b

pattern EnvPiece sfv p <- (getEnvPiece -> (sfv, p))
  where EnvPiece sfv@(SFV n u') = \case
            EOp2_1 op e -> EOp2_1 op (uppS sfv e)
            EOp2_2 op e -> EOp2_2 op (uppS sfv e)
            ECase_ u s es -> ECase_ (expand u' u) s es
            ELet (Exp_ u e) -> ELet (Exp_ (sDrop 1 u' `expand` u) e)
            EDLet1 z -> EDLet1 $ uppDE u' 1 z

getEnvPiece = \case
    EOp2_1 op (Exp_ u e) -> (SFV 0 u, EOp2_1 op (Exp_ (selfContract u) e))
    EOp2_2 op (Exp_ u e) -> (SFV 0 u, EOp2_2 op (Exp_ (selfContract u) e))
    ECase_ u s es -> (SFV 0 u, ECase_ (selfContract u) s es)
    ELet (Exp_ u e) -> (SFV 1 $ fv 1 0 u, ELet $ Exp_ (selfContract u) e)
    EDLet1 DExpNil -> (mempty, EDLet1 DExpNil)
    EDLet1 (DExpCons_ u x y) -> (SFV 0 $ sDrop 1 u, EDLet1 $ DExpCons_ (onTail selfContract 1 u) x y)

uppS (SFV _ x) (Exp_ u a) = Exp_ (expand x u) a

data DExp
    = DExpNil   -- variable
    | DExpCons_ FV EnvPiece DExp
    deriving (Eq, Show)

pattern DExpCons :: EnvPiece -> DExp -> DExp
pattern DExpCons a b <- (getDExpCons -> (a, b))
  where DExpCons (EnvPiece ux a) DExpNil = DExpCons_ (fromSFV s) (EnvPiece ux' a) DExpNil
          where (s, D1 ux') = diffT $ D1 ux
        DExpCons (ELet a) (dDown 0 -> Just d) = d
        DExpCons (EnvPiece ux a) (DExpCons_ u x y) = DExpCons_ (fromSFV s) (EnvPiece ux' a) (DExpCons_ u' x y)
          where (s, D2 (SFV 0 u') ux') = diffT $ D2 (SFV 0 u) ux

getDExpCons (DExpCons_ u x@(EnvPiece (SFV n _) _) b) = (uppEP u x, uppDE u n b)

uppEP u (EnvPiece (SFV n x) y) = EnvPiece (SFV n $ onTail (u `expand`) n x) y      -- ???

upP i j = uppEP $ mkUp i j

incFV' (SFV n u) = SFV (n + 1) $ incFV u

uppDE :: FV -> Nat -> DExp -> DExp
uppDE a _ DExpNil = DExpNil
uppDE a n (DExpCons_ u x y) = DExpCons_ (onTail (expand a) n u) x y

data DEnv
    = DEnvNil
    | DEnvCons EnvPiece DEnv
    deriving (Eq, Show)

-- state of the machine
data MSt = MSt DEnv Exp
    deriving (Eq, Show)

infixr 4 `DEnvCons`, `DExpCons`

dDown i DExpNil = Just DExpNil
dDown i (DExpCons_ u a b) = DExpCons_ <$> downFV i u <*> pure a <*> pure b

--------------------------------------------------------------------- toolbox: pretty print

class ViewShow a where
    viewShow :: Bool -> a -> Doc

instance ViewShow Exp where
  viewShow vi = pShow where
    pShow e@(Exp_ fv x) = showFE green vi fv $
      case {-if vi then Exp_ (selfContract fv) x else-} e of
        Var (Nat i)  -> DVar i
        Let a b     -> shLet (pShow a) $ pShow b
        Seq a b     -> DOp "`seq`" (Infix 1) (pShow a) (pShow b)
        Lam e       -> shLam $ pShow e
        Con s i xs  -> foldl DApp (text s) $ pShow <$> xs
        Int i       -> pShow' i
        Y e         -> "Y" `DApp` pShow e
        InHNF x     -> DBrace (pShow x)
        Op1 o x     -> text (show o) `DApp` pShow x
        Op2 o x y   -> shOp2 o (pShow x) (pShow y)
        Case cn e xs -> shCase cn (pShow e) (pShow <$> xs)
        Exp_ u Var_ -> onblue $ pShow' u
        e -> error $ "pShow @Exp: " ++ show e

glueTo = DGlue (InfixR 40)

shCase cn e xs = DPreOp (-20) (ComplexAtom "case" (-10) e (SimpleAtom "of"))
                        $ foldr1 DSemi [DArr_ "->" (text a) b | (a, b) <- zip cn xs]

shOp2 AppOp x y = DApp x y
shOp2 EqInt x y = DOp "==" (Infix 4) x y
shOp2 Add x y   = DOp "+" (InfixL 6) x y
shOp2 o x y     = text (show o) `DApp` x `DApp` y

showFE c True fv | fv /= mempty = DGlue (InfixL 40) (c $ pShow' fv)
showFE _ _ _ = id

pShow' = pShow

instance ViewShow MSt where
    viewShow vi (MSt env e) = g (onred $ white $ pShow e) env
      where
        pShow = viewShow vi

        g y DEnvNil = y
        g y z@(DEnvCons p env) = flip g env $ {-showFE red vi (case p of EnvPiece f _ -> f) $-} case p of
            EDLet1 x -> shLet y (h x)
            ELet x -> shLet (pShow x) y
            ECase cns xs -> shCase cns y (pShow <$> xs)
            EOp2_1 op x -> shOp2 op y (pShow x)
            EOp2_2 op x -> shOp2 op (pShow x) y

        h DExpNil = onred $ white "*" --TODO?
        h z@(DExpCons p (h -> y)) = showFE blue vi (case p of EnvPiece f _ -> f) $ case p of
            EDLet1 x -> shLet y (h x)
            ELet x -> shLet (pShow x) y
            ECase cns xs -> shCase cns y (pShow <$> xs)
            EOp2_1 op x -> shOp2 op y (pShow x)
            EOp2_2 op x -> shOp2 op (pShow x) y

instance PShow MSt where pShow = viewShow False


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
  where Op1 op (Exp_ ab x) = Exp_ ab $ Op1_ op $ Exp_ (selfContract ab) x
pattern Var' i      =  Exp_ (VarFV i) Var_
pattern Var i       =  Var' i
pattern Lam i       <- Exp_ u (Lam_ (upp (incFV u) -> i))
  where Lam (Exp_ vs ax) = Exp_ (sDrop 1 vs) $ Lam_ $ Exp_ (compact vs) ax
pattern Con a b i   <- Exp_ u (Con_ a b (map (upp u) -> i))
  where Con a b x   =  Exp_ s $ Con_ a b bz where (s, bz) = deltas x
pattern Case a b c  <- Exp_ u (Case_ a (upp u -> b) (map (upp u) -> c))
  where Case cn a b =  Exp_ s $ Case_ cn az bz where (s, az: bz) = deltas $ a: b

pattern Let i x    <- App (Lam x) i
  where Let i (down 0 -> Just x) = x
        Let i x     = App (Lam x) i
pattern Y a         = Op1 YOp a
pattern InHNF a     = Op1 HNF_ a
pattern App a b     = Op2 AppOp a b
pattern Seq a b     = Op2 SeqOp a b

infixl 4 `App`

delta2 (Exp_ ua a) (Exp_ ub b) = (s, Exp_ ua' a, Exp_ ub' b)
  where
    (s, ua', ub') = delta2' ua ub

delta2' ua ub = (s, primContract s ua, primContract s ub)
  where
    s = ua <> ub

deltas [] = (mempty, [])
deltas [Exp_ x e] = (x, [Exp_ (selfContract x) e]) 
deltas [Exp_ ua a, Exp_ ub b] = (s, [Exp_ (primContract s ua) a, Exp_ (primContract s ub) b])
  where
    s = ua <> ub
deltas es = (s, [Exp_ (primContract s u) e | (u, Exp_ _ e) <- zip xs es])
  where
    xs = [ue | Exp_ ue _ <- es]

    s = mconcat xs

upp :: FV -> Exp -> Exp
upp a (Exp_ b e) = Exp_ (expand a b) e

up l n (Exp_ us x) = Exp_ (upFV l n us) x

-- free variables set
fvs (Exp_ us _) = usedFVs us

usedVar i (Exp_ us _) = sIndex us i

usedVar' i DExpNil = False
usedVar' i (DExpCons_ u _ _) = sIndex u i

down i (Exp_ us e) = Exp_ <$> downFV i us <*> pure e

---------------------------

initSt :: Exp -> MSt
initSt e = MSt DEnvNil e

----------------------------------------------------------- machine code begins here

justResult :: MSt -> MSt
justResult = steps 0 id (const ($)) (const (.))

hnf = justResult . initSt

----------------

inHNF (InHNF a) = InHNF a
inHNF a = InHNF a

type GenSteps e
    = (MSt -> e)
   -> (StepTag -> (MSt -> e) -> MSt -> e)
   -> (StepTag -> (MSt -> e) -> (MSt -> e) -> MSt -> e)
   -> MSt -> e

type StepTag = String

focusNotUsed (MSt (EDLet1 x `DEnvCons` _) _) = not $ usedVar' 0 x
focusNotUsed _ = True

steps :: forall e . Int -> GenSteps e
steps lev nostep bind cont (MSt vs e) = case e of

    Int{} -> step "int hnf" $ MSt vs $ InHNF e
    Lam{} -> step "lam hnf" $ MSt vs $ InHNF e

    Con cn i xs
        | lz == 0 || focusNotUsed (MSt vs e) -> step "con hnf" $ MSt vs $ InHNF e
        | otherwise -> step "copy con" $ MSt (foldr DEnvCons vs $ ELet <$> zs) $ InHNF $ Con cn i xs'  -- share complex constructor arguments
      where
        lz = Nat $ length zs
        (xs', concat -> zs) = unzip $ f 0 xs
        f i [] = []
        f i (x: xs) | simple x = (up 0 lz x, []): f i xs
                    | otherwise = (Var' i, [up 0 (lz - i - 1) x]): f (i+1) xs

    -- TODO: handle recursive constants
    Y x             -> step "Y"     $ MSt vs $ App x (Y x)

    Var i           -> step "var"   $ zipDown i DExpNil vs
    Seq a b         -> step "seq"   $ MSt (EOp2_1 SeqOp b `DEnvCons` vs) a
    Case cns a cs   -> step "case"  $ MSt (ECase cns cs `DEnvCons` vs) a
    Op2 op a b      -> step "op2_1" $ MSt (EOp2_1 op b `DEnvCons` vs) a

    InHNF a -> case vs of

        DEnvNil -> bind "whnf" nostep $ MSt DEnvNil $ InHNF a

        ELet x `DEnvCons` vs -> step "goUp" $ MSt vs $ inHNF $ Let x $ InHNF a
        x `DEnvCons` vs | Let y e <- a -> step "pakol" $ MSt (upP 0 1 x `DEnvCons` ELet y `DEnvCons` vs) e
        x `DEnvCons` vs -> case x of
            EOp2_1 SeqOp b -> case a of
                Int{}   -> step "seq" $ MSt vs b
                Lam{}   -> step "seq" $ MSt vs b   -- TODO: remove a
                Con{}   -> step "seq" $ MSt vs b   -- TODO: remove a
                _       -> step "seq hnf" $ MSt vs $ InHNF $ Seq (InHNF a) b
            EOp2_1 AppOp b -> case a of
                Lam x | usedVar 0 x -> step "app"    $ MSt (ELet b `DEnvCons` vs) x
                      | otherwise   -> step "appdel" $ MSt vs x   -- TODO: remove b
                _     -> step "app hnf" $ MSt vs $ InHNF $ App (InHNF a) b
            ECase cns cs -> case a of
                Con cn i es -> step "case" $ MSt vs $ foldl App (cs !! i) es  -- TODO: remove unused cases
                _           -> step "case hnf" $ MSt vs $ InHNF $ Case cns (InHNF a) cs
            EOp2_1 op b -> step "op2_2 hnf" $ MSt (EOp2_2 op (InHNF a) `DEnvCons` vs) b
            EOp2_2 op b -> case (b, a) of
                (InHNF (Int e), Int f) -> step "op-done" $ MSt vs (int op e f)
                  where
                    int Add a b = Int $ a + b
                    int Sub a b = Int $ a - b
                    int Mod a b = Int $ a `mod` b
                    int LessEq a b = if a <= b then T else F
                    int EqInt a b = if a == b then T else F
                _ -> step "op2 hnf" $ MSt vs $ InHNF $ Op2 op b (InHNF a)
            EDLet1 (dDown 0 -> Just d) -> zipUp a vs d
            EDLet1 d -> zipUp (up 0 1 a) (ELet (InHNF a) `DEnvCons` vs) d

  where
    zipDown 0 e (ELet z `DEnvCons` zs) = MSt (EDLet1 e `DEnvCons` zs) z
    zipDown j e (z@ELet{} `DEnvCons` zs) = zipDown (j-1) (z `DExpCons` e) zs
    zipDown j e (z `DEnvCons` zs) = zipDown j (z `DExpCons` e) zs

    zipUp x xs DExpNil = step "zipUp ready" $ MSt xs x
    zipUp x xs (DExpCons a@ELet{} as) = zipUp (up 0 1 x) (a `DEnvCons` xs) as
    zipUp x xs (DExpCons a as) = zipUp x (a `DEnvCons` xs) as

    rec i = steps i nostep bind cont

    step :: StepTag -> MSt -> e
    step t = bind t (rec lev)
{-
    hnf :: StepTag -> (MSt -> e) -> MSt -> e
    hnf t f = bind ("hnf " ++ t) $ cont t f (rec (1 + lev))

    hnf' :: StepTag -> MSt -> e
    hnf' t = hnf t $ bind ("focus " ++ t) $ goUp t 0
-}

simple = \case
    Var{} -> True
    Int{} -> True
    _ -> False

delElem i xs = take i xs ++ drop (i+1) xs

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

test'' = Lam (Int 4) `App` Int 3

tests
    =   hnf test == hnf (Int 13)
    &&  hnf test' == hnf (Int 14)
    &&  hnf test'' == hnf (Int 4)
    &&  hnf (t' 10) == hnf (Int 55)
    &&  hnf (t'' 10) == hnf (Int 55)



