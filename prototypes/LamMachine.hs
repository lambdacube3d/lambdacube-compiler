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

data Lit
    = LInt  !Int
    | LChar !Char
    | LFloat !Double
    deriving Eq

data Exp_
    = Var_
    | Lam_ VarInfo !Exp
    | Let_ VarInfo !Exp !Exp
    | Con_  ConInfo !Int [Exp]
    | Case_ CaseInfo !Exp ![Exp]
    | Lit_ !Lit
    | Op1_ !Op1 !Exp
    | Op2_ !Op2 !Exp !Exp
    deriving (Eq, Show)

data Op1 = HNFMark | YOp | Round
    deriving (Eq, Show)

data Op2 = AppOp | SeqOp | Add | Sub | Mod | LessEq | EqInt
    deriving (Eq, Show)

pattern Y a         = Op1 YOp a
pattern App a b     = Op2 AppOp a b
pattern Seq a b     = Op2 SeqOp a b
pattern Int i       = Lit (LInt i)

infixl 4 `App`

-- cached and compressed free variables set
data Exp = Exp !FV !Exp_
    deriving (Eq, Show)

data EnvPiece
    = ELet   VarInfo !Exp
    | EDLet1 VarInfo !DExp
    | ECase_ CaseInfo !FV ![Exp]
    | EOp2_1 !Op2 !Exp
    | EOp2_2 !Op2 !Exp
    deriving (Eq, Show)

data DExp
    = DExpNil   -- variable
    | DExpCons_ !FV !EnvPiece !DExp
    deriving (Eq, Show)

data DEnv
    = DEnvNil
    | DEnvCons !EnvPiece !DEnv
    deriving (Eq, Show)

-- state of the machine
data MSt = MSt !DEnv !Exp
    deriving (Eq, Show)

--------- pretty print info

type VarInfo = String
type ConInfo = String
type CaseInfo = [(String, [String])]

--------------------------------------------------------------------- pattern synonyms

infixr 4 `DEnvCons`, `DExpCons`

pattern ECase op e <- ECase_ op u (map (upp u) -> e)
  where ECase op b = ECase_ op u bz where (u, bz) = deltas b

pattern EnvPiece sfv p <- (getEnvPiece -> (sfv, p))
  where EnvPiece sfv@(SFV n u') = \case
            EOp2_1 op e -> EOp2_1 op (uppS sfv e)
            EOp2_2 op e -> EOp2_2 op (uppS sfv e)
            ECase_ s u es -> ECase_ s (expand u' u) es
            ELet n (Exp u e) -> ELet n (Exp (sDrop 1 u' `expand` u) e)
            EDLet1 n z -> EDLet1 n $ uppDE u' 1 z

getEnvPiece = \case
    EOp2_1 op (Exp u e) -> (SFV 0 u, EOp2_1 op (Exp (selfContract u) e))
    EOp2_2 op (Exp u e) -> (SFV 0 u, EOp2_2 op (Exp (selfContract u) e))
    ECase_ s u es -> (SFV 0 u, ECase_ s (selfContract u) es)
    ELet n (Exp u e) -> (SFV 1 $ fv 1 0 u, ELet n $ Exp (selfContract u) e)
    EDLet1 n DExpNil -> (mempty, EDLet1 n DExpNil)
    EDLet1 n (DExpCons_ u x y) -> (SFV 0 $ sDrop 1 u, EDLet1 n $ DExpCons_ (onTail selfContract 1 u) x y)

uppS (SFV _ x) (Exp u a) = Exp (expand x u) a

pattern DExpCons :: EnvPiece -> DExp -> DExp
pattern DExpCons a b <- (getDExpCons -> (a, b))
  where DExpCons (EnvPiece ux a) DExpNil = DExpCons_ (fromSFV s) (EnvPiece ux' a) DExpNil
          where (s, D1 ux') = diffT $ D1 ux
        DExpCons (ELet _ a) (dDown 0 -> Just d) = d
        DExpCons (EnvPiece ux a) (DExpCons_ u x y) = DExpCons_ (fromSFV s) (EnvPiece ux' a) (DExpCons_ u' x y)
          where (s, D2 (SFV 0 u') ux') = diffT $ D2 (SFV 0 u) ux

getDExpCons (DExpCons_ u x@(EnvPiece (SFV n _) _) b) = (uppEP u x, uppDE u n b)

uppEP u (EnvPiece (SFV n x) y) = EnvPiece (SFV n $ onTail (u `expand`) n x) y

upP i j = uppEP $ mkUp i j

incFV' (SFV n u) = SFV (n + 1) $ incFV u

uppDE :: FV -> Nat -> DExp -> DExp
uppDE a _ DExpNil = DExpNil
uppDE a n (DExpCons_ u x y) = DExpCons_ (onTail (expand a) n u) x y

dDown i DExpNil = Just DExpNil
dDown i (DExpCons_ u a b) = DExpCons_ <$> downFV i u <*> pure a <*> pure b

---------------------------------------------------------------------

pattern Lit i       <- Exp _ (Lit_ i)
  where Lit i       =  Exp mempty $ Lit_ i
pattern Op2 op a b  <- Exp u (Op2_ op (upp u -> a) (upp u -> b))
  where Op2 op a b  =  Exp s $ Op2_ op az bz where (s, az, bz) = delta2 a b
pattern Op1 op a    <- Exp u (Op1_ op (upp u -> a))
  where Op1 op (Exp ab x) = Exp ab $ Op1_ op $ Exp (selfContract ab) x
pattern Var' i      =  Exp (VarFV i) Var_
pattern Var i       =  Var' i
pattern Lam n i           <- Exp u (Lam_ n (upp (incFV u) -> i))
  where Lam n (Exp vs ax) = Exp (sDrop 1 vs) $ Lam_ n $ Exp (compact vs) ax
pattern Con a b i   <- Exp u (Con_ a b (map (upp u) -> i))
  where Con a b x   =  Exp s $ Con_ a b bz where (s, bz) = deltas x
pattern Case a b c  <- Exp u (Case_ a (upp u -> b) (map (upp u) -> c))
  where Case cn a b =  Exp s $ Case_ cn az bz where (s, az: bz) = deltas $ a: b

pattern Let n i x   <- Exp u (Let_ n (upp u -> i) (upp (incFV u) -> x))
  where Let _ _ (down 0 -> Just x) = x
        Let n a b   =  Exp s (Let_ n a' b') where (s, a', Lam _ b') = delta2 a $ Lam n b

pattern InHNF a    <- (getHNF -> Just a)
  where InHNF a@Lit{}        = a
        InHNF a@Lam{}        = a
        InHNF a@(Op1 HNFMark _) = a
        InHNF a              = Op1 HNFMark a

getHNF x = case x of
    Lit{} -> Just x
    Lam{} -> Just x
    Op1 HNFMark a -> Just a
    _ -> Nothing

delta2 (Exp ua a) (Exp ub b) = (s, Exp ua' a, Exp ub' b)
  where
    (s, ua', ub') = delta2' ua ub

delta2' ua ub = (s, primContract s ua, primContract s ub)
  where
    s = ua <> ub

deltas [] = (mempty, [])
deltas [Exp x e] = (x, [Exp (selfContract x) e]) 
deltas [Exp ua a, Exp ub b] = (s, [Exp (primContract s ua) a, Exp (primContract s ub) b])
  where
    s = ua <> ub
deltas es = (s, [Exp (primContract s u) e | (u, Exp _ e) <- zip xs es])
  where
    xs = [ue | Exp ue _ <- es]

    s = mconcat xs

upp :: FV -> Exp -> Exp
upp a (Exp b e) = Exp (expand a b) e

up l n (Exp us x) = Exp (upFV l n us) x

-- free variables set
--fvs (Exp us _) = usedFVs us

usedVar i (Exp us _) = sIndex us i

usedVar' i DExpNil = False
usedVar' i (DExpCons_ u _ _) = sIndex u i

down i (Exp us e) = Exp <$> downFV i us <*> pure e

---------------------------

initSt :: Exp -> MSt
initSt e = MSt DEnvNil e

----------------------------------------------------------- machine code begins here

justResult :: MSt -> MSt
justResult st = steps st (\_ s -> justResult s) st

hnf = justResult . initSt

----------------

data StepTag = Begin String | End String | Step String
  deriving Show

type GenSteps e
    = e
   -> (StepTag -> MSt -> e)
   -> MSt -> e

focusNotUsed (MSt (EDLet1 _ x `DEnvCons` _) _) = not $ usedVar' 0 x
focusNotUsed _ = True

inHNF :: MSt -> Bool
inHNF (MSt _ (InHNF _)) = True
inHNF _ = False

steps :: forall e . GenSteps e
steps nostep bind (MSt vs e) = case e of

    Con cn i xs
        | lz == 0 || focusNotUsed (MSt vs e) -> step (cn ++ " hnf") $ MSt vs $ InHNF e
        | otherwise -> step (cn ++ " copy") $ MSt (foldr DEnvCons vs $ ELet "" <$> zs) $ InHNF $ Con cn i xs'  -- share complex constructor arguments
      where
        lz = Nat $ length zs
        (xs', concat -> zs) = unzip $ f 0 xs
        f i [] = []
        f i (x: xs) | simple x = (up 0 lz x, []): f i xs
                    | otherwise = (Var' i, [up 0 (lz - i - 1) x]): f (i+1) xs

    -- TODO: handle recursive constants
    Y x             -> step "Y"     $ MSt vs $ App x (Y x)

    Var i           -> begin "var"   $ zipDown i DExpNil vs
    Case cns a cs   -> begin "case"  $ MSt (ECase cns cs `DEnvCons` vs) a
    Op2 op a b      -> begin (show op) $ MSt (EOp2_1 op b `DEnvCons` vs) a

    InHNF a -> case vs of

        DEnvNil -> nostep

        ELet n x `DEnvCons` vs -> step "goUp" $ MSt vs $ InHNF $ Let n x $ InHNF a
        x `DEnvCons` vs | Let n y e <- a -> step "pakol" $ MSt (upP 0 1 x `DEnvCons` ELet n y `DEnvCons` vs) e
        x `DEnvCons` vs -> case x of
            ECase cns cs -> end "case" $ case a of
                Con cn i es -> MSt vs $ foldl App (cs !! i) es  -- TODO: remove unused cases
                _           -> MSt vs $ InHNF $ Case cns (InHNF a) cs
            EOp2_1 AppOp b -> end "AppOp" $ case a of
                Lam _ (down 0 -> Just x) -> MSt vs x   -- TODO: remove b
                Lam n x -> MSt (ELet n b `DEnvCons` vs) x
                _       -> MSt vs $ InHNF $ App (InHNF a) b
            EOp2_1 SeqOp b -> end "SeqOp" $ case a of
                Lit{}   -> MSt vs b
                Lam{}   -> MSt vs b   -- TODO: remove a
                Con{}   -> MSt vs b   -- TODO: remove a
                _       -> MSt vs $ InHNF $ Seq (InHNF a) b
            EOp2_1 op b -> next (show op) $ MSt (EOp2_2 op (InHNF a) `DEnvCons` vs) b
            EOp2_2 op b -> end (show op) $ case (b, a) of
                (Int e, Int f) -> MSt vs (int op e f)
                  where
                    int Add a b = Int $ a + b
                    int Sub a b = Int $ a - b
                    int Mod a b = Int $ a `mod` b
                    int LessEq a b = if a <= b then T else F
                    int EqInt a b = if a == b then T else F
                _ -> MSt vs $ InHNF $ Op2 op b (InHNF a)
            EDLet1 _ (dDown 0 -> Just d) -> zipUp (InHNF a) vs d
            EDLet1 n d -> zipUp (up 0 1 a) (ELet n (InHNF a) `DEnvCons` vs) d

  where
    zipDown 0 e (ELet n z `DEnvCons` zs) = MSt (EDLet1 n e `DEnvCons` zs) z
    zipDown j e (z@ELet{} `DEnvCons` zs) = zipDown (j-1) (z `DExpCons` e) zs
    zipDown j e (z `DEnvCons` zs) = zipDown j (z `DExpCons` e) zs

    zipUp x xs DExpNil = end "var" $ MSt xs x
    zipUp x xs (DExpCons a@ELet{} as) = zipUp (up 0 1 x) (a `DEnvCons` xs) as
    zipUp x xs (DExpCons a as) = zipUp x (a `DEnvCons` xs) as

    begin t = bind (Begin t)
    next t  = bind (Step t)
    end t   = bind (End t)
    step t  = bind (Step t)

simple = \case
    Var{} -> True
    Lit{} -> True
    _ -> False

delElem i xs = take i xs ++ drop (i+1) xs

--------------------------------------------------------------------- toolbox: pretty print

instance PShow Lit where
    pShow (LInt i) = pShow i

instance Show Lit where show = ppShow

class ViewShow a where
    viewShow :: Bool -> a -> Doc

instance ViewShow Exp where
  viewShow vi = pShow where
    pShow e@(Exp fv x) = showFE green vi fv $
      case {-if vi then Exp_ (selfContract fv) x else-} e of
        Var (Nat i)  -> DVar i
        Let n a b   -> shLet n (pShow a) $ pShow b
        Lam n e     -> shLam n $ pShow e
        Con s i xs  -> foldl DApp (text s) $ pShow <$> xs
        Lit i       -> pShow' i
        Y e         -> "Y" `DApp` pShow e
        InHNF x     -> DBrace (pShow x)
        Op1 o x     -> text (show o) `DApp` pShow x
        Op2 o x y   -> shOp2 o (pShow x) (pShow y)
        Case cn e xs -> shCase cn (pShow e) pShow xs
--        Exp_ u Var_ -> onblue $ pShow' u
        e -> error $ "pShow @Exp: " ++ show e

glueTo = DGlue (InfixR 40)

app_ (Lam _ x) _ = x
app_ x y = App x y

shCase cn e f xs = DPreOp (-20) (ComplexAtom "case" (-10) e (SimpleAtom "of"))
                        $ foldr1 DSemi [foldr DFreshName (DArr_ "->" (foldl DApp (text a) $ DVar <$> reverse [0..length n - 1]) (f $ foldl app_ b $ Var . Nat <$> [0..length n - 1])) $ Just <$> n | ((a, n), b) <- zip cn xs]

shOp2 AppOp x y = DApp x y
shOp2 SeqOp a b = DOp "`seq`" (Infix 1) a b
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
        g y z@(DEnvCons p env) = flip g env $ case p of
            EDLet1 n x -> shLet n y (h 0 x)
            ELet n x -> shLet n (pShow x) y
            ECase cns xs -> shCase cns y pShow xs
            EOp2_1 op x -> shOp2 op y (pShow x)
            EOp2_2 op x -> shOp2 op (pShow x) y

        h n DExpNil = onred $ white $ DVar n
        h n z@(DExpCons p (h (adj p n) -> y)) = showFE blue vi (case p of EnvPiece f _ -> f) $ case p of
            EDLet1 n x -> shLet n y (h 0 x)
            ELet n x -> shLet n (pShow x) y
            ECase cns xs -> shCase cns y pShow xs
            EOp2_1 op x -> shOp2 op y (pShow x)
            EOp2_2 op x -> shOp2 op (pShow x) y

        adj p n = case p of
            ELet{} -> n + 1
            _ -> n

instance PShow MSt where pShow = viewShow False


shUps a b = DPreOp (-20) (SimpleAtom $ show a) b
shUps' a x b = DPreOp (-20) (SimpleAtom $ show a ++ show x) b

shLam n b = DFreshName (Just n) $ showLam (DVar 0) b

showLam x (DFreshName u d) = DFreshName u $ showLam (DUp 0 x) d
showLam x (DLam xs y) = DLam (DSep (InfixR 11) x xs) y
showLam x y = DLam x y

shLet n a b = DFreshName (Just n) $ showLet (DLet "=" (shVar 0) $ DUp 0 a) b

showLet x (DFreshName u d) = DFreshName u $ showLet (DUp 0 x) d
showLet x (DLet' xs y) = DLet' (DSemi x xs) y
showLet x y = DLet' x y


---------------------------------------------------------------------------------------- examples

pPrint = putStrLn . ppShow

runMachinePure = pPrint . hnf

pattern F = Con "False" 0 []
pattern T = Con "True" 1 []
pattern Nil = Con "[]" 0 []
pattern Cons a b = Con "Cons" 1 [a, b]

caseBool x f t = Case [("False", []), ("True", [])] x [f, t]
caseList x n c = Case [("[]", []), ("Cons", ["c", "cs"])] x [n, c]

id_ = Lam "x" (Var 0)

if_ b t f = caseBool b f t

not_ x = caseBool x T F

test = id_ `App` id_ `App` id_ `App` id_ `App` Int 13

test' = id_ `App` (id_ `App` Int 14)

foldr_ f e = Y $ Lam "g" $ Lam "as" $ caseList (Var 0) (up 0 2 e) (Lam "x" $ Lam "xs" $ up 0 4 f `App` Var 1 `App` (Var 3 `App` Var 0))

filter_ p = foldr_ (Lam "y" $ Lam "ys" $ if_ (p `App` Var 1) (Cons (Var 1) (Var 0)) (Var 0)) Nil

and2 a b = if_ a b F

and_ = foldr_ (Lam "a" $ Lam "b" $ and2 (Var 1) (Var 0)) T

map_ f = foldr_ (Lam "z" $ Lam "zs" $ Cons (f (Var 1)) (Var 0)) Nil

neq a b = not_ $ Op2 EqInt a b

from_ = Y $ Lam "from" $ Lam "n" $ Cons (Var 0) $ Var 1 `App` Op2 Add (Var 0) (Int 1)

idx xs n = caseList xs undefined $ Lam "q" $ Lam "qs" $ if_ (Op2 EqInt n $ Int 0) (Var 1) $ idx (Var 0) (Op2 Sub n $ Int 1)

t = runMachinePure $ idx (from_ `App` Int 3) (Int 5)

takeWhile_ p xs = caseList xs Nil $ Lam "x" $ Lam "xs" $ if_ (p (Var 1)) (Cons (Var 1) $ takeWhile_ p (Var 0)) Nil

sum_ = foldr_ (Lam "a" $ Lam "b" $ Op2 Add (Var 1) (Var 0)) (Int 0)

sum' = Y $ Lam "sum" $ Lam "xs" $ caseList (Var 0) (Int 0) $ Lam "y" $ Lam "ys" $ Op2 Add (Var 1) $ Var 3 `App` Var 0

infixl 4 `sApp`

sApp a b = Seq b (App a b)

{-
accsum acc [] = acc
accsum acc (x: xs) = let z = acc + x `seq` accsum z xs
-}
accsum = Y $ Lam "accsum" $ Lam "acc" $ Lam "xs" $ caseList (Var 0) (Var 1) $ Lam "y" $ Lam "ys" $ Var 4 `sApp` Op2 Add (Var 3) (Var 1) `App` Var 0

fromTo = Y $ Lam "fromTo" $ Lam "begin" $ Lam "end" $ Cons (Var 1) $ if_ (Op2 EqInt (Var 0) (Var 1)) Nil $ Var 2 `App` Op2 Add (Var 1) (Int 1) `App` Var 0

t' n = sum' `App` (fromTo `App` Int 0 `App` Int n) --  takeWhile_ (\x -> Op2 LessEq x $ Int 3) (from_ `App` Int 0)

t'' n = accsum `App` Int 0 `App` (fromTo `App` Int 0 `App` Int n) --  takeWhile_ (\x -> Op2 LessEq x $ Int 3) (from_ `App` Int 0)

{- TODO

primes :: [Int]
primes = 2:3: filter (\n -> and $ map (\p -> n `mod` p /= 0) (takeWhile (\x -> x <= iSqrt n) primes)) (from 5)


main = primes !! 3000
-}

twice = Lam "f" $ Lam "x" $ Var 1 `App` (Var 1 `App` Var 0)
twice2 = Lam "f" $ Lam "x" $ Var 1 `sApp` (Var 1 `App` Var 0)

inc = Lam "n" $ Op2 Add (Var 0) (Int 1)

test'' = Lam "f" (Int 4) `App` Int 3

twiceTest n = (Lam "twice" $ (iterate (`App` Var 0) (Var 0) !! n) `App` inc `App` Int 0) `App` twice
twiceTest2 = twice2 `App` twice2 `App` twice2 `App` twice2 `App` inc `App` Int 0

tests
    =   hnf test == hnf (Int 13)
    &&  hnf test' == hnf (Int 14)
    &&  hnf test'' == hnf (Int 4)
    &&  hnf (t' 10) == hnf (Int 55)
    &&  hnf (t'' 10) == hnf (Int 55)



