{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE BangPatterns #-}

--module LamMachineV2 where

import Data.List
import Data.Word
import Data.Int
import Data.Monoid
import Data.Maybe
import Data.Bits
import Data.String
import qualified Data.Vector as PV
import qualified Data.Vector.Mutable as V
import qualified Data.Vector.Unboxed.Mutable as UV
import qualified Data.Vector.Unboxed as PUV
import Control.Arrow hiding ((<+>))
import Control.Category hiding ((.), id)
import Control.Monad
import Control.Monad.Writer
import Control.Monad.ST
import Debug.Trace
import qualified Text.Show.Pretty as P
import System.Environment

import LambdaCube.Compiler.Pretty

-----------------------------------------

class HasLen v where
    len :: v -> Int

class (HasLen v, Monad m) => VecLike v m where
    type VElem v
    new     :: Int -> m v
    append  :: v -> (Int, [VElem v]) -> m v
    read_   :: v -> Int -> m (VElem v)
    freezedRead :: v -> m (Int -> VElem v)
    write   :: v -> Int -> VElem v -> m v
    modify  :: v -> Int -> (VElem v -> VElem v) -> m v
    vToList :: v -> m [VElem v]

-----------------

data Vec s a = Vec !Int !(V.STVector s a)

instance HasLen (Vec s a) where
    len (Vec n _) = n

instance VecLike (Vec s a) (ST s) where
    type VElem (Vec s a) = a

    new n | n < 0 = error $ "new: " ++ show n
    new n = Vec 0 <$> V.unsafeNew n

    append (Vec n v@(V.length -> m)) (k, xs) = do
        let !nk = n + k
        v' <- if m >= nk then return v else V.unsafeGrow v (2 * nk - m)
        zipWithM_ (V.unsafeWrite v') [n..] xs
        return $ Vec nk v'

    read_ (Vec _ v) i = V.unsafeRead v i

    freezedRead (Vec _ v) = PV.unsafeFreeze v <&> PV.unsafeIndex

    write x@(Vec _ v) i a = V.unsafeWrite v i a >> return x

    modify x@(Vec _ v) i a = V.unsafeModify v a i >> return x

    vToList (Vec n v) = mapM (V.unsafeRead v) [0..n-1]

--------------------------------------------------------------------------- data structures

data Lit
    = LInt   !Int
    | LChar  !Char
    | LFloat !Double
    deriving Eq

data Exp
    = Var_ !DB
    | Lam  VarInfo Exp
    | App  Exp Exp
    | Con  ConIndex [Exp]
    | Case CaseInf Exp [Exp]
    | Lit  !Lit
    | Delta !Op [Exp]
    deriving (Show)

pattern Var i  = Var_ (Pos i)
pattern Free i = Var_ (Neg i)

type DB = Int
type ConIndex = (ConInfo, Int)
type CaseInf = (CaseInfo, [Int])

data Op
    = Round | ISqrt
    | Add | Sub | Mod | LessEq | EqInt
    | YOp | SeqOp
    deriving (Eq, Show)

pattern Op1 op x    = Delta op [x]
pattern Op2 op x y  = Delta op [x, y]

pattern Y s a       = Op1 YOp (Lam s a)
pattern Seq a b     = Op2 SeqOp a b
pattern Int i       = Lit (LInt i)

infixl 4 `App`

data EnvPiece
    = EApp !EExp
    | ECase CaseInf ![EExp]
    | EDelta !Op ![Lit] ![EExp]
    | Update_ !DB
    deriving (Eq, Show)

data HNF
    = HLam VarInfo !EExp
    | HCon ConIndex ![DB]
    | HLit !Lit
    | HVar_ !DB
    | HPiece !EnvPiece !HNF
    | HLet !Int ![EExp] !HNF
    deriving (Eq, Show)

zipWith' f (x: xs) (y: ys) = f x y !: zipWith' f xs ys
zipWith' _ _ _ = []
{-
f <$!> [] = []
f <$!> (a: as) = f a :! (f <$!> as)
-}
a !: as = a `seq` as `seq` (a: as)

[] ++! xs = xs
(x: xs) ++! ys = x !: (xs ++! ys)

pattern Update i = Update_ (Pos i)

pattern HVar i  = HVar_ (Pos i)
pattern HFree i = HVar_ (Neg i)

pattern Neg i <- (getNeg -> Just i)
  where Neg i =  negate i - 1

getNeg i | i < 0 = Just $ negate i - 1
getNeg _ = Nothing

pattern Pos :: Int -> Int
pattern Pos i <- (getPos -> Just i)
  where Pos i =  i

getPos i | i >= 0 = Just i
getPos _ = Nothing

data EExp
    = ExpC !Int ![EExp] !HNF
    | ErrExp
    deriving (Eq, Show)

pattern SExp :: HNF -> EExp
pattern SExp e <- ExpC 0 _ e
  where SExp = ExpC 0 []

pattern ERef r = SExp (HVar_ r)

pattern LExp n ls v = ExpC n ls (HVar_ v)

-------------------------------------- max db index

newtype MDB = MDB {getMDB :: Int}
    deriving (Eq, Show)

instance Monoid MDB where
    mempty = MDB 0
    MDB n `mappend` MDB m = MDB $ n `max` m

------------------------------------- rearrange De Bruijn indices

class Rearrange a where
    rearrange :: (Int -> Int) -> Int -> a -> a

instance Rearrange a => Rearrange [a] where
    rearrange f i xs = rearrange f i <$!> xs

instance Rearrange EExp
  where
    rearrange _ _ ErrExp = ErrExp
    rearrange f l_ (ExpC n ls e) = ExpC n (rearrange f l ls) $ rearrange f l e
      where
        l = l_ + n

instance Rearrange EnvPiece
  where
    rearrange f l = \case
        EApp e          -> EApp $ rearrange f l e
        ECase is@(_, i) es -> ECase is $ zipWith' (rearrange f . (l +)) i es
        EDelta o ls es  -> EDelta o ls $ rearrange f l es
        Update_ i       -> Update_ $ atL f l i

instance Rearrange HNF
  where
    rearrange f l = \case
        HLam i e    -> HLam i $ rearrange f (l+1) e
        HCon i ns   -> HCon i $ atL f l <$!> ns
        HVar_ i     -> HVar_ $ atL f l i
        HPiece p e  -> HPiece (rearrange f l p) $ rearrange f l e
        x@HLit{}    -> x

instance Rearrange Exp
  where
    rearrange f l = \case
        Var_ i      -> Var_ $ atL f l i
        Lam i e     -> Lam i $ rearrange f (l+1) e
        App e e'    -> App (rearrange f l e) (rearrange f l e')
        Con i es    -> Con i $ rearrange f l es
        Case is@(_, i) e es -> Case is (rearrange f l e) $ zipWith (rearrange f . (l +)) i es
        Delta d es  -> Delta d $ rearrange f l es
        x           -> x

----------

rearrange' f = rearrange f 0

up _ 0 = id
up l n = rearrange (+n) l

up' = up 0

-----------------------------------------

(<&>) = flip (<$>)

addI f l i | i < l = return 
addI f l i = f (i-l)

atL f l i | i < l = i
atL f l i = aadd l $ f (i-l)

aadd l (Pos i) = l + i
aadd l i = i

class FVs a where
    fv :: Monad m => (Int -> b -> m b) -> Int -> a -> b -> m b
    sfv :: (Int -> Int) -> Int -> a -> a
    open :: Int -> Int -> a -> a

instance FVs a => FVs [a] where
    fv l f [] = return
    fv l f (x: xs) = fv l f x >=> fv l f xs

    sfv l f xs = sfv l f <$!> xs

    open l f xs = open l f <$!> xs

instance (FVs a, FVs b) => FVs (a, b) where
    fv l f (a, b) = fv l f a >=> fv l f b

    sfv f l (a, b) = (sfv f l a, sfv f l b)

    open f i (a, b) = (open f i a, open f i b)

instance FVs EExp where
    fv f l ErrExp = return
    fv f l (ExpC n ls e) = fv f l' ls >=> fv f l' e
      where l' = l + n

    sfv f l ErrExp = ErrExp
    sfv f l (ExpC n ls e) = ExpC n (sfv f l' ls) (sfv f l' e)
      where l' = l + n

    open f l ErrExp = ErrExp
    open f l (ExpC n ls e) = ExpC n (open f l' ls) (open f l' e)
      where l' = l + n

instance FVs EnvPiece where

    fv f l = \case
        EApp e          -> fv f l e
        ECase (_, i) es -> foldr (>=>) return $ zipWith (fv f . (l +)) i es
        EDelta o ls es  -> fv f l es
        Update_ i       -> addI f l i

    sfv f l = \case
        EApp e          -> EApp $ sfv f l e
        ECase is@(_, i) es -> ECase is $ zipWith' (sfv f . (l +)) i es
        EDelta o ls es  -> EDelta o ls $ sfv f l es
        Update_ i       -> Update_ $ atL f l i

    open f l = \case
        EApp e          -> EApp $ open f l e
        ECase is@(_, i) es -> ECase is $ zipWith' (open f . (l +)) i es
        EDelta o ls es  -> EDelta o ls $ open f l es
        Update_ i       -> Update_ $ openL f l i

instance FVs HNF where

    fv f l = \case
        HLam i e    -> fv f (l+1) e
        HCon i ns   -> foldr (>=>) return $ addI f l <$!> ns
        HVar_ i     -> addI f l i
        HPiece p e  -> fv f l p >=> fv f l e
        HLit{}      -> return

    sfv f l = \case
        HLam i e    -> HLam i $ sfv f (l+1) e
        HCon i ns   -> HCon i $ atL f l <$!> ns
        HVar_ i     -> HVar_ $ atL f l i
        HPiece p e  -> HPiece (sfv f l p) $ sfv f l e
        x@HLit{}    -> x

    open f l = \case
        HLam i e    -> HLam i $ open f (l+1) e
        HCon i ns   -> HCon i $ openL f l <$!> ns
        HVar_ i     -> HVar_ $ openL f l i
        HPiece p e  -> HPiece (open f l p) $ open f l e
        x@HLit{}    -> x

openL f l (Neg i) | i >= f = i - f + l
openL f l i = i

-----------------------------------------

type GCConfig = (Int, Int, Int, Int)

defaultConfig = (20000, 10000, max 0 $ 10000 - 20, 20)

hnf = hnf_ defaultConfig

hnf_ gcconfig e_
     = open ii 0 $ steps gcconfig -- $ join (trace . ("\n------------\n" ++) . ppShow)
        $ preprocess e
  where
    (e, MDB ii) = runWriter $ closeExp ii 0 e_

    closeExp f l = \case
        Free i      -> tell (MDB $ i + 1) >> return (Free i)
        Var i       -> return $ if i >= l then Free $ i - l + f else Var i
        Lam i e     -> Lam i <$> closeExp f (l+1) e
        App e e'    -> App <$> closeExp f l e <*> closeExp f l e'
        Con i es    -> Con i <$> traverse (closeExp f l) es
        Case is@(_, i) e es -> Case is <$> closeExp f l e <*> zipWithM (\ns -> closeExp f (l + ns)) i es
        Delta d es  -> Delta d <$> traverse (closeExp f l) es
        x           -> return x

preprocess :: Exp -> EExp
preprocess = \case
    Lit l       -> SExp $ HLit l
    Var_ i      -> SExp $ HVar_ i
    Lam i e     -> SExp $ HLam i $ hnf e
    Y s e       -> ExpC (n+1) (ls ++ [({-s,-} SExp f)]) (HVar n)
      where ExpC n ls f = hnf e
    Delta d (e: es) -> add' (EDelta d [] $ preprocess <$!> es) $ preprocess e
    App e f         -> add' (EApp $ letify "u" $ preprocess f) $ preprocess e
    Case is@(_, i) e es -> add' (ECase is $ zipWith' (\ns -> if ns == 0 then preprocess else hnf) i es) $ preprocess e
    Con i es        -> foldl (app2 f) (SExp $ HCon i mempty) $ letify "r" . preprocess <$> es
      where
        f (HCon i vs) (HVar_ v) = HCon i $ vs ++ [v]
  where
    add' p (ExpC n ls e) = ExpC n ls $ HPiece (up' n p) e

    app2 g e@(ExpC n ls f) e'@(ExpC n' ls' f') = ExpC (n+n') (up n n' ls ++! up 0 n ls') f''
      where
        f'' = g (up n n' f) (up 0 n f')

    letify :: Info String -> EExp -> EExp
    letify s e@LExp{} = e
    letify s (ExpC n ls e) = LExp (n+1) (up n 1 $ ls <> [({-s,-} SExp e)]) n

-------------------------------------------------

nogc_mark = -1

type Vecs s = (Vec s EExp, Vec s EExp)

steps :: GCConfig -> EExp -> EExp
steps (gc1, gc2, gc3, gc4) e = runST (init e)
  where
    init :: forall s . EExp -> ST s EExp
    init (ExpC n ls e) = do
        v1 <- new n
        v2 <- new gc4
        v1' <- append v1 (n, ls)
        trace "-----" $ vsteps (n, 0, []) (v1', v2) [] e
      where
        vsteps :: (Int, Int, [Int]) -> Vecs s -> [EnvPiece] -> HNF -> ST s EExp

        vsteps sn ls ps (HPiece p e) = vsteps sn ls (p: ps) e

        vsteps sn ls@(v1@(len -> n), v2@(len -> n')) ps e@(HVar_ i)
            | i < 0 || i >= n + n' = final sn ls ps e
            | i < n = do
                (adjust (n + n') -> e) <- read_ v1 i
                if isHNF e
                  then addLets sn ls ps e
                  else write v1 i ErrExp >>= \v1 -> addLets sn (v1, v2) (Update i: ps) e
            | i < n + n' = do
                (adjust (n + n') -> e) <- read_ v2 (i-n)
                if isHNF e
                  then addLets sn ls ps e
                  else write v2 (i-n) ErrExp >>= \v2 -> addLets sn (v1, v2) (Update i: ps) e
        vsteps sn@(gc1, gc2, argh) ls@(v1@(len -> n), v2@(len -> n')) (p: ps) e
            | Update i <- p = if i < n
                then do
                    v1' <- write v1 i $ SExp e
                    vsteps (gc1, gc2, i: argh) (v1', v2) ps e
                else do
                    v2' <- write v2 (i - n) $ SExp e
                    vsteps sn (v1, v2') ps e
            | Just x <- dx (n + n') p e = addLets sn ls ps x
        vsteps sn ls ps e = final sn ls ps e

        final sn v ps e = majorGC sn v ps e $ \sn' (v1@(len -> n), _) ps' e' -> do
            ls' <- vToList v1
            return $ ExpC n ls' $ foldl (flip HPiece) e' ps'

        dx len (EApp (LExp n ls z)) (HLam i (ExpC n' ls' e))
            = Just $ ExpC (n + n') (rearrange' upFun ls ++! rearrange' fu ls') $ rearrange' fu e
              where
                z' = if z < 0 then z else if z < n then z + len else z - n
                fu i | i <  n'   = i + n + len
                     | i == n'   = z'
                     | otherwise = i - (1 + n')

                upFun i = if i < n then i + len else i - n

        dx len (ECase _ cs) (HCon (_, i) vs@(length -> n))
            | nn == 0 = Just e
            | otherwise = Just $ adjust' (\i -> if i < n' then i + len else if i < nn then vs !! (nn - 1 - i) else i - nn) e
          where
            !nn = n + n'
            !e@(ExpC n' _ _) = cs !! i
        dx len (EDelta SeqOp [] [f]) x
            | isHNF' x = Just $ adjust len f
            | otherwise = Nothing
        dx len (EDelta o lits (ExpC n ls f: fs)) (HLit l)
            = Just $ adjust len $ ExpC n ls $ HPiece (EDelta o (l: lits) fs) f
        dx len (EDelta o lits []) (HLit l)
            = Just $ SExp $ delta o $ l: lits
        dx _ _ _ = Nothing

        addLets sn ls ps (SExp e) = vsteps sn ls ps e
        addLets sn ls@(v1, v2) ps (ExpC n' xs e) = do
            v2' <- append v2 (n', xs)
            mkGC sn (v1, v2') ps e

        mkGC sn@(mg, sn_, xx) v@(len -> n, len -> n') ps e
            | n' < gc2          = vsteps (mg, sn_ + 1, xx) v ps e
            | n + n' - mg < gc1 = minorGC sn v ps e
            | otherwise         = majorGC sn v ps e vsteps

        adjust _ e@SExp{} = e
        adjust n e@(ExpC n' _ _) = adjust' (\i -> if i < n' then i + n else i - n') e

        adjust' fu (ExpC n' xs e) = ExpC n' (rearrange' fu xs) (rearrange' fu e)

        minorGC :: (Int, Int, [Int]) -> Vecs s -> [EnvPiece] -> HNF -> ST s EExp
        minorGC (mg, sn, argh) (v1@(len -> n), v2@(len -> n')) ps e = do
          fv2 <- freezedRead v2
          genericGC_ fv2 n n' $ \mark co -> do
            let cc (xx, acc) i = do
                    e <- read_ v1 i
                    (same, xx') <- fv (\i (same, b) -> (,) False <$> mark i b) n e (True, xx)
                    return (xx', if same then acc else i: acc)

            let !la = length argh
            (xx', argh') <- foldM cc (0, []) argh
            let !la' = length argh'
            s <- fv mark n (ps, e) xx'
            append v1 (s, []) >>= \vv -> co vv $ \fvi v1'@(len -> n'') ->
                trace ("minor gc: " ++ show (n - la) ++ " + " ++ show (la - la') ++ " + " ++ show la' ++ " + " ++ show xx' ++ " + " ++ show (n' - xx') ++ " - " ++ show (n + n' - n'')) $ do
                    v1'' <- foldM (\v i -> modify v i $ sfv fvi n) v1' argh'
                    v2' <- new gc3
                    vsteps (mg, sn + 1, []) (v1'', v2') (sfv fvi n ps) (sfv fvi n e)

        majorGC :: (Int, Int, [Int]) -> Vecs s -> [EnvPiece] -> HNF
                -> ((Int, Int, [Int]) -> Vecs s -> [EnvPiece] -> HNF -> ST s e)
                -> ST s e
        majorGC (_, sn, argh) v@(v1@(len -> n), v2@(len -> n')) ps e cont = do
          fv1 <- freezedRead v1
          fv2 <- freezedRead v2
          let read2 i = if i < n then fv1 i else fv2 (i - n)
          genericGC_ read2 0 (n + n') $ \mark co -> do
            s <- fv mark 0 (ps, e) 0
            new s >>= \v -> append v (s, []) >>= \vv -> co vv $ 
              \fvi v1'@(len -> n'') ->
                trace ("major gc: " ++ show n ++ " + " ++ show n' ++ " - " ++ show (n + n' - n'')) $ do
                    v2' <- new gc3
                    cont (n'', sn + 1, []) (v1', v2') (sfv fvi 0 ps) (sfv fvi 0 e)

        genericGC_ read_ n len cont = do
            vi <- UV.replicate len nogc_mark
            cont (mark vi read_ n []) $ \vv cont -> do
                (PUV.unsafeIndex -> fvi) <- PUV.unsafeFreeze vi
                let sweep i v | i == len = return v
                    sweep i v = do
                        let !ma = fvi i
                        if ma == nogc_mark then sweep (i+1) v else
                            case read_ i of
                              ERef r | r >= n -> sweep (i+1) v
                              e -> sweep (i+1) =<< write v (ma + n) (sfv fvi n e)
                cont fvi =<< sweep 0 vv
         where
            mark vi read_ n acc i t = do
                ma <- UV.unsafeRead vi i
                if ma /= nogc_mark then writes ma >> return t else
                    case read_ i of
                      ERef r | r >= n -> mark vi read_ n (i: acc) (r - n) t
                      e -> do
                        writes t
                        UV.unsafeWrite vi i t
                        fv (mark vi read_ n []) n e $ t+1
              where
                writes t = forM_ acc $ \i -> UV.unsafeWrite vi i t

delta ISqrt             [LInt i] = HLit $ LInt $ round $ sqrt $ fromIntegral i
delta LessEq    [LInt j, LInt i] = mkBool $ i <= j
delta EqInt     [LInt j, LInt i] = mkBool $ i == j
delta Add       [LInt j, LInt i] = HLit $ LInt $ i + j
delta Sub       [LInt j, LInt i] = HLit $ LInt $ i - j
delta Mod       [LInt j, LInt i] = HLit $ LInt $ i `mod` j
delta o ls = error $ "delta: " ++ show o ++ "\n" ++ show ls

mkBool b = HCon (if b then ("True", 1) else ("False", 0)) mempty

isHNF (SExp x) = isHNF' x
isHNF _ = False

isHNF' HVar_{} = False
isHNF' HPiece{} = False
isHNF' _ = True

--------------------------------------------------------------- pretty print

newtype Info a = Info {getInfo :: a}

instance Eq (Info a) where _ == _ = True
instance Show a => Show (Info a) where show (Info s) = show s
instance IsString a => IsString (Info a) where fromString = Info . fromString

type VarInfo = Info String
type ConInfo = String
type CaseInfo = [(String, [String])]

instance PShow Lit where
    pShow (LInt i)   = pShow i
    pShow (LChar i)  = pShow i
    pShow (LFloat i) = pShow i

instance Show Lit where show = ppShow

shLet [] x = x
shLet ls x = foldl (flip DFreshName) (DLet' (foldr1 DSemi $ zipWith (\i (_, e) -> DOp "=" (Infix (-1)) (dVar i) e) [0..] ls) x) (Just . getInfo . fst <$> ls)

shCase cn e xs = DPreOp (-20) (ComplexAtom "case" (-10) e (SimpleAtom "of"))
    $ foldr1 DSemi
    [ foldr DFreshName
        (DArr_ "->" (foldl DApp (text a) $ dVar <$> reverse [0..length n - 1])
                    b
        )
        $ Just <$> n
    | ((a, n), b) <- zip cn xs]

shLam n b = DFreshName (Just n) $ showLam (DVar 0) b

showLam x (DFreshName u d) = DFreshName u $ showLam (DUp 0 x) d
showLam x (DLam xs y) = DLam (DSep (InfixR 11) x xs) y
showLam x y = DLam x y

instance PShow HNF where
    pShow = \case
        HLam n e -> shLam (getInfo n) $ pShow e
        HCon (s, _) is -> foldl DApp (text s) $ dVar <$> is
        HLit l -> pShow l
        HVar_ i -> dVar i
        HPiece p e -> showPiece (pShow e) p

dVar (Pos i) = DVar i
dVar (Neg i) = text $ "v" ++ show i

instance PShow EExp where
    pShow ErrExp = text "_|_"
    pShow (ExpC _ ls e) = shLet ((,) "x" . pShow <$> ls) $ pShow e

showPiece e = \case
    EApp x -> e `DApp` pShow x
    ECase (cns, _) xs -> shCase cns e $ pShow <$> xs
    Update_ i -> DOp "@" (InfixR 14) (dVar i) e
    EDelta o ls es -> shDelta o $ (pShow <$> ls) ++ e: (pShow <$> es)
{-
instance PShow Exp where
    pShow = \case
        Var i -> DVar i
        Free i -> text $ "v" ++ show i
        Lam n e -> shLam (getInfo n) $ pShow e
        App a b -> pShow a `DApp` pShow b
        Con (s, _) is -> foldl DApp (text s) $ pShow <$> is
        Case (cns, _) e xs -> shCase cns (pShow e) $ pShow <$> xs
        Lit l -> pShow l
        Delta o es -> shDelta o $ pShow <$> es
-}
--shDelta ISqrt [x]    =
shDelta SeqOp [a, b] = DOp "`seq`" (Infix 1) a b
shDelta EqInt [x, y] = DOp "==" (Infix 4) x y
shDelta Add [x, y]   = DOp "+" (InfixL 6) x y
shDelta Sub [x, y]   = DOp "-" (InfixL 6) x y
shDelta Mod [x, y]   = DOp "`mod`" (InfixL 7) x y
shDelta o xs = foldl DApp (text $ show o) xs

---------------------------------------------------------------------------------------- examples

--pPrint = putStrLn . ppShow

pattern F = Con ("False", 0) []
pattern T = Con ("True", 1) []
pattern ENil = Con ("[]", 0) []
pattern ECons a b = Con ("ECons", 1) [a, b]

mkCase a b c = Case (a, map (length . snd) a) b c

caseBool x f t = mkCase [("False", []), ("True", [])] x [f, t]
caseList x n c = mkCase [("[]", []), ("ECons", ["c", "cs"])] x [n, c]

id_ = Lam "x" (Var 0)

if_ b t f = caseBool b f t

not_ x = if_ x F T

test = id_ `App` id_ `App` id_ `App` id_ `App` Int 13

test' = id_ `App` (id_ `App` Int 14)

foldr_ f e = Y "g" $ Lam "as" $ caseList (Var 0) (up' 2 e) (up' 4 f `App` Var 1 `App` (Var 3 `App` Var 0))

filter_ p = foldr_ (Lam "y" $ Lam "ys" $ if_ (up' 2 p `App` Var 1) (ECons (Var 1) (Var 0)) (Var 0)) ENil

and2 a b = if_ a b F

and_ = foldr_ (Lam "a" $ Lam "b" $ and2 (Var 1) (Var 0)) T

map_ f = foldr_ (Lam "z" $ Lam "zs" $ ECons (up' 2 f `App` Var 1) (Var 0)) ENil

neq a b = not_ $ Op2 EqInt a b

from_ = Y "from" $ Lam "n" $ ECons (Var 0) $ Var 1 `App` Op2 Add (Var 0) (Int 1)

undefined_ = Y "undefined" $ Var 0

idx = Y "idx" $ Lam "xs" $ Lam "n" $ caseList (Var 1) undefined_ $ if_ (Op2 EqInt (Var 2) $ Int 0) (Var 1) $ Var 4 `App` Var 0 `App` (Op2 Sub (Var 2) $ Int 1)

t = idx `App` (from_ `App` Int 3) `App` Int 5

takeWhile_ = Y "takeWhile" $ Lam "p" $ Lam "xs" $ caseList (Var 0) ENil $ if_ (Var 3 `App` Var 1) (ECons (Var 1) $ Var 4 `App` Var 3 `App` Var 0) ENil

sum_ = foldr_ (Lam "a" $ Lam "b" $ Op2 Add (Var 1) (Var 0)) (Int 0)

sum' = Y "sum" $ Lam "xs" $ caseList (Var 0) (Int 0) $ Op2 Add (Var 1) $ Var 3 `App` Var 0

infixl 4 `sApp`

sApp a b = Lam "s" (Seq (Var 0) (up' 1 a `App` Var 0)) `App` b

{-
accsum acc [] = acc
accsum acc (x: xs) = let z = acc + x `seq` accsum z xs
-}
accsum = Y "accsum" $ Lam "acc" $ Lam "xs" $ caseList (Var 0) (Var 1) $ Var 4 `sApp` Op2 Add (Var 3) (Var 1) `App` Var 0

fromTo = Y "fromTo" $ Lam "begin" $ Lam "end" $ ECons (Var 1) $ if_ (Op2 EqInt (Var 0) (Var 1)) ENil $ Var 2 `App` Op2 Add (Var 1) (Int 1) `App` Var 0

from = Y "from" $ Lam "begin" $ ECons (Var 0) $ Var 1 `App` Op2 Add (Var 0) (Int 1)

t' n = sum' `App` (fromTo `App` Int 0 `App` Int n)

t'' n = accsum `App` Int 0 `App` (fromTo `App` Int 0 `App` Int n)

t_opt n = Y "optsum" (Lam "i" $ if_ (Op2 EqInt (Int n) (Var 0)) (Var 0) (Op2 Add (Var 0) $ Var 1 `App` Op2 Add (Int 1) (Var 0))) `App` Int 0

t_seqopt n = Y "seqoptsum" (Lam "i" $ Lam "j" $ if_ (Op2 EqInt (Int n) (Var 0)) (Op2 Add (Int n) (Var 1)) (Var 2 `sApp` Op2 Add (Var 0) (Var 1) `sApp` Op2 Add (Int 1) (Var 0))) `App` Int 0 `App` Int 0

mod_ = Op2 Mod

isqrt = Op1 ISqrt

le = Op2 LessEq

primes = Y "primes"
    $ ECons (Int 2) $ ECons (Int 3)
    $ filter_ (Lam "n" $ and_ `App` (map_ (Lam "p" $ neq (Int 0) $ mod_ (Var 1) (Var 0)) `App` (takeWhile_ `App` (Lam "x" $ le (Var 0) $ isqrt $ Var 1) `App` Var 1))) `App` (from `App` Int 5)
-- primes = 2:3: filter (\n -> and $ map (\p -> n `mod` p /= 0) (takeWhile (\x -> x <= iSqrt n) primes)) (from 5)


nthPrime n = idx `App` primes `App` (Int $ n-1)


twice = Lam "f" $ Lam "x" $ Var 1 `App` (Var 1 `App` Var 0)
twice2 = Lam "f" $ Lam "x" $ Var 1 `sApp` (Var 1 `App` Var 0)

inc = Lam "n" $ Op2 Add (Int 1) (Var 0)

test'' = Lam "f" (Int 4) `App` Int 3

twiceTest n = (Lam "twice" $ (iterate (`App` Var 0) (Var 0) !! n) `App` inc `App` Int 0) `App` twice
twiceTest2 n = (Lam "twice" $ (iterate (`App` Var 0) (Var 0) !! n) `App` inc `App` Int 0) `App` twice2

tests =
    [ t test (Int 13)
    , t test' (Int 14)
    , t test'' (Int 4)
    , t (t' 10) (Int 55)
    , t (t'' 10) (Int 55)
    , t (nthPrime 6) (Int 13)
    ]
  where t = (,)

evalTests = case [(a, b) | (hnf -> a, hnf -> b) <- tests, a /= b] of
    [] -> True
    (a, b): _ -> error $ "tests:\n" ++ ppShow a ++ "\n------ /= -------\n" ++ ppShow b 


main | evalTests = do
    [s, read -> m, read -> m', read -> g3, n] <- getArgs
    putStrLn . (++"\n---------------") . ppShow $ 
        hnf_ (m, m', max 0 $ m' - g3, g3) $ prog s $ read n

prog = \case
    "prime" -> nthPrime
    "seq" -> t''
    "sum" -> t'
    "opt" -> t_opt
    "seqopt" -> t_seqopt
    "twice" -> twiceTest
    "twice2" -> twiceTest2

