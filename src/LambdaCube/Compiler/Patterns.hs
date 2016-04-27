{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module LambdaCube.Compiler.Patterns where

import Data.Monoid
import Data.Maybe
import qualified Data.Set as Set
import Control.Monad.Writer
import Control.Arrow hiding ((<+>))

import LambdaCube.Compiler.Utils
import LambdaCube.Compiler.DeBruijn
import LambdaCube.Compiler.Pretty hiding (braces, parens)
import LambdaCube.Compiler.DesugaredSource

---------------------------------

data ParseCheck
    = TrackedCode Range
    | Reachable Range
    | Uncovered' SI [PatList]

type PatList = ([ParPat_ ()], [(ParPat_ (), SExp)])

type ConsInfo = Either ((SName{-case eliminator name-}, Int{-num of indices-}), [(SIName, Int)]{-constructors with arities-})
                       Int{-arity-}

-------------------------------------------------------------------------------- pattern representation

type Pat = Pat_ ConsInfo

data Pat_ c
    = PVar SIName -- Int
    | PCon_ SI (SIName, c) [ParPat_ c]
    | ViewPat_ SI SExp (ParPat_ c)
    | PatType_ SI (ParPat_ c) SExp
  deriving Show

type ParPat = ParPat_ ConsInfo

-- parallel patterns like  v@(f -> [])@(Just x)
data ParPat_ c = ParPat_ SI [Pat_ c]
  deriving Show

pattern ParPat ps <- ParPat_ _ ps
  where ParPat ps =  ParPat_ (foldMap sourceInfo ps) ps

instance PShow (Pat_ a) where
    pShowPrec _ = showDoc_ . patDoc
instance PShow (ParPat_ a) where
    pShowPrec _ = showDoc_ . parPatDoc


pattern PWildcard si = ParPat_ si []
pattern PCon n pp <- PCon_ _ n pp
  where PCon n pp =  PCon_ (sourceInfo (fst n) <> sourceInfo pp) n pp
pattern ViewPat e pp <- ViewPat_ _ e pp
  where ViewPat e pp =  ViewPat_ (sourceInfo e <> sourceInfo pp) e pp
pattern PatType pp e <- PatType_ _ pp e
  where PatType pp e =  PatType_ (sourceInfo e <> sourceInfo pp) pp e
--pattern SimpPats ps <- (traverse simpleParPat -> Just ps)
--  where SimpPats ps =  ParPat . (:[]) <$> ps

--simpleParPat (ParPat [p]) = Just p
--simpleParPat _ = Nothing

pattern PVarSimp    n    = ParPat [PVar    n]
pattern PConSimp    n ps = ParPat [PCon    n ps]
--pattern PConSimp    n ps = PCon    n (SimpPats ps)
pattern ViewPatSimp e p  = ParPat [ViewPat e p]
pattern PatTypeSimp p t  = ParPat [PatType p t]

pBuiltin n ci ps =  PConSimp (f n, left (second $ map $ first f) ci) ps
  where
    f n = SIName (debugSI $ "pattern_" ++ n) n

cTrue = pBuiltin "True" (Left ((CaseName "'Bool", 0), [("False", 0), ("True", 0)])) []
cZero = pBuiltin "Zero" (Left ((CaseName "'Nat", 0), [("Zero", 0), ("Succ", 1)])) []
cNil  = pBuiltin "Nil"  (Left ((CaseName "'List", 0), [("Nil", 0), ("Cons", 2)])) []
cHNil = pBuiltin "HNil" (Left (("hlistNilCase", -1), [("HNil", 0)])) []
cList  a = pBuiltin "'List" (Right 1) [a]
cHList a = pBuiltin "'HList" (Right 1) [a]
cSucc  a = pBuiltin "Succ" (Left ((CaseName "'Nat", 0), [("Zero", 0), ("Succ", 1)])) [a]
cCons  a b = pBuiltin "Cons" (Left ((CaseName "'List", 0), [("Nil", 0), ("Cons", 2)])) [a, b]
cHCons a b = pBuiltin "HCons" (Left (("hlistConsCase", -1), [("HCons", 2)])) [a, b]

pattern PParens p = ViewPatSimp (SBuiltin "parens") p

mapP :: (Int -> SExp -> SExp) -> Int -> Pat -> Pat
mapP f i = \case
    PVar n -> PVar n
    PCon_ si n ps -> PCon_ si n (upPats (mapPP f) i ps)
    ViewPat_ si e p -> ViewPat_ si (f i e) (mapPP f i p)
    PatType_ si p t -> PatType_ si (mapPP f i p) (f i t)

mapPP f i = \case
    ParPat_ si ps -> ParPat_ si $ upPats (mapP f) i ps

upPats g k [] = []
upPats g k (p: ps) = g k p: upPats g (k + patVars p) ps

instance Rearrange Pat where
    rearrange k f = mapP (`rearrange` f) k

instance Rearrange ParPat where
    rearrange k f = mapPP (`rearrange` f) k

instance DeBruijnify SIName ParPat where
    deBruijnify_ l ns = mapPP (`deBruijnify_` ns) l

-- pattern variables
class PatVars a where getPVars :: a -> [SIName]

instance PatVars Pat
  where
    getPVars = \case
        PVar n -> [n]
        PCon _ ps -> foldMap getPVars ps
        ViewPat e p -> getPVars p
        PatType p t -> getPVars p

instance PatVars ParPat where getPVars (ParPat ps) = foldMap getPVars ps

instance PatVars a => PatVars [a] where getPVars = foldMap getPVars

-- number of pattern variables
patVars :: PatVars a => a -> Int
patVars = length . getPVars

instance SourceInfo (ParPat_ c) where
    sourceInfo (ParPat_ si _) = si

instance SetSourceInfo (ParPat_ c) where
    setSI si (ParPat_ _ ps) = ParPat_ si ps

instance SourceInfo (Pat_ c) where
    sourceInfo = \case
        PVar sn         -> sourceInfo sn
        PCon_ si _ _    -> si
        ViewPat_ si _ _ -> si
        PatType_ si _ _ -> si

instance SetSourceInfo (Pat_ c) where
    setSI si = \case
        PVar sn         -> PVar $ setSI si sn
        PCon_ _  a b    -> PCon_ si a b
        ViewPat_ _  a b -> ViewPat_ si a b
        PatType_ _  a b -> PatType_ si a b

-------------------------------------------------------------------------------- pretty print

patDoc :: Pat_ a -> NDoc
patDoc = \case
    PCon (n, _) _ -> shAtom $ sName n -- TODO

parPatDoc :: ParPat_ a -> NDoc
parPatDoc = \case
    ParPat [] -> shAtom "_"
    ParPat [p] -> patDoc p
    -- TODO
-------------------------------------------------------------------------------- pattern match compilation

-- pattern match compilation monad
type PMC = Writer ([CasePath], [Range])

type CasePath = [Maybe (SIName, Int, SExp)]

runPMC :: MonadWriter [ParseCheck] m => Maybe SI -> [(Visibility, SExp)] -> PMC a -> m a
runPMC si vt m = do
    tell $ Reachable <$> rs
    case si of
        Nothing -> return ()
        Just si -> tell [Uncovered' si [mkPatt_ (zip [0 :: Int ..] $ reverse p) $ reverse [0.. length vt - 1] | Just p <- sequence <$> ps]]
    return a
  where
    (a, (ps, rs)) = runWriter m
    mkPatt_ ps_ i_ = (ps, mkGuards 0 ps_)
      where
        (mconcat -> qs, ps) = unzip $ map (mkPatt 0 ps_) i_

        mkGuards k [] = []
        mkGuards k ((q, (cn, n, e)): ps) = [(PConSimp (cn, ()) $ replicate n $ PWildcard mempty, e) | q `Set.notMember` qs] ++ mkGuards (k + n) ps

        mkPatt k ((q, (cn, n, SVar _ j)): ps) i | j == (i + k) = (Set.singleton q <>) . mconcat *** PConSimp (cn, ()) $ unzip [mkPatt (k + n) ps l | l <- [n-1, n-2..0]]
        mkPatt k ((q, (cn, n, _)): ps) i = mkPatt (k + n) ps i
        mkPatt k [] i = (mempty, PWildcard mempty)
--        mkPatt k ps' i = error $ "mkPatt " ++ show i_ ++ ":  " ++ maybe "" showSI si ++ "\n" ++ show ps' ++ "\n" ++ show ps_

data Lets a
    = LLet SIName SExp (Lets a)
    | LTypeAnn SExp (Lets a)        -- TODO: eliminate if not used
    | In a
  deriving Show

lLet sn (SVar sn' i) l = rSubst 0 i l
lLet sn e l = LLet sn e l

foldLets f = \case
    In e -> f e
    LLet sn e x -> foldLets f x
    LTypeAnn e x -> foldLets f x

mapLets f h l = \case
    In e -> In $ h l e
    LLet sn e x -> LLet sn (f l e) $ mapLets f h (l+1) x
    LTypeAnn e x -> LTypeAnn (f l e) $ mapLets f h l x

instance Rearrange a => Rearrange (Lets a) where
    rearrange l f = mapLets (`rearrange` f) (`rearrange` f) l

instance DeBruijnify SIName a => DeBruijnify SIName (Lets a) where
    deBruijnify_ l ns = mapLets (`deBruijnify_` ns) (`deBruijnify_` ns) l

data GuardTree
    = GuardNode SExp (SIName, ConsInfo) [SIName] GuardTrees GuardTrees
    | GTSuccess SExp
    | GTFailure
  deriving Show

instance DeBruijnify SIName GuardTree where
    deBruijnify_ l ns = mapGT (`deBruijnify_` ns) (`deBruijnify_` ns) l

type GuardTrees = Lets GuardTree

instance Monoid GuardTrees where
    mempty = In GTFailure
    LLet sn e x `mappend` y = LLet sn e $ x `mappend` rUp 1 0 y
    LTypeAnn t x `mappend` y = LTypeAnn t $ x `mappend` y
    In (GuardNode e n ps t ts) `mappend` y = In $ GuardNode e n ps t (ts `mappend` y)
    In GTFailure `mappend` y = y
    x@(In GTSuccess{}) `mappend` _ = x

noGuards = In . GTSuccess

mapGT :: (Int -> ParPat -> ParPat) -> (Int -> SExp -> SExp) -> Int -> GuardTree -> GuardTree
mapGT f h k = \case
    GuardNode e c pps gt el -> GuardNode (h k e) c pps (mapGTs f h (k + length pps) gt) (mapGTs f h k el)
    GTSuccess e -> GTSuccess $ h k e
    GTFailure -> GTFailure

mapGTs f h = mapLets h (mapGT f h)
{-
foldGT f = \case
    GuardNode e c pps gt el -> GuardNode (h k e) c pps (mapGTs f h (k + length pps) gt) (mapGTs f h k el)
    GTSuccess e -> f e
    GTFailure -> mempty
-}
instance Rearrange GuardTree where
    rearrange l f = mapGT (`rearrange` f) (`rearrange` f) l

pattern Otherwise = SBuiltin "otherwise"

guardNode :: Pat -> SExp -> GuardTrees -> GuardTrees
guardNode (PCon (sName -> "True", _) []) Otherwise gt = gt
guardNode (PCon (sName -> "False", _) []) Otherwise gt = In GTFailure
guardNode (PVar sn) e gt = lLet sn e gt
guardNode (ViewPat f p) e gt = guardNode' p (f `SAppV` e) gt
guardNode (PatType p t) e gt = guardNode' p (SAnn e t) gt
guardNode (PCon sn ps) e gt = In $ GuardNode e sn (replicate n $ dummyName "gn") (buildNode guardNode' n ps [n-1, n-2..0] gt) mempty
  where
    n = length ps

guardNode' (PParens p) e gt = guardNode' p e gt
guardNode' (ParPat_ si ps) e gt = case ps of
    []  -> gt
    [p] -> guardNode p e gt
    ps  -> lLet (SIName si "gtc") e $ buildNode guardNode 1 ps [0..] gt

buildNode guardNode n ps is gt
    = foldr f (rUp n (patVars ps) gt) $ zip3 ps is $ scanl (+) 0 $ map patVars ps
  where
    f (p, i, d) = guardNode (rUp n d p) (sVar "gn" $ i + d)

compilePatts :: [ParPat] -> GuardTrees -> GuardTrees
compilePatts ps = buildNode guardNode' n ps [n-1, n-2..0]
  where
    n = length ps

compileGuardTree :: MonadWriter [ParseCheck] m => (SExp -> SExp) -> (SExp -> SExp) -> Maybe SI -> [(Visibility, SExp)] -> GuardTrees -> m SExp
compileGuardTree ulend lend si vt = fmap (\e -> foldr (uncurry SLam) e vt) . runPMC si vt . guardTreeToCases []
  where
    guardTreeToCases :: CasePath -> GuardTrees -> PMC SExp
    guardTreeToCases path = \case
        LLet sn e g -> SLet sn e <$> guardTreeToCases (Nothing: path){-TODO-} g
        LTypeAnn t g -> SAnn <$> guardTreeToCases (Nothing: path){-TODO-} g <*> pure t
        In GTFailure -> do
            tell ([path], mempty)
            return $ ulend $ SBuiltin "undefined"
        In (GTSuccess e) -> do
            tell $ (,) mempty $ maybeToList $ getRange $ sourceInfo e
            --trace (ppShow $ sourceInfo e) $ 
            return $ lend e
        ts@(In (GuardNode f (s, cn) _ _ _)) -> case cn of
--            Nothing -> throwError sn
            Left ((casename, inum), cns) -> do
                cf <- sequence [ iterateN n SLamV <$> guardTreeToCases (Just (cn, n, f): path) (filterGuardTree (up n f) cn 0 n $ rUp n 0 ts)
                               | (cn, n) <- cns ]
                return $
                    foldl SAppV
                        (SGlobal (SIName mempty casename) `SAppV` iterateN (1 + inum) SLamV (Wildcard (Wildcard SType)))
                        cf
                    `SAppV` f
            Right n -> do
                g1 <- guardTreeToCases (Nothing: path){-TODO-} $ filterGuardTree (up n f) s 0 n $ rUp n 0 ts
                g2 <- guardTreeToCases (Nothing: path){-TODO-} (filterGuardTree' f s ts)
                return $ SGlobal (SIName mempty $ MatchName $ sName s)
                 `SAppV` SLamV (Wildcard SType)
                 `SAppV` iterateN n SLamV g1
                 `SAppV` f
                 `SAppV` g2

    filterGuardTree' :: SExp -> SIName{-constr.-} -> GuardTrees -> GuardTrees
    filterGuardTree' f s = \case
        LLet sn e gt -> LLet sn e $ filterGuardTree' (up 1 f) s gt
        LTypeAnn e gt -> LTypeAnn e $ filterGuardTree' f s gt
        In (GuardNode f' s' ps gs (filterGuardTree' f s -> el))
            | f /= f' || s /= fst s' -> In $ GuardNode f' s' ps (filterGuardTree' (up (length ps) f) s gs) el
            | otherwise -> el
        In x -> In x

    filterGuardTree :: SExp -> SIName{-constr.-} -> Int -> Int{-number of constr. params-} -> GuardTrees -> GuardTrees
    filterGuardTree f s k ns = \case
        LLet sn e gt -> LLet sn e $ filterGuardTree (up 1 f) s (k + 1) ns gt
        LTypeAnn e gt -> LTypeAnn e $ filterGuardTree f s k ns gt
        In (GuardNode f' s' ps gs (filterGuardTree f s k ns -> el))
            | f /= f'   -> In $ GuardNode f' s' ps (filterGuardTree (up su f) s (su + k) ns gs) el
            | s == fst s' -> filterGuardTree f s k ns $ foldr (rSubst 0) gs (replicate su $ k+ns-1) <> el
            | otherwise -> el
          where
            su = length ps
        In x -> In x

compileGuardTrees ulend si vt = compileGuardTree ulend SRHS si vt . mconcat

compileGuardTrees' si vt = fmap (foldr1 $ SAppV2 $ SBuiltin "parEval" `SAppV` Wildcard SType) . mapM (compileGuardTrees id Nothing vt . (:[]))

compileCase x cs
    = (`SAppV` x) <$> compileGuardTree id id (Just $ sourceInfo x) [(Visible, Wildcard SType)] (mconcat [compilePatts [p] e | (p, e) <- cs])

patLam :: MonadWriter [ParseCheck] m => (SExp -> SExp) -> (Visibility, SExp) -> ParPat -> SExp -> m SExp
patLam f vt p e = compileGuardTree f f (Just $ sourceInfo p) [vt] (compilePatts [p] $ noGuards e)

