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
module LambdaCube.Compiler.Statements where

import Data.Maybe
import Data.List
import Data.Char
import Data.Function
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.IntMap as IM
import Control.Monad.Writer
import Control.Arrow hiding ((<+>))

import LambdaCube.Compiler.Utils
import LambdaCube.Compiler.DeBruijn
import LambdaCube.Compiler.Pretty hiding (braces, parens)
import LambdaCube.Compiler.DesugaredSource
import LambdaCube.Compiler.Patterns

-------------------------------------------------------------------------------- declaration representation

-- eliminated during parsing
data PreStmt
    = Stmt Stmt
    | TypeAnn SIName SExp
    | TypeFamily SIName SExp{-type-}   -- type family declaration
    | FunAlt SIName [(Visibility, SExp)]{-TODO: remove-} GuardTrees
    | Class SIName [SExp]{-parameters-} [(SIName, SExp)]{-method names and types-}
    | Instance SIName [ParPat]{-parameter patterns-} [SExp]{-constraints-} [Stmt]{-method definitions-}

instance PShow PreStmt where
    pShow _ = text "PreStmt - TODO"

instance DeBruijnify SIName PreStmt where
    deBruijnify_ k v = \case
        FunAlt n ts gue -> FunAlt n (map (second $ deBruijnify_ k v) ts) $ deBruijnify_ k v gue
        x -> error $ "deBruijnify @ " ++ ppShow x

mkLets :: [Stmt]{-where block-} -> SExp{-main expression-} -> SExp{-big let with lambdas; replaces global names with de bruijn indices-}
mkLets = mkLets_ SLet

mkLets_ :: DeBruijnify SIName a => (SIName -> SExp -> a -> a) -> [Stmt] -> a -> a
mkLets_ mkLet = mkLets' mkLet . concatMap desugarMutual . sortDefs

mkLets' :: DeBruijnify SIName a => (SIName -> SExp -> a -> a) -> [Stmt] -> a -> a
mkLets' mkLet = f where
    f [] e = e
    f (StmtLet n x: ds) e = mkLet n x (deBruijnify [n] $ f ds e)
    f (PrecDef{}: ds) e = f ds e
    f (x: ds) e = error $ "mkLets: " ++ ppShow x

type DefinedSet = Set.Set SName

addForalls :: DefinedSet -> SExp -> SExp
addForalls defined x = foldl f x [v | v@(sName -> vh:_) <- reverse $ names x, sName v `notElem'` defined, isLower vh]
  where
    f :: SExp -> SIName -> SExp
    f e v = SPi Hidden (Wildcard SType) $ deBruijnify [v] e

    notElem' :: SName -> Set.Set SName -> Bool
    notElem' s@(Ticked s') m = Set.notMember s m && Set.notMember s' m    -- TODO: review
    notElem' s m = s `notElem` m

    names :: SExp -> [SIName]
    names = nub . foldName pure

------------------------------------------------------------------------

compileStmt' :: MonadWriter [ParseCheck] m => [PreStmt] -> m [Stmt]
compileStmt' = compileStmt'_ SLHS SRHS SRHS

compileStmt'_ :: MonadWriter [ParseCheck] m => (SIName -> SExp -> SExp) -> (SExp -> SExp) -> (SExp -> SExp) -> [PreStmt] -> m [Stmt]
compileStmt'_ lhs ulend lend ds = fmap concat . sequence $ map (compileStmt lhs (\si vt -> compileGuardTree ulend lend (Just si) vt . mconcat) ds) $ groupBy h ds where
    h :: PreStmt -> PreStmt -> Bool
    h (FunAlt n _ _) (FunAlt m _ _) = m == n
    h _ _ = False

compileStmt :: MonadWriter [ParseCheck] m => (SIName -> SExp -> SExp) -> (SIName -> [(Visibility, SExp)] -> [GuardTrees] -> m SExp) -> [PreStmt] -> [PreStmt] -> m [Stmt]
compileStmt lhs compilegt ds = \case
    [Instance{}] -> return []
    [Class n ps ms] -> do
        cd <- compileStmt' $
            [ TypeAnn n $ foldr (SPi Visible) SConstraint ps ]
         ++ [ funAlt n (map noTA ps) $ noGuards $ foldr (SAppV2 $ SBuiltin F'T2) (SBuiltin FCUnit) cstrs | Instance n' ps cstrs _ <- ds, n == n' ]
         ++ [ funAlt n (replicate (length ps) (noTA $ PVarSimp $ dummyName "cst0")) $ noGuards $ SBuiltin FCEmpty `SAppV` sLit (LString $ "no instance of " ++ sName n ++ " on ???"{-TODO-})]
        cds <- sequence
            [ compileStmt'_ SLHS SRHS SRHS{-id-}
            $ TypeAnn m (UncurryS (map ((,) Hidden) ps) $ SPi Hidden (SCW $ foldl SAppV (SGlobal n) $ downToS "a2" 0 $ length ps) $ up1 t)
            : as
            | (m, t) <- ms
--            , let ts = fst $ getParamsS $ up1 t
            , let as = [ funAlt m p $ noGuards {- -$ SLam Hidden (Wildcard SType) $ up1 -} $ SLet m' e $ sVar "cst" 0
                       | Instance n' i cstrs alts <- ds, n' == n
                       , StLet m' ~Nothing e <- alts, m' == m
                       , let p = zip ((,) Hidden <$> ps) i ++ [((Hidden, Wildcard SType), PVarSimp $ dummyName "cst2")]
        --              , let ic = patVars i
                       ]
            ]
        return $ cd ++ concat cds
    [TypeAnn n t] -> return [Primitive n t | n `notElem` [n' | FunAlt n' _ _ <- ds]]
    tf@[TypeFamily n t] -> case [d | d@(FunAlt n' _ _) <- ds, n' == n] of
        [] -> return [Primitive n t]
        alts -> compileStmt lhs compileGuardTrees' [TypeAnn n t] alts
    fs@(FunAlt n vs _: _) -> case groupBy ((==) `on` fst) [(length vs, n) | FunAlt n vs _ <- fs] of
        [gs@((num, _): _)]
          | num == 0 && length gs > 1 -> fail $ "redefined " ++ sName n ++ ":\n" ++ show (vcat $ pShow . sourceInfo . snd <$> gs)
          | n `elem` [n' | TypeFamily n' _ <- ds] -> return []
          | otherwise -> do
            cf <- compilegt (SIName_ (mconcat [sourceInfo n | FunAlt n _ _ <- fs]) (nameFixity n) $ sName n) vs [gt | FunAlt _ _ gt <- fs]
            return [StLet n (listToMaybe [t | TypeAnn n' t <- ds, n' == n]{-TODO: fail if more-}) $ lhs n cf]
        fs -> fail $ "different number of arguments of " ++ sName n ++ ":\n" ++ show (vcat $ pShow . sourceInfo . snd . head <$> fs)
    [Stmt x] -> return [x]
  where
    noTA x = ((Visible, Wildcard SType), x)

funAlt :: SIName -> [((Visibility, SExp), ParPat)] -> GuardTrees -> PreStmt
funAlt n pats gt = FunAlt n (fst <$> pats) $ compilePatts (map snd pats) gt

funAlt' :: SIName -> [(Visibility, SExp)] -> [ParPat] -> GuardTrees -> PreStmt
funAlt' n ts x gt = FunAlt n ts $ compilePatts x gt

desugarValueDef :: MonadWriter [ParseCheck] m => ParPat -> SExp -> m [PreStmt]
desugarValueDef p e = sequence
    $ pure (FunAlt n [] $ noGuards e)
    : [ FunAlt x [] . noGuards <$> compileCase (SGlobal n) [(p, noGuards $ SVar x i)]
      | (i, x) <- zip [0..] dns
      ]
  where
    dns = reverse $ getPVars p :: [SIName]
    n = mangleNames dns :: SIName

getLet :: Stmt -> Maybe (SIName, SExp)
getLet (StmtLet x dx) = Just (x, dx)
getLet _ = Nothing

fst' (x, _) = x -- TODO

desugarMutual :: {-MonadWriter [ParseCheck] m => -} [Stmt] -> [Stmt]
desugarMutual [x@Primitive{}] = [x]
desugarMutual [x@Data{}] = [x]
desugarMutual [x@PrecDef{}] = [x]
desugarMutual [StLet n nt nd] = [StLet n nt $ addFix n nd]
--desugarMutual [StmtLet n nd] = [StmtLet n $ addFix n nd]      -- TODO
desugarMutual (traverse getLet -> Just (unzip -> (ns, ds))) = fst' $ runWriter $ do
    ss <- compileStmt'_ sLHS SRHS SRHS =<< desugarValueDef (foldr cHCons cHNil $ PVarSimp <$> ns) (SGlobal xy)
    return $ StmtLet xy (addFix xy $ mkLets' SLet ss $ foldr HCons HNil ds) : ss

  where
    xy = mangleNames ns
desugarMutual xs = error "desugarMutual"

addFix :: SIName -> SExp -> SExp
addFix n x
    | usedS n x = SBuiltin FprimFix `SAppV` SLamV (deBruijnify [n] x)
    | otherwise = x

mangleNames :: [SIName] -> SIName
mangleNames xs = SIName (foldMap sourceInfo xs) $ "_" ++ intercalate "_" (sName <$> xs)

-------------------------------------------------------------------------------- statement with dependencies

data StmtNode = StmtNode
    { snId          :: !Int
    , snValue       :: Stmt
    , snChildren    :: [StmtNode]
    , snRevChildren :: [StmtNode]
    }

sortDefs :: [Stmt] -> [[Stmt]]
sortDefs xs = map snValue <$> scc snId snChildren snRevChildren nodes
  where
    nodes :: [StmtNode]
    nodes = zipWith mkNode [0..] xs
      where
        mkNode :: Int -> Stmt -> StmtNode
        mkNode i s = StmtNode i s (nubBy ((==) `on` snId) $ catMaybes $ (`Map.lookup` defMap) <$> need)
                                  (fromMaybe [] $ IM.lookup i revMap)
          where
            need :: [SIName]
            need = Set.toList $ case s of
                PrecDef{} -> mempty
                StLet _ mt e -> foldMap names mt <> names e
                Data _ ps t cs -> foldMap (names . snd) ps <> names t <> foldMap (names . snd) cs

            names :: SExp -> Set.Set SIName
            names = foldName Set.singleton

    revMap :: IM.IntMap [StmtNode]
    revMap = IM.unionsWith (++) [IM.singleton (snId c) [n] | n <- nodes, c <- snChildren n]

    defMap :: Map.Map SIName StmtNode
    defMap = Map.fromList [(s, n) | n <- nodes, s <- def $ snValue n]
      where
        def :: Stmt -> [SIName]
        def = \case
            PrecDef{} -> mempty
            StLet n _ _ -> [n]
            Data n _ _ cs -> n: map fst cs
