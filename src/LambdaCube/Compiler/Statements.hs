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
import Control.Monad.Writer
import Control.Arrow hiding ((<+>))
--import Debug.Trace

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

mkLets_ mkLet = mkLets' . sortDefs where
    mkLets' [] e = e
    mkLets' (Let n mt x: ds) e
        = mkLet n (maybe id (flip SAnn) mt x') (deBruijnify [n] $ mkLets' ds e)
      where
        x' = if usedS n x then SBuiltin "primFix" `SAppV` SLamV (deBruijnify [n] x) else x
    mkLets' (PrecDef{}: ds) e = mkLets' ds e
    mkLets' (x: ds) e = error $ "mkLets: " ++ ppShow x

type DefinedSet = Set.Set SName

addForalls :: DefinedSet -> SExp -> SExp
addForalls defined x = foldl f x [v | v@(sName -> vh:_) <- reverse $ names x, sName v `notElem'` defined, isLower vh]
  where
    f e v = SPi Hidden (Wildcard SType) $ deBruijnify [v] e

    notElem' s@(Ticked s') m = Set.notMember s m && Set.notMember s' m    -- TODO: review
    notElem' s m = s `notElem` m

    names :: SExp -> [SIName]
    names = nub . foldName pure

------------------------------------------------------------------------

compileStmt' ds = fmap concat . sequence $ map (compileStmt (compileGuardTrees SRHS . Just) ds) $ groupBy h ds where
    h (FunAlt n _ _) (FunAlt m _ _) = m == n
    h _ _ = False

compileStmt :: MonadWriter [ParseCheck] m => (SI -> [(Visibility, SExp)] -> [GuardTrees] -> m SExp) -> [PreStmt] -> [PreStmt] -> m [Stmt]
compileStmt compilegt ds = \case
    [Instance{}] -> return []
    [Class n ps ms] -> do
        cd <- compileStmt' $
            [ TypeAnn n $ foldr (SPi Visible) SType ps ]
         ++ [ funAlt n (map noTA ps) $ noGuards $ foldr (SAppV2 $ SBuiltin "'T2") (SBuiltin "'Unit") cstrs | Instance n' ps cstrs _ <- ds, n == n' ]
         ++ [ funAlt n (replicate (length ps) (noTA $ PVarSimp $ dummyName "cst0")) $ noGuards $ SBuiltin "'Empty" `SAppV` sLit (LString $ "no instance of " ++ sName n ++ " on ???")]
        cds <- sequence
            [ compileStmt'
            $ TypeAnn m (UncurryS (map ((,) Hidden) ps) $ SPi Hidden (foldl SAppV (SGlobal n) $ downToS "a2" 0 $ length ps) $ up1 t)
            : as
            | (m, t) <- ms
--            , let ts = fst $ getParamsS $ up1 t
            , let as = [ funAlt m p $ noGuards {- -$ SLam Hidden (Wildcard SType) $ up1 -} $ SLet m' e $ sVar "cst" 0
                      | Instance n' i cstrs alts <- ds, n' == n
                      , Let m' ~Nothing e <- alts, m' == m
                      , let p = zip ((,) Hidden <$> ps) i ++ [((Hidden, Wildcard SType), PVarSimp $ dummyName "cst2")]
        --              , let ic = patVars i
                      ]
            ]
        return $ cd ++ concat cds
    [TypeAnn n t] -> return [Primitive n t | n `notElem` [n' | FunAlt n' _ _ <- ds]]
    tf@[TypeFamily n t] -> case [d | d@(FunAlt n' _ _) <- ds, n' == n] of
        [] -> return [Primitive n t]
        alts -> compileStmt compileGuardTrees' [TypeAnn n t] alts
    fs@(FunAlt n vs _: _) -> case groupBy ((==) `on` fst) [(length vs, n) | FunAlt n vs _ <- fs] of
        [gs@((num, _): _)]
          | num == 0 && length gs > 1 -> fail $ "redefined " ++ sName n ++ ":\n" ++ show (vcat $ pShow . sourceInfo . snd <$> gs)
          | n `elem` [n' | TypeFamily n' _ <- ds] -> return []
          | otherwise -> do
            cf <- compilegt (mconcat [sourceInfo n | FunAlt n _ _ <- fs]) vs [gt | FunAlt _ _ gt <- fs]
            return [Let n (listToMaybe [t | TypeAnn n' t <- ds, n' == n]) cf]
        fs -> fail $ "different number of arguments of " ++ sName n ++ ":\n" ++ show (vcat $ pShow . sourceInfo . snd . head <$> fs)
    [Stmt x] -> return [x]
  where
    noTA x = ((Visible, Wildcard SType), x)

funAlt :: SIName -> [((Visibility, SExp), ParPat)] -> GuardTrees -> PreStmt
funAlt n pats gt = FunAlt n (fst <$> pats) $ compilePatts (map snd pats) gt

funAlt' n ts x gt = FunAlt n ts $ compilePatts x gt

