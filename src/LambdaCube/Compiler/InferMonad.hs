{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}  -- TODO: remove
{-# OPTIONS_GHC -fno-warn-unused-binds #-}  -- TODO: remove
module LambdaCube.Compiler.InferMonad where

import Data.Monoid
import Data.List
import qualified Data.Set as Set
import qualified Data.Map as Map

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Arrow hiding ((<+>))
import Control.DeepSeq

--import LambdaCube.Compiler.Utils
import LambdaCube.Compiler.DeBruijn
import LambdaCube.Compiler.Pretty hiding (braces, parens)
import LambdaCube.Compiler.DesugaredSource hiding (getList)
import LambdaCube.Compiler.Parser (ParseWarning) -- TODO: remove
import LambdaCube.Compiler.Core

-------------------------------------------------------------------------------- error messages

data ErrorMsg
    = ErrorMsg Doc
    | ECantFind SName SI
    | ETypeError Doc SI
    | ERedefined SName SI SI

instance NFData ErrorMsg where rnf = rnf . ppShow
{-
    rnf = \case
        ErrorMsg m -> rnf m
        ECantFind a b -> rnf (a, b)
        ETypeError a b -> rnf (a, b)
        ERedefined a b c -> rnf (a, b, c)
-}
errorRange_ = \case
    ErrorMsg s -> []
    ECantFind s si -> [si]
    ETypeError msg si -> [si]
    ERedefined s si si' -> [si, si']

instance PShow ErrorMsg where
    pShow = \case
        ErrorMsg s -> s
        ECantFind s si -> "can't find:" <+> text s <+> "in" <+> pShow si
        ETypeError msg si -> "type error:" <+> msg <$$> "in" <+> pShow si
        ERedefined s si si' -> "already defined" <+> text s <+> "at" <+> pShow si <$$> "and at" <+> pShow si'


-------------------------------------------------------------------------------- infos

data Info
    = Info Range Doc
    | IType SIName Exp
    | ITrace String String
    | IError ErrorMsg
    | ParseWarning ParseWarning

instance NFData Info where rnf = rnf . ppShow
{-
 where
    rnf = \case
        Info r s -> rnf (r, s)
        IType a b -> rnf (a, b)
        ITrace i s -> rnf (i, s)
        IError x -> rnf x
        ParseWarning w -> rnf w
-}
instance PShow Info where
    pShow = \case
        Info r s -> nest 4 $ shortForm (pShow r) <$$> s
        IType a b -> shAnn (pShow a) (pShow b)
        ITrace i s -> text i <> ": " <+> text s
        IError e -> "!" <> pShow e
        ParseWarning w -> pShow w

errorRange is = [r | IError e <- is, RangeSI r <- errorRange_ e ]

type Infos = [Info]

throwError' e = tell [IError e] >> throwError e

mkInfoItem (RangeSI r) i = [Info r i]
mkInfoItem _ _ = mempty

listAllInfos m = h "trace"  (listTraceInfos m)
             ++  h "tooltips" [ nest 4 $ shortForm $ pShow r <$$> hsep (intersperse "|" is) | (r, is) <- listTypeInfos m ]
             ++  h "warnings" [ pShow w | ParseWarning w <- m ]
  where
    h x [] = []
    h x xs = ("------------" <+> x) : xs

listAllInfos' m = h "tooltips" [ nest 4 $ shortForm $ pShow r <$$> hsep (intersperse "|" is) | (r, is) <- listTypeInfos m ]
              ++  h "warnings" [ pShow w | ParseWarning w <- m ]
  where
    h x [] = []
    h x xs = ("------------" <+> x) : xs

listTraceInfos m = [DResetFreshNames $ pShow i | i <- m, case i of Info{} -> False; ParseWarning{} -> False; _ -> True]
listTypeInfos m = Map.toList $ Map.unionsWith (<>) [Map.singleton r [DResetFreshNames i] | Info r i <- m]

tellType si t = tell $ mkInfoItem (sourceInfo si) $ DTypeNamespace True $ pShow t

-------------------------------------------------------------------------------- global env

type GlobalEnv = Map.Map SName (Exp, Type, SI)

initEnv :: GlobalEnv
initEnv = Map.fromList
    [ (,) "'Type" (TType, TType, debugSI "source-of-Type")
    ]

-- inference monad
type IM m = ExceptT ErrorMsg (ReaderT (Extensions, GlobalEnv) (WriterT Infos m))

expAndType s (e, t, si) = (ET e t)

-- todo: do only if NoTypeNamespace extension is not on
lookupName s@(Ticked s') m = expAndType s <$> (Map.lookup s m `mplus` Map.lookup s' m)
lookupName s m             = expAndType s <$> Map.lookup s m

getDef te si s = do
    nv <- asks snd
    maybe (throwError' $ ECantFind s si) return (lookupName s nv)

addToEnv :: Monad m => SIName -> ExpType -> IM m GlobalEnv
addToEnv sn@(SIName si s) (ET x t) = do
--    maybe (pure ()) throwError_ $ ambiguityCheck s t      -- TODO
--    b <- asks $ (TraceTypeCheck `elem`) . fst
    tell [IType sn t]
    v <- asks $ Map.lookup s . snd
    case v of
      Nothing -> return $ Map.singleton s (x, t, si)
      Just (_, _, si') -> throwError' $ ERedefined s si si'


removeHiddenUnit (Pi Hidden (hnf -> Unit) (down 0 -> Just t)) = removeHiddenUnit t
removeHiddenUnit (Pi h a b) = Pi h a $ removeHiddenUnit b
removeHiddenUnit t = t

addParams ps t = foldr (uncurry Pi) t ps

addLams ps t = foldr (const Lam) t ps

lamify t x = addLams (fst $ getParams t) $ x $ downTo 0 $ arity t

arity :: Exp -> Int
arity = length . fst . getParams

downTo n m = map Var [n+m-1, n+m-2..n]

withEnv e = local $ second (<> e)

lamPi h t (ET x y) = ET (Lam x) (Pi h t y)

-- Ambiguous: (Int ~ F a) => Int
-- Not ambiguous: (Show a, a ~ F b) => b
ambiguityCheck :: String -> Exp -> Maybe String
ambiguityCheck s ty = case ambigVars ty of
    [] -> Nothing
    err -> Just $ s ++ " has ambiguous type:\n" ++ ppShow ty ++ "\nproblematic vars:\n" ++ ppShow err

ambigVars :: Exp -> [(Int, Exp)]
ambigVars ty = [(n, c) | (n, c) <- hid, not $ any (`Set.member` defined) $ Set.insert n $ free c]
  where
    (defined, hid, _i) = compDefined False ty

floatLetMeta :: Exp -> Bool
floatLetMeta ty = (i-1) `Set.member` defined
  where
    (defined, hid, i) = compDefined True ty

compDefined b ty = (defined, hid, i)
  where
    defined = dependentVars hid $ Set.map (if b then (+i) else id) $ free ty

    i = length hid_
    hid = zipWith (\k t -> (k, up (k+1) t)) (reverse [0..i-1]) hid_
    (hid_, ty') = hiddenVars ty

-- TODO: remove
free = Set.fromList . freeVars . getFreeVars

hiddenVars (Pi Hidden a b) = first (a:) $ hiddenVars b
hiddenVars t = ([], t)

-- compute dependent type vars in constraints
-- Example:  dependentVars [(a, b) ~ F b c, d ~ F e] [c] == [a,b,c]
dependentVars :: [(Int, Exp)] -> Set.Set Int -> Set.Set Int
dependentVars ie = cycle mempty
  where
    freeVars = free

    cycle acc s
        | Set.null s = acc
        | otherwise = cycle (acc <> s) (grow s Set.\\ acc)

    grow = flip foldMap ie $ \case
      (n, t) -> (Set.singleton n <-> freeVars t) <> case t of
        (hnf -> CW (hnf -> CstrT _{-todo-} ty f)) -> freeVars ty <-> freeVars f
        (hnf -> CSplit a b c) -> freeVars a <-> (freeVars b <> freeVars c)
        _ -> mempty
      where
        a --> b = \s -> if Set.null $ a `Set.intersection` s then mempty else b
        a <-> b = (a --> b) <> (b --> a)


