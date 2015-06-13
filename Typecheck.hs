{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-} -- for ghc-7.10.1
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Typecheck where

import Data.Function
import Data.List
import Data.Maybe
import Data.Either
import Data.Monoid
import Data.Foldable (Foldable, foldMap, toList, foldrM)
import qualified Data.Traversable as T
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Applicative
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Identity
import Control.Arrow hiding ((<+>))
import Debug.Trace
import GHC.Exts (Constraint)

import Text.Parsec.Pos

import Pretty
import Type
import Parser

--------------------------------------------------------------------------------

trace'' _ x = x

pairsWith f xs = zipWith f xs $ drop 1 xs

unifyMaps_ :: (Ord a) => (a -> Doc) -> [Map a b] -> [WithExplanation [b]]
unifyMaps_ f ms = {-case filter (not . Map.null) ms of
    [] -> []
    [m] -> []
    ms -> -} map (f *** id) . filter (not . null . drop 1 . snd) . Map.toList . Map.unionsWith (++) . map ((:[]) <$>) $ ms

unifyMaps :: (Ord a, PShow a) => [Map a b] -> [WithExplanation [b]]
unifyMaps = unifyMaps_ pShow

groupByFst :: (Ord a, PShow a) => [(a, b)] -> [WithExplanation [b]]
groupByFst = unifyMaps . map (uncurry Map.singleton)

matches TVar{} _ = True
matches x ts = x `elem'` ts

elem' a b = b a

isRec TRecord{} = True
isRec t = isVar t

isVar TVar{} = True
isVar _ = False

nat234 (ENat i) = i `elem` [2..4]
nat234 _ = False

floatIntWordBool = \case
    TFloat -> True
    TInt -> True
    TWord -> True
    TBool -> True
    _ -> False

data InjType
    = ITMat | ITVec | ITVecScalar
    deriving (Show, Eq, Ord)

instance PShow InjType where
    pShowPrec p = text . show

injType :: TypeFunT -> Maybe (InjType, [Exp])
injType = \case
    TFMat a b -> Just (ITMat, [a, b])
    TFVec a b -> Just (ITVec, [a, b])
    TFVecScalar a b -> Just (ITVecScalar, [a, b])
    _ -> Nothing


{- TODO
  type family NoStencilRepr a :: *
    type instance NoStencilRepr ZZ = ZZ
    type instance NoStencilRepr (Stencil a :+: b) = NoStencilRepr b
    type instance NoStencilRepr (Color a :+: b) = Color a :+: NoStencilRepr b
    type instance NoStencilRepr (Depth a :+: b) = Depth a :+: NoStencilRepr b
-}

{- currently not used
  [injective] type family PrimitiveVertices (primitive :: PrimitiveType) a
    type instance PrimitiveVertices Point a             = a
    type instance PrimitiveVertices Line a              = (a,a)
    type instance PrimitiveVertices LineAdjacency a     = (a,a,a,a)
    type instance PrimitiveVertices Triangle a          = (a,a,a)
    type instance PrimitiveVertices TriangleAdjacency a = (a,a,a,a,a,a)
-}
{- currently not used
  - texturing -
  [semiinjective] type family TexDataRepr arity (t :: TextureSemantics *)
    type instance TexDataRepr Red  (v a) = a
    type instance TexDataRepr RG   (v a) = V2 a
    type instance TexDataRepr RGB  (v a) = V3 a
    type instance TexDataRepr RGBA (v a) = V4 a

  [injective if (= SigleTex)] type family TexArrRepr (a :: Nat) :: TextureArray
    --type instance TexArrRepr 1 = SingleTex
    --type instance TexArrRepr ((2 <= t) => t) = ArrayTex
    -- FIXME: implement properly
    type instance TexArrRepr 1 = SingleTex
    type instance TexArrRepr 2 = ArrayTex
    type instance TexArrRepr 3 = ArrayTex
    type instance TexArrRepr 4 = ArrayTex
    type instance TexArrRepr 5 = ArrayTex
    type instance TexArrRepr 6 = ArrayTex
    type instance TexArrRepr 7 = ArrayTex
    type instance TexArrRepr 8 = ArrayTex
    type instance TexArrRepr 9 = ArrayTex

  [semiinjective] type family TexSizeRepr (a :: TextureShape)
    type instance TexSizeRepr (Tex1D)   = Word32
    type instance TexSizeRepr (Tex2D)   = V2U
    type instance TexSizeRepr (TexRect) = V2U
    type instance TexSizeRepr (Tex3D)   = V3U

  [injective in 4th param, semiinjective in 3rd param] type family TexelRepr sampler
    type instance TexelRepr (Sampler dim arr (v t) Red)     = t
    type instance TexelRepr (Sampler dim arr (v t) RG)      = V2 t
    type instance TexelRepr (Sampler dim arr (v t) RGB)     = V3 t
    type instance TexelRepr (Sampler dim arr (v t) RGBA)    = V4 t
-}


-------------------------------------------------------------------------------- constraints reduction

type ConstraintSolvRes = (TEnv, [WithExplanation [Exp]])

reduceConstraint :: IdN -> Exp -> TCM ConstraintSolvRes
reduceConstraint a b = reduceConstraint_ a b b

reduceConstraint_ :: forall m . (m ~ TCM) => IdN -> Exp -> Exp -> m ConstraintSolvRes
reduceConstraint_ cvar orig x = do
  builtinInstances <- asks instanceDefs
  pe <- asks getPolyEnv
  case x of
    -- hack for swizzling; TODO: define Vec as a structural record instead
    Split (TVec n a) c@TVar{} (TSingRecord s a') -> case n of
        4 | s `elem` (map ExpN ["x","y","z","w"]) -> discard' [WithExplanation "vec-split" [a, a'], WithExplanation "vec-split'" [c, TVec 3 a]]
        3 | s `elem` (map ExpN ["x","y","z"]) -> discard' [WithExplanation "vec-split" [a, a'], WithExplanation "vec-split'" [c, TVec 2 a]]
        2 | s `elem` (map ExpN ["x","y"]) -> discard' [WithExplanation "vec-split" [a, a'], WithExplanation "vec-split'" [c, TVec 1 a]]
        _ -> fail "bad swizzling"
    Split (TRecord a) (TRecord b) (TRecord c) ->
      case (Map.keys $ Map.intersection b c, Map.keys $ a Map.\\ (b <> c), Map.keys $ (b <> c) Map.\\ a) of
        ([], [], []) -> discard' $ unifyMaps [a, b, c]
--        ks -> failure $ "extra keys:" <+> pShow ks
    Split (TRecord a) (TRecord b) c@TVar{} -> diff a b c
    Split (TRecord a) c@TVar{} (TRecord b) -> diff a b c
    Split c@TVar{} (TRecord a) (TRecord b) -> case Map.keys $ Map.intersection a b of
        [] -> discard' [WithExplanation "???" [c, TRecord $ a <> b]]
--        ks -> failure $ "extra keys:" <+> pShow ks
    Split a b c
        | isRec a && isRec b && isRec c -> nothing
--        | otherwise -> failure $ "bad split:" <+> pShow x

    ctr@(getApp -> Just (c, ts))
      | all isVar ts -> nothing
      | otherwise -> case c of

        IsTypeLevelNatural -> case ts of
            [TNat{}] -> discard' []
            _ -> noInstance

        IsValidOutput -> discard' [] -- TODO

        IsValidFrameBuffer -> case ts of
            [TTuple ts]
                | any isVar ts -> nothing
                | sum [1 | Depth{} <- ts] <= 1 && sum [1 | Stencil{} <- ts] <= 1 -> discard' []
                | otherwise -> noInstance
            [_] -> discard' []
--            _ -> noInstance     -- impossible?

        IsAttributeTuple -> case ts of
            [TTuple ts]
                | any isVar ts -> nothing
                | length [() | a <- ts, Set.member a validAttributes] == length ts -> discard' []
                | otherwise -> noInstance
            [_] -> discard' []
          where
            validAttributes = Set.fromList $ [ TMat 2 2 TFloat, TMat 2 3 TFloat, TMat 2 4 TFloat
                                             , TMat 3 2 TFloat, TMat 3 3 TFloat, TMat 3 4 TFloat
                                             , TMat 4 2 TFloat, TMat 4 3 TFloat, TMat 4 4 TFloat
                                             , TFloat, TInt, TWord, TBool
                                             ] ++ concat [[TVec 2 a, TVec 3 a, TVec 4 a] | a <- [TFloat, TInt, TWord, TBool]]

        _ -> findInstance (const nothing) cvar ctr
      where
        findInstance failure cvar ctr@(getApp -> Just (c, ts))
            | all isVar ts = nothing
            | otherwise = maybe nothing (findWitness failure cvar ctr) $ Map.lookup c builtinInstances
        findInstance _ _ ctr = error $ "findInstance: " ++ ppShow ctr

        findWitness failure' cvar tt m = do
          let is :: [(Name, Exp)]
              is = [(n, tyOfItem e) | n@(flip Map.lookup pe -> Just e) <- Map.keys m]

          res <- trace'' (ppShow is) $ forM is $ \(n, t') -> catchExc $ do
                (se_, (fn, t_)) <- runWriterT' $ do
                    (fn, t'') <- toTCMS t'
                    trace'' ("checking " ++ ppShow (t', (fn, t''), tt)) $ 
                     addUnifOneDir t'' tt
                    trace'' "ok" $ return (fn, t'')
                css <- forM (zip fn $ subst (toSubst se_) fn) $ \case
                    (TVar _ cc, TVar ctr _)  -> do
                        (cs, []) <- findInstance failure cc ctr
                        return cs
                    _ -> return mempty
                se <- joinSE $ se_: css
                let x = subst (toSubst se) $ buildApp (`TVar` n) t_ fn
                trace'' ("eer: " ++ ppShow (se, cvar, x)) $ return ((n, t'), (singSubst cvar x <> se, []))
          case [x | Just x <- res] of
            [x] -> return $ snd x
            [] -> failure' $ msg' </> "possible instances:" </> pShow [x | (n, x) <- is]
            ws -> failure $ msg' </> "overlapping instances:" </> pShow (map fst ws)
          where
            msg' = "no instance for" <+> pShow tt
            noInstance = failure msg'

        msg' = "no" <+> pShow c <+> "instance for" <+> pShow ts
        noInstance = failure msg'

    CUnify a b -> discard' [WithExplanation "~~~" [a, b]]

    CEq res f -> case f of

        TFMat (TVec n TFloat) (TVec m TFloat) -> reduced $ TMat n m TFloat
        TFMat a b -> observe res $ \case
            TMat n m t -> keep [WithExplanation "Mat res 1" [a, TVec n t], WithExplanation "Mat res 2" [b, TVec m t]]
            _ -> fail "no instance"

        TFVec (ENat n) ty | n `elem` [2,3,4] {- && ty `elem'` floatIntWordBool -} -> reduced $ TVec n ty
        TFVec a b -> check (a `matches` nat234 && b `matches` floatIntWordBool {- -- FIXME -}) $ observe res $ \case
            TVec n t -> keep [WithExplanation "Vec res 1" [a, ENat n], WithExplanation "Vec res 2" [b, t]]
            _ -> fail "no instance tfvec"

        TFVecScalar a b -> case a of
            ENat 1 -> case b of
                TVar{} | res `matches` floatIntWordBool -> keep [WithExplanation "VecScalar dim 1" [b, res]]
                b -> check (b `elem'` floatIntWordBool) $ reduced b
            TVar{} -> check (b `matches` floatIntWordBool) $ observe res $ \case
                t | t `elem'` floatIntWordBool -> keep [WithExplanation "VecScalar res 1" [a, ENat 1], WithExplanation "VecScalar res 2" [b, t]]
                TVec n t -> keep [WithExplanation "VecScalar res 1" [a, ENat n], WithExplanation "VecScalar res 2" [b, t]]
                _ -> nothing --like $ TFVec a b
            _ -> like $ TFVec a b

        TFMatVecElem t -> observe t $ \case
            TVec _ t -> reduced t
            TMat _ _ t -> reduced t
            _ -> fail $ "no instance matvecelem" <+> pShow t

        TFMatVecScalarElem t -> observe t $ \case
            t | t `elem'` floatIntWordBool -> reduced t
            t -> like $ TFMatVecElem t

        TFColorRepr ty -> observe ty $ \case
            TTuple ts -> reduced . TTuple $ map Color ts
            ty -> reduced $ Color ty

        TFFTRepr' ty -> caseTuple "expected List/Interpolated/Depth/Color" ty (reduced . tTuple) $ \case
            TInterpolated a -> reduce' a
            Depth a         -> reduce' a
            Color a         -> reduce' a
            TList a         -> reduce' a
            _ -> fail'

        TFFragOps ty -> caseTuple "expected FragmentOperation" ty (reduced . tTuple) $ \case
            TFragmentOperation a -> reduce' a
            _ -> fail'

        TFFrameBuffer ty -> caseTuple "expected (Image Nat)" ty end $ \case
            TImage a b -> observe' a $ \case
                ENat n -> reduce' (n, b)
                _ -> fail'
            _ -> fail'
          where
            end (unzip -> (n: ns, tys))
                | all (==n) ns = reduced $ TFrameBuffer (ENat n) $ tTuple tys
                | otherwise = fail "frambuffer number of layers differ"

        TFJoinTupleType (TTuple []) x -> reduced x
        TFJoinTupleType x (TTuple []) -> reduced x
        TFJoinTupleType TVar{} _ -> nothing  -- TODO: observe res?
        TFJoinTupleType _ TVar{} -> nothing  -- TODO: observe res?
        TFJoinTupleType (TTuple l) (TTuple r) -> reduced $ TTuple (l ++ r)
        TFJoinTupleType l (TTuple r) -> reduced $ TTuple (l : r)
        TFJoinTupleType (TTuple l) r -> reduced $ TTuple (l ++ [r])
        TFJoinTupleType l r -> reduced $ TTuple [l,r]

        _ -> error $ "Unknown type function: " ++ ppShow f

      where
        like f = reduceConstraint_ cvar x (CEq res f)
        reduced t = discard' [WithExplanation "type family reduction" [res, t]]
        check b m = if b then m else fail "no instance (1)"
        fail :: Doc -> m ConstraintSolvRes
        fail = failure . (("error during reduction of" </> pShow res <+> "~" <+> pShow f) </>)

        reduce' = Just . Just
        nothing' = Just Nothing
        fail' = Nothing
        observe' TVar{} _ = nothing'
        observe' x f = f x

        caseTuple :: Doc -> Exp -> ([a] -> m ConstraintSolvRes) -> (Exp -> Maybe (Maybe a)) -> m ConstraintSolvRes
        caseTuple msg ty end f = observe ty $ \case
            TTuple ts -> maybe (fail $ msg <+> "inside tuple") (maybe nothing end . sequence) $ mapM f' ts
            _ -> maybe (fail msg) (maybe nothing (end . (:[]))) $ f' ty
          where f' x = observe' x f

        tTuple [x] = x
        tTuple xs = TTuple xs
    _ -> nothing

  where
    diff a b c = case Map.keys $ b Map.\\ a of
        [] -> discard' $ WithExplanation "???" [c, TRecord $ a Map.\\ b]: unifyMaps [a, b]
--        ks -> failure $ "extra keys:" <+> pShow ks
    discard w xs = return (singSubst cvar w, xs)
    discard' xs = discard (WRefl orig) xs
    keep xs = return (mempty, xs)
    failure :: Doc -> m ConstraintSolvRes
    failure = throwErrorTCM

    nothing = return mempty
    observe TVar{} _ = nothing
    observe x f = f x

--------------------------------------------------------------------------------

-- unify each types in the sublists
unifyTypes :: forall m . (MonadPlus m, MonadState FreshVars m, MonadError ErrorMsg m) => Bool -> [WithExplanation [Exp]] -> m TEnv
unifyTypes bidirectional tys = flip execStateT mempty $ forM_ tys $ sequence_ . pairsWith uni . snd
  where
--    uni :: Exp -> Exp -> StateT TEnv TCM ()
    uni a b = gets (subst1{-could be subst-} . toSubst) >>= \f -> unifyTy (f $ reduceHNF a) (f $ reduceHNF b)

    -- make single tvar substitution; check infinite types
    bindVar n t = do
        s <- get
        let t' = subst_ (toSubst s) t
        if n `Set.member` freeVars t'
            then throwErrorTCM $ "Infinite type, type variable" <+> pShow n <+> "occurs in" <+> pShow t'
            else put $ singSubst n t' <> s

    bindVars a@(TVar tu u) b@(TVar tv v) = case (compare u v, bidirectional) of
        (EQ, _) -> return ()
        (GT, True) -> bindVar v (TVar tu u)
        _ -> bindVar u (TVar tv v)

--    unifyTy :: Exp -> Exp -> StateT Subst m ()
    unifyTy (Exp t) (Exp t') = unifyTy' t t'
      where
--        unifyTy' (Forall_ Hidden n a1 b1) x = maybe (lift $ newName "?") return n >>= \n -> put (singSubstTy_ n a1) >> uni b1 (Exp x)
--        unifyTy' x (Forall_ Hidden n a1 b1) = maybe (lift $ newName "?") return n >>= \n -> put (singSubstTy_ n a1) >> uni b1 (Exp x)
        unifyTy' (Forall_ Visible (Just a) k t) (Forall_ Visible (Just a') k' t') = do
            uni k k'
            a'' <- lift $ newName "unifyTy"
            modify $ TEnv . Map.insert a'' (ISig False k) . getTEnv
            -- TODO! protect a in t
--            if ppShow a' == "t1755" then throwErrorTCM "!!!" else 
            uni (subst (Subst $ Map.singleton a $ TVar k a'') t) ({-trace (ppShow (a', a, k)) $ -} subst (Subst $ Map.singleton a' $ TVar k a'') t')
            --bindVars (TVar k a) (TVar k' a') >> uni t t'
        unifyTy' (Forall_ Visible Nothing a1 b1) (Forall_ Visible Nothing a2 b2) = uni a1 a2 >> uni b1 b2
        unifyTy' (EVar_ k u) (EVar_ k' v) = uni k k' >> bindVars (Exp t) (Exp t')
        unifyTy' (EVar_ k u) _ = bindVar u (Exp t')
        unifyTy' _ (EVar_ k v) | bidirectional = bindVar v (Exp t)
        unifyTy' (ELit_ l) (ELit_ l') | l == l' = return ()
        unifyTy' (TCon_ k u) (TCon_ k' v) | u == v = uni k k' >> return ()
        unifyTy' (TTuple_ t1) (TTuple_ t2) = sequence_ $ zipWith uni t1 t2
        unifyTy' (EApp_ k a1 b1) (EApp_ k' a2 b2) = uni k k' >> uni a1 a2 >> uni b1 b2
        unifyTy' Star_ Star_ = return ()
        unifyTy' (TRecord_ xs) (TRecord_ xs') | Map.keys xs == Map.keys xs' = sequence_ $ zipWith uni (Map.elems xs) (Map.elems xs')
        unifyTy' (CUnify_ a b) (CUnify_ a' b') = uni a a' >> uni b b'   -- ???
        unifyTy' (CEq_ a (TypeFun n b)) (CEq_ a' (TypeFun n' b')) | n == n' = uni a a' >> sequence_ (zipWith uni b b')   -- ???
        unifyTy' (Split_ a b c) (Split_ a' b' c') = uni a a' >> uni b b' >> uni c c'   -- ???
        unifyTy' (WRefl_ a) (WRefl_ b) = uni a b
        unifyTy' _ _
          | otherwise = throwError $ UnificationError (Exp t) (Exp t') $ filter (not . null . drop 1 . snd) tys

-- TODO: revise applications
appSES :: (Substitute Subst x, PShow x, Monad m) => TypingT m x -> TypingT m x
appSES = mapWriterT' $ fmap $ \(se, x) -> 
   let
    su = toSubst se
   in (subst su $ TEnv $ Map.filter (eitherItem (\r _ -> not r) (\_ _ -> True)) $ getTEnv se, subst su x)

removeMonoVars = mapWriterT' $ fmap $ \(en@(TEnv se), (s, x)) -> let
        su = toSubst en
    in (TEnv $ foldr Map.delete se $ {-map (subst' su) $ -} Set.toList s, subst su x)
{-
  where
    subst' (Subst m) n | Just (EVar i) <- Map.lookup n m = i
        | otherwise = n
-}
runWriterT'' = runWriterT' . appSES

closeSubst (TEnv m) = s where s = TEnv $ subst (toSubst s) <$> m

joinSubsts :: [TEnv] -> TCM TEnv
joinSubsts (map getTEnv -> ss) = case filter (not . Map.null) ss of
  [] -> return mempty
  [x] -> return $ TEnv x
  ss -> do
    s <- addCtx "joinSubsts" $ unifyTypes True $ concatMap ff $ unifyMaps ss
    if nullTEnv s
        then return $ closeSubst $ TEnv $ Map.unionsWith mergeSubsts ss
        else joinSubsts [s, TEnv $ Map.unionsWith mergeSubsts ss]
  where
    ff (expl, ss) = case ( WithExplanation (expl <+> "subst") [s | ISubst _ s <- ss]
                         , WithExplanation (expl <+> "typesig") [s | ISig rigid s <- ss]) of 
        (WithExplanation _ [], ss) -> [ss]
        (ss, WithExplanation _ []) -> [ss]
        (subs@(WithExplanation i (s:_)), sigs@(WithExplanation i' (s':_))) -> [subs, sigs, WithExplanation ("subskind" <+> i <+> i') [tyOf s, s']]

joinSE :: [TEnv] -> TCM TEnv
joinSE ts = case ts of
    [a, b]
        | Map.null $ getTEnv a -> return b     -- optimization
        | Map.null $ getTEnv b -> return a     -- optimization
    ab -> swapRule <$> (joinSubsts ab >>= untilNoUnif)

swapRule (TEnv te) = TEnv $ foldr f te vs
  where
    vs = [(v1, v2, t) | (v1, ISubst False (TVar t v2)) <- Map.toList te, v1 < v2]
    f (v1, v2, t) m = case Map.lookup v2 m of
        Just (ISubst True (TVar _ v))
            | v == v1 -> Map.delete v1 m
            | otherwise -> m
        Just (ISig False _) -> Map.insert v2 (ISubst True $ TVar t v1) $ Map.delete v1 m
        Nothing -> m

writerT' x = WriterT' $ do
    (me, t) <- x
    me <- untilNoUnif me
    return (me, t)

addUnif, addUnifOneDir :: Exp -> Exp -> TCMS ()
addUnif a b = addUnifs True [[a, b]]
addUnifOneDir a b = addUnifs True [[a, b]]

addUnifs :: Bool -> [[Exp]] -> TCMS ()
addUnifs twodir ts = writerT' $ do
    m <- addCtx "addUnifs" (unifyTypes twodir $ map (WithExplanation "~~~") ts)
    return (m, ())

untilNoUnif :: TEnv -> TCM TEnv
untilNoUnif es = do
    let cs = [(n, c) | (n, ISig False c) <- Map.toList $ getTEnv es]
    (unzip -> (ss, concat -> eqs)) <- mapM (uncurry reduceConstraint) cs
    s0 <- addCtx "untilNoUnif" $ unifyTypes True
        -- unify left hand sides where the right hand side is equal:  (t1 ~ F a, t2 ~ F a)  -->  t1 ~ t2
         $ groupByFst [(f, ty) | CEq ty f <- map snd cs]
        -- injectivity test:  (t ~ Vec a1 b1, t ~ Vec a2 b2)  -->  a1 ~ a2, b1 ~ b2
        ++ concatMap (\(s, l) -> map ((,) s) $ transpose l)
                (groupByFst
                [((ty, it), is) | CEq ty (injType -> Just (it, is)) <- map snd cs])
        ++ eqs

    -- (a :: Num X, b :: Num X) ----> a := TVar (Num X) b
    let ff ((n, _):xs) = [(n, TVar c x) | (x, c) <- xs] 
    let s1 = Subst $ Map.fromList $ concatMap (\(WithExplanation _ xs) -> ff xs) $ groupByFst [(x, (n, x)) | (n, x) <- cs, isConstraint x]
 --   trace ("---" ++ ppShow s1) $ 
    if nullTEnv s0 && nullSubst s1 && all nullTEnv ss then return es else do
        joinSubsts (s0: toTEnv s1: es: ss) >>= untilNoUnif

isConstraint (getApp -> Just _) = True
isConstraint _ = False

instance Monoid' TEnv where
    type MonoidConstraint TEnv = TCM
    mempty' = mempty
    mappend' a b = joinSE [a, b]

--------------------------------------------------------------------------------

singSubstTy a b = addConstraints $ singSubstTy_ a b
singSubstTy' a b = WriterT' $ pure (singSubstTy_ a b, ())

newStarVar' :: Doc -> Name -> TCMS Exp
newStarVar' i n = do
    t <- newStarVar $ i <+> pShow n
    singSubstTy' n t
    return t

newStarVar :: Doc -> TCMS Exp
newStarVar i = newVar i Star

newVar :: Doc -> Exp -> TCMS Exp
newVar i k = do
    n <- newName i
    singSubstTy' n k
    return $ TVar k n

addConstraints m = writerT' $ pure (m, ())
addConstraint c = newName "constraint" >>= \n -> singSubstTy n c

checkStarKind Star = return ()
checkStarKind t = addUnif Star $ tyOf t

----------------------------

instantiateTyping :: Doc -> TCMS Exp -> TCM Exp
instantiateTyping i ty = do
    (se, ty) <- runWriterT'' ty
    x <- instantiateTyping_' False i se ty
    return $ snd x


lookEnv :: Name -> TCMS ([Exp], Exp) -> TCMS ([Exp], Exp)
lookEnv n m = asks (Map.lookup n . getPolyEnv) >>= maybe m (toTCMS . tyOfItem)

lookEnv' n m = asks (Map.lookup n . typeFamilies) >>= maybe m toTCMS

--------------------------------------------------------------------------------

calcPrec
  :: (MonadError ErrorMsg m, PShow e)
     => (e -> e -> e -> e)
     -> (e -> Name)
     -> PrecMap
     -> e
     -> [(e, e)]
     -> m e
calcPrec app getname ps e es = do
    compileOps [((Nothing, -1), undefined, e)] es
  where
    compileOps [(_, _, e)] [] = return e
    compileOps acc [] = compileOps (shrink acc) []
    compileOps acc@((p, g, e1): ee) es_@((op, e'): es) = case compareFixity (pr, op) (p, g) of
        Right GT -> compileOps ((pr, op, e'): acc) es
        Right LT -> compileOps (shrink acc) es_
        Left err -> throwErrorTCM err
      where
        pr = fromMaybe --(error $ "no prec for " ++ ppShow n)
                       (Just FDLeft, 9)
                       $ Map.lookup (getname op) ps

    shrink ((_, op, e): (pr, op', e'): es) = (pr, op', app op e' e): es

    compareFixity ((dir, i), op) ((dir', i'), op')
        | i > i' = Right GT
        | i < i' = Right LT
        | otherwise = case (dir, dir') of
            (Just FDLeft, Just FDLeft) -> Right LT
            (Just FDRight, Just FDRight) -> Right GT
            _ -> Left $ "fixity error:" <+> pShow (op, op')

--------------------------------------------------------------------------------

appTy (TArr ta v) ta' = addUnif ta ta' >> return v      -- optimalization
appTy tf ta = newStarVar ("tapp" <+> pShow tf <+> "|" <+> pShow ta) >>= \v -> addUnif tf (ta ~> v) >> return v

forallApp (Forall x k y) t = do
    addUnif (tyOf t) k
    return $ subst (Subst $ Map.singleton x t) y
forallApp tt t = do -- ???
    throwErrorTCM $ "can't unify" <+> pShow tt <+> "with" <+> "forall"
{-
    x' <- newName "forallApp"
    y <- newStarVar "etyapp"
    addUnif tt (Forall x' (tyOf t) y)
    return y -- $ subst (Subst $ Map.singleton x $ TVar k x') y
-}


getRes 0 x = Just ([], x)
getRes i (TArr a b) = ((a:) *** id) <$> getRes (i-1) b
getRes _ _ = Nothing

starV (TVar t n) = monoInstType n t

inferPatTyping :: Bool -> PatR -> TCMS (Pat, InstEnv)
inferPatTyping polymorph p_@(PatR pt p) = addRange pt $ addCtx ("type inference of pattern" <+> pShow p_) $ case p of

  PPrec_ e es -> do
        ps <- asks precedences
        inferPatTyping polymorph =<< calcPrec (\a b c -> appP' a [b, c]) (\(PCon' _ n []) -> n) ps e es

  PVar_ _{-TODO-} n -> do
        t <- newStarVar $ "pvar" <> pShow pt
        return (PVar t n, monoInstType n t)
  _ -> do
    p <- traverse (inferPatTyping polymorph) p
    (res, tr) <- case p of
      PCon_ _{-TODO-} n ps -> do
            (fn, tn) <- lookEnv n $ lift $ throwErrorTCM $ "Constructor" <+> pShow n <+> "is not in scope."
            v <- case getRes (length ps) tn of
                Just (ts, x) -> do
                    addUnifs True $ zipWith (\a b -> [a, b]) ts $ map (tyOfPat . fst) ps
                    return x
                _ -> do
                    v <- newStarVar "pcon"
                    addUnif tn $ map (tyOfPat . fst) ps ~~> v
                    return v
            return (PCon v n $ [Pat $ PVar_ t n | TVar t n <- fn] ++ (fst <$> ps), mempty)

      _ -> do
       (t, tr) <- case tyOfPat . fst <$> p of
        Wildcard_ _{-TODO-} -> noTr $ newStarVar "_" >>= pure

        PAt_ n p -> return (error "impossible patty", monoInstType n p)

        PTuple_ ps -> {-mapM_ checkStarKind (map tyOf ps) >> -}return (error "impossible patty", mempty)

        PRecord_ (unzip -> (fs, ps)) -> noTr $ do
            v <- newStarVar "pfp2"
            v' <- newStarVar "pfp3"
            addConstraint $ Split v v' $ TRecord $ Map.fromList $ zip fs ps
            return v

        _ -> return (error "impossible patty", mempty)
       return (Pat $ mapPat (const t) id id $ fst <$> p, tr)

    let trs = Map.unionsWith (++) . map ((:[]) <$>) $ tr: map snd (toList p)
    tr <- case filter (not . null . drop 1 . snd) $ Map.toList trs of
        [] -> return $ Map.map head trs
        ns -> lift $ throwErrorTCM $ "conflicting definitions for" <+> pShow (map fst ns)
    return (res, tr)
  where
    noTr = addTr $ const mempty
    addTr tr m = (\x -> (x, tr x)) <$> m

eLam' (n, t) e = Exp $ ELam_ (Just $ Exp $ Forall_ Hidden (Just n) t $ tyOf e) (PVar t n) e

inferType = inferType_ True True
inferTyping = inferType_ True False

info (Range i j) x = tell [(i, j, ppShow x)]
info _ x = return ()

withSE = mapWriterT' $ fmap $ \(se, x) -> (se, (se, x))

addRange' msg = addRangeBy' msg id
addRangeBy' msg f r m = addRange r $ do
    (se, x) <- withSE m
    addRange_ msg r se $ f x
    return x

addRangeBy f r m = addRange r $ do
    x <- m
    info r =<< typingToTy' (f x)
    return x

addRange_ msg r se x = info r =<< typingToTy msg se (tyOf x)

inferType_ :: Bool -> Bool -> ExpR -> TCMS Exp
inferType_ addcst allowNewVar e_@(ExpR r e) = addRange' (pShow e_) r $ addCtx ("type inference of" <+> pShow e) $ appSES $ case e of
    EPrec_ e es -> do
        ps <- asks precedences
        infer =<< calcPrec (\a b c -> application [a, b, c]) (\(EVarR' _ n) -> n) ps e es
    -- hack
    ENamedRecord_ n (unzip -> (fs, es)) ->
        inferTyping $ foldl (EAppR' mempty) (EVarR' mempty n) es

    ELam_ h p f -> {-mapWriterT' (fmap $ \(se, x) -> trace (" -- " ++ ppShow p ++ ppShow se) (se, x) ) $ -} do
        h <- traverse infer h
        (se, (p, tr)) <- lift $ runWriterT' $ inferPatTyping False p
        addConstraints se
        f <- addCtx "?" $ withTyping (tr <> (tyOfItem <$> getTEnv se)) $ inferTyping f
        case h of
            Just t -> removeMonoVars $ do
                n <- newName "?"
                let t' = Exp $ Forall_ Hidden (Just n) (tyOfPat p) (tyOf f)
                    tp = tyOfPat p
                addUnif t t'
                singSubstTy n tp
                return (Set.singleton n, Exp $ ELam_ (Just t') p f)
            Nothing -> return $ Exp $ ELam_ Nothing p f

    ELet_ p@(PVar' _ n) x_ e -> do
        (se, x) <- lift $ do
            (se, x) <- runWriterT'' $ inferTyping x_
            let (se', se'') = splitEnv se
            (fs, it) <- addRange (getTag x_) $ addCtx "let" $ instantiateTyping_' True (pShow n) se' $ tyOf x
            return (se'', foldr eLam' x fs)
--            addRange_ ("var" <+> pShow n) (getTag p `mappend` getTag x_) se x
        addConstraints $ TEnv $ Map.filter (eitherItem (\r -> const $ not r) (\_ -> const False)) $ getTEnv se
        e <- withTyping (Map.singleton n $ tyOf x) $ inferTyping e
        return $ ELet (PVar (tyOf x) n) x e
    ELet_ p x e -> infer $ ExpR mempty $ EApp_ TWildcard (ExpR mempty $ ELam_ Nothing p e) x             -- monomorph let; TODO
    ETypeSig_ e ty -> do
        e <- inferTyping e
        ty <- inferType ty
        addUnifOneDir (tyOf e) ty
        return e
    ETyApp_ TWildcard f t -> do
        f <- inferTyping f
        t <- inferType t
        v <- forallApp (tyOf f) t
        return $ TApp v f t

    Forall_ h (Just n) k t -> removeMonoVars $ do
        k <- inferType k
        singSubstTy n k
        t <- withTyping (monoInstType n k) $ inferType t
        return $ (,) (Set.fromList [n]) $ Exp $ Forall_ h (Just n) k t

    EVar_ TWildcard n -> do
        (ty, t) <- lookEnv n $ if allowNewVar
                then newStarVar' "tvar" n >>= \t -> return ([], t)
                else throwErrorTCM $ "Variable" <+> pShow n <+> "is not in scope."
        return $ buildApp (`TVar` n) t ty

    TCon_ TWildcard n -> do
        (fn, t) <- lookEnv n $ lookLifted $ throwErrorTCM $ "Type constructor" <+> pShow n <+> "is not in scope."
        return $ buildApp (Exp . (`TCon_` n)) t fn
      where
        lookLifted = if isTypeVar n then lookEnv (toExpN n) else id

    EApp_ TWildcard tf_ ta_ -> do
        tf <- infer tf_
        ta <- infer ta_
        t <- appTy (tyOf tf) (tyOf ta)
        return $ Exp $ EApp_ t tf ta

    TWildcard_ -> newStarVar "_"

    _ -> do
        e <- mapExp_ id (error "infertype") <$> traverse infer e
        case e of
            EFieldProj_ t fn -> do
                a <- newStarVar "fp1"
                r <- newStarVar "fp2"
                r' <- newStarVar "fp3"
                addConstraint $ Split r r' $ TRecord $ Map.singleton (IdN fn) a
                addUnif t $ r ~> a

            EAlts_ xs -> addUnifs True [map tyOf xs]
            TTuple_ ts -> mapM_ checkStarKind ts

            CEq_ (tyOf -> t) (TypeFun f (map tyOf -> ts)) -> do
                (_, tf) <- lookEnv' f $ throwErrorTCM $ "Type family" <+> pShow f <+> "is not in scope."
                addUnif tf $ ts ~~> t

            Forall_ _ Nothing a b -> checkStarKind a >> checkStarKind b

            x -> return ()
        case e of
            Forall_ (hidden -> True) Nothing c b | addcst -> do
                addConstraint c
                return b
            e -> return $ Exp e
  where
    infer = inferType_ addcst allowNewVar

--------------------------------------------------------------------------------

tyConKind :: [ExpR] -> TCM Exp
tyConKind = tyConKind_ $ ExpR mempty Star_

tyConKind_ :: ExpR -> [ExpR] -> TCM Exp
tyConKind_ res vs = instantiateTyping "tyconkind" $ inferType $ foldr (\a b -> ExpR' $ Forall_ Visible Nothing a b) res vs

inferConDef :: Name -> [(Name, ExpR)] -> WithRange ConDef -> TCM InstEnv
inferConDef con ks (r, ConDef n tys) = addRange r $ do
    ty <- instantiateTyping (pShow con) $ inferType $ foldr
            (\(vn, vt) b -> ExpR' $ Forall_ Irrelevant (Just vn) vt b)
            (foldr (\a b -> ExpR' (Forall_ Visible Nothing a b)) (tyConResTy con $ map fst ks) [t | FieldTy _ t <- tys])
            ks
    return $ Map.singleton n ty

inferConDef' :: Name -> [(Name, ExpR)] -> WithRange (Name, ConDef') -> TCM InstEnv
inferConDef' con ks (r, (n, ConDef' ctx tys res)) = addRange r $ do
    ty <- instantiateTyping (pShow con) $ inferType $ {-foldr
            (\(vn, vt) b -> ExpR' $ Forall_ Irrelevant (Just vn) vt b)-}
            (foldr
                (\(n, a) b -> ExpR' (maybe (Forall_ Hidden Nothing) (Forall_ Visible . Just) n a b))
                (foldr (\a b -> ExpR' (Forall_ Visible Nothing a b)) res [t | FieldTy _ t <- tys])
                ctx
            )
     {-       $ filter (not . (`elem` map fst ctx) . Just . fst)
             ks -}
    return $ Map.singleton n ty

tyConResTy con vn
    = application $ (ExpR' $ TCon_ TWildcard con): map (ExpR' . EVar_ TWildcard) vn
tyConResTy' con vn
    = application $ (ExpR' $ TCon_ TWildcard con): vn

selectorDefs :: DefinitionR -> [DefinitionR]
selectorDefs (r, DDataDef n _ cs) =
    [ (r, DValueDef False $ ValueDef False
      ( PatR' $ PVar_ TWildcard sel)
      ( ExpR' $ ELam_ (if ctx then Just TWildcard else Nothing)
            (PatR' $ PCon_ TWildcard cn
                [ if i == j then PVar' mempty (ExpN "x") else PatR mempty (Wildcard_ TWildcard)
                | (j, _) <- zip [0..] tys]
            )
            (EVarR' mempty $ ExpN "x")
      ))
    | (rc, ConDef cn tys) <- cs
    , (i, FieldTy (Just (sel, ctx)) t) <- zip [0..] tys
    ]
selectorDefs (r, GADT n _ cs) =
    [ (r, DValueDef False $ ValueDef False
      ( PatR' $ PVar_ TWildcard sel)
      ( ExpR' $ ELam_ (if ctx then Just TWildcard else Nothing)
            (PatR' $ PCon_ TWildcard cn
                [ if i == j then PVar' mempty (ExpN "x") else PatR mempty (Wildcard_ TWildcard)
                | (j, _) <- zip [0..] tys]
            )
            (EVarR' mempty $ ExpN "x")
      ))
    | (rc, (cn, ConDef' _ctx' tys _res)) <- cs
    , (i, FieldTy (Just (sel, ctx)) t) <- zip [0..] tys
    ]

--inferDef :: ValueDefR -> TCM (TCM a -> TCM a)
inferDef (ValueDef True p e)
    = inferDef $ ValueDef False p $ application [EVarR' mempty fixName, ExpR' $ ELam_ Nothing p e]
inferDef (ValueDef False p@(PVar' _ n) e) = do
    (se, exp) <- runWriterT' $ inferTyping e
    (fs, f) <- addCtx ("inst" <+> pShow p) $ instantiateTyping_' True (pShow p) se $ tyOf exp
    the <- asks getPolyEnv
    let th = subst ( toSubst (TEnv the)
                   )
           $ flip (foldr eLam') fs exp
    return (n, th)
inferDef (ValueDef _ p e) = error $ "inferDef: " ++ ppShow p

classDictName = toExpN . addPrefix "Dict"

withThunk n th = addPolyEnv $ emptyPolyEnv {getPolyEnv = Map.singleton n $ ISubst True th}

inferDefs :: [DefinitionR] -> TCM PolyEnv
inferDefs [] = ask
inferDefs (dr@(r, d): ds@(inferDefs -> cont)) = {-addRange r $ -}case d of
    PrecDef n p -> addPolyEnv (emptyPolyEnv {precedences = Map.singleton n p}) cont
    DValueDef inst d -> do
        (n, th) <- addRangeBy (\(_,th) -> envType *** id $ toEnvType $ tyOf th) r $ inferDef d
        withThunk n th . (if inst then addInstance n $ tyOf th else id) $ cont
    TypeFamilyDef con vars res -> do
        tk <- tyConKind_ res $ map snd vars
        addPolyEnv (emptyPolyEnv {typeFamilies = Map.singleton con tk}) cont
    DAxiom (TypeSig n t) -> do
        t <- instantiateTyping (pShow n) $ inferType t
        let res (Exp (Forall_ _ _ a b)) = res b
            res t = t
            n' = (if isStar $ res t then toTypeN else id) n
            isPrim (ExpN s) = take 4 s `elem` ["prim", "Prim"]
            arity = f t where
                f (Exp (Forall_ h _ _ x)) = (case h of Visible -> 1; _ -> 0) + f x
                f _ = 0
            f | isPrim n = withThunk n $ Exp $ PrimFun t n [] arity
              | otherwise = withTyping $ Map.singleton n' t
        f cont
    GADT con vars cdefs -> do
        tk <- tyConKind $ map snd vars
        withTyping (Map.singleton con tk) $ do
            ev <- mapM (inferConDef' con vars) cdefs
            withTyping (mconcat ev) $ inferDefs $ selectorDefs dr ++ ds
    DDataDef con vars cdefs -> do
        tk <- tyConKind $ map snd vars
        withTyping (Map.singleton con tk) $ do
            ev <- mapM (inferConDef con vars) cdefs
            withTyping (mconcat ev) $ inferDefs $ selectorDefs dr ++ ds

    ClassDef ctx{-TODO-} con vars cdefs -> inferDefs $ (r, d'): ds
      where
        d' = DDataDef con vars
                [WithRange mempty $ ConDef (classDictName con) [FieldTy (Just (n, True)) t | TypeSig n t <- cdefs]]

    InstanceDef ctx con vars xs -> inferDefs $ (r, d'): ds
      where
        iname = addPrefix "instance" $ ExpN $ ppShow $ application $ ExpR' (EVar_ TWildcard con): vars
        d' = DValueDef True $ ValueDef True (PatR' $ PVar_ TWildcard iname) $
                ExpR' $ ETypeSig_
                    (application $ (ExpR' $ EVar_ TWildcard $ classDictName con): [e | ValueDef _ (PVar' _ n{-TODO-}) e <- xs])
                    (tyConResTy' con vars)

    _ -> error $ "inferDefs: " ++ ppShow d

inference_ :: PolyEnv -> ModuleR -> ErrorT (WriterT Infos (VarMT Identity)) PolyEnv
inference_ penv@PolyEnv{..} Module{..} = do
    resetVars
    ExceptT $ mapWriterT (fmap $ (id +++ diffEnv) *** id) (runExceptT $ flip runReaderT penv $ addPolyEnv startPolyEnv $ inferDefs definitions)
  where
    diffEnv (PolyEnv i g p tf _) = PolyEnv
        (Map.differenceWith (\a b -> Just $ a Map.\\ b) i instanceDefs)
        (g Map.\\ getPolyEnv)
        (p Map.\\ precedences)
        (tf Map.\\ typeFamilies)
        mempty --infos

