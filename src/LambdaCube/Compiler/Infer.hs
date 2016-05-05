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
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}  -- TODO: remove
{-# OPTIONS_GHC -fno-warn-unused-binds #-}  -- TODO: remove
-- {-# OPTIONS_GHC -O0 #-}
module LambdaCube.Compiler.Infer
    ( inference
    , neutType'
    , makeCaseFunPars'
    ) where

import Data.Function
import Data.Monoid
import Data.Maybe
import Data.List
import qualified Data.Set as Set

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Arrow hiding ((<+>))

import LambdaCube.Compiler.Utils
import LambdaCube.Compiler.DeBruijn
import LambdaCube.Compiler.Pretty hiding (braces, parens)
import LambdaCube.Compiler.DesugaredSource hiding (getList)
import LambdaCube.Compiler.Statements (addFix)
import LambdaCube.Compiler.Core
import LambdaCube.Compiler.InferMonad

------------------------------------------------------------------------------------

varType :: String -> Int -> Env -> (Binder, Exp)
varType err n_ env = f n_ env where
    f n (EAssign i (ET x _) es) = second (subst i x) $ f (if n < i then n else n+1) es
    f n (EBind2 b t es)  = if n == 0 then (b, up 1 t) else second (up 1) $ f (n-1) es
    f n (ELet2 _ (ET x t) es) = if n == 0 then (BLam Visible{-??-}, up 1 t) else second (up 1) $ f (n-1) es
    f n e = either (error $ "varType: " ++ err ++ "\n" ++ show n_ ++ "\n" ++ ppShow env) (f n) $ parent e

mkELet n x xt env = {-(if null vs then id else trace_ $ "mkELet " ++ show (length vs) ++ " " ++ show n)-} term
  where
    vs = sort $ Set.toList $ join grow $ free x <> free xt
    nloc = length vs
    fn = FunName (mkFName n) nloc (ExpDef $ addLams 0 vs x) (addPis 0 vs xt)

    term = mkFun fn (Var <$> reverse vs) $ getFix x 0

    addLams l [] x = x
    addLams l (v: vs) x = Lam $ rMove v l $ addLams (l+1) vs x

    addPis l [] x = x
    addPis l (v: vs) x = Pi Visible (snd $ varType "mkELet" v env) $ rMove v l $ addPis (l+1) vs x

    grow acc s
        | Set.null s = acc
        | otherwise = grow (s' <> acc) (s' Set.\\ acc)
      where
        s' = mconcat (free . snd . flip (varType "mkELet2") env <$> Set.toList s)

    getFix (Lam z) i = Lam $ getFix z (i+1)
    getFix (DFun FprimFix _ [t, Lam f]) i = subst 0 (foldl app_ term (downTo 0 i)) f
    getFix x _ = x



instance PShow (CEnv Exp) where
    pShow = mkDoc False

instance PShow Env where
    pShow e = envDoc e $ underline $ text "<<HERE>>"

showEnvExp :: Env -> ExpType -> String
showEnvExp e c = show $ envDoc e $ underline $ mkDoc False c

showEnvSExp :: (PShow a, Up a) => Env -> SExp' a -> String
showEnvSExp e c = show $ envDoc e $ underline $ pShow c

showEnvSExpType :: (PShow a, Up a) => Env -> SExp' a -> Exp -> String
showEnvSExpType e c t = show $ envDoc e $ underline $ (shAnn (pShow c) (mkDoc False t))

envDoc :: Env -> Doc -> Doc
envDoc x m = case x of
    EGlobal{}           -> m
    EBind1 _ h ts b     -> envDoc ts $ shLam (usedVar 0 b) h m (pShow b)
    EBind2 h a ts       -> envDoc ts $ shLam True h (mkDoc False a) m
    EApp1 _ h ts b      -> envDoc ts $ shApp h m (pShow b)
    EApp2 _ h (ET (Lam (Var 0)) (Pi Visible TType _)) ts -> envDoc ts $ shApp h (text "tyType") m
    EApp2 _ h a ts      -> envDoc ts $ shApp h (mkDoc False a) m
    ELet1 _ ts b        -> envDoc ts $ shLet_ m (pShow b)
    ELet2 _ x ts        -> envDoc ts $ shLet_ (mkDoc False x) m
    EAssign i x ts      -> envDoc ts $ shLet i (mkDoc False x) m
    CheckType t ts      -> envDoc ts $ shAnn m $ mkDoc False t
    CheckIType t ts     -> envDoc ts $ shAnn m (text "??") -- mkDoc ts' t
--    CheckSame t ts      -> envDoc ts $ shCstr <$> m <*> mkDoc ts' t
    CheckAppType si h t te b -> envDoc (EApp1 si h (CheckType_ (sourceInfo b) t te) b) m
    ERHS ts        -> envDoc ts $ shApp Visible (text "labEnd") m
    x   -> error $ "envDoc: " ++ ppShow x

instance MkDoc (CEnv Exp) where
    mkDoc pr e = green $ f e
      where
        f :: CEnv Exp -> Doc
        f = \case
            MEnd a          -> mkDoc pr a
            Meta a b        -> shLam True BMeta (mkDoc pr a) (f b)
            Assign i (ET x _) e -> shLet i (mkDoc pr x) (f e)

-------------------------------------------------------------------------------- constraints env

data CEnv a
    = MEnd a
    | Meta Exp (CEnv a)
    | Assign !Int ExpType (CEnv a)       -- De Bruijn index decreasing assign reservedOp, only for metavariables (non-recursive)
  deriving (Functor)

instance (Subst Exp a, Up a) => Up (CEnv a) where
    usedVar i a = error "usedVar @(CEnv _)"
    foldVar _ _ _ = error "foldVar @(CEnv _)"
--    maxDB_ _ = error "maxDB_ @(CEnv _)"

instance (Subst Exp a, Rearrange a) => Rearrange (CEnv a) where
    rearrange l f = \case
            MEnd a -> MEnd $ rearrange l f a
            Meta a b -> Meta (rearrange l f a) (rearrange (l+1) f b)
            Assign j a b
                | l >  j -> assign j (rearrange (l-1) f a) (rearrange (l-1) f b)
                | l <= j -> assign (f (j-l) + l) (rearrange l f a) (rearrange l f b)

instance (Subst Exp a, Rearrange a) => Subst Exp (CEnv a) where
    subst_ i dx x = \case
        MEnd a -> MEnd $ subst_ i dx x a
        Meta a b  -> Meta (subst_ i dx x a) (subst_ (i+1) (upDB 1 dx) (up 1 x) b)
        Assign j a b
            | j > i, Just a' <- down i a       -> assign (j-1) a' (subst i (subst (j-1) (expr a') x) b)
            | j > i, Just x' <- down (j-1) x   -> assign (j-1) (subst i x' a) (subst i x' b)
            | j < i, Just a' <- down (i-1) a   -> assign j a' (subst (i-1) (subst j (expr a') x) b)
            | j < i, Just x' <- down j x       -> assign j (subst (i-1) x' a) (subst (i-1) x' b)
            | j == i                           -> Meta (cstr_ (ty a) x $ expr a) $ up1_ 0 b

--swapAssign :: (Int -> Exp -> CEnv Exp -> a) -> (Int -> Exp -> CEnv Exp -> a) -> Int -> Exp -> CEnv Exp -> a
swapAssign _ clet i (ET (Var j) t) b | i > j = clet j (ET (Var (i-1)) t) $ subst j (Var (i-1)) $ up1_ i b
swapAssign clet _ i a b = clet i a b

--assign :: Rearrange a => Int -> ExpType -> CEnv a -> CEnv a
assign = swapAssign Assign Assign

replaceMetas bind = \case
    Meta a t -> bind a $ replaceMetas bind t
    Assign i x t | x' <- up1_ i x -> bind (cstr_ (ty x') (Var i) $ expr x') . up 1 . up1_ i $ replaceMetas bind t
    MEnd t ->  t


-------------------------------------------------------------------------------- environments

-- SExp + Exp zipper
data Env
    = EBind1 SI Binder Env SExp2            -- zoom into first parameter of SBind
    | EBind2_ SI Binder Type Env             -- zoom into second parameter of SBind
    | EApp1 SI Visibility Env SExp2
    | EApp2 SI Visibility ExpType Env
    | ELet1 SIName Env SExp2
    | ELet2 SIName ExpType Env
    | EGlobal
    | ERHS Env

    | EAssign Int ExpType Env
    | CheckType_ SI Type Env
    | CheckIType SExp2 Env
--    | CheckSame Exp Env
    | CheckAppType SI Visibility Type Env SExp2   --pattern CheckAppType _ h t te b = EApp1 _ h (CheckType t te) b

pattern EBind2 b e env <- EBind2_ _ b e env where EBind2 b e env = EBind2_ (debugSI "6") b e env
pattern CheckType e env <- CheckType_ _ e env where CheckType e env = CheckType_ (debugSI "7") e env

parent = \case
    EAssign _ _ x        -> Right x
    EBind2 _ _ x         -> Right x
    EBind1 _ _ x _       -> Right x
    EApp1 _ _ x _        -> Right x
    EApp2 _ _ _ x        -> Right x
    ELet1 _ x _          -> Right x
    ELet2 _ _ x          -> Right x
    CheckType _ x        -> Right x
    CheckIType _ x       -> Right x
--    CheckSame _ x        -> Right x
    CheckAppType _ _ _ x _ -> Right x
    ERHS x               -> Right x
    EGlobal              -> Left ()

-------------------------------------------------------------------------------- simple typing

neutType te = \case
    App_ f x        -> appTy (neutType te f) x
    Var_ i          -> snd $ varType "C" i te
    CaseFun_ s ts n -> appTy (foldl appTy (nType s) $ makeCaseFunPars te n ++ ts) (Neut n)
    TyCaseFun_ s [m, t, f] n -> foldl appTy (nType s) [m, t, Neut n, f]
    Fun s a _      -> foldlrev appTy (nType s) a

neutType' te = \case
    App_ f x        -> appTy (neutType' te f) x
    Var_ i          -> varType' i te
    CaseFun_ s ts n -> appTy (foldl appTy (nType s) $ makeCaseFunPars' te n ++ ts) (Neut n)
    TyCaseFun_ s [m, t, f] n -> foldl appTy (nType s) [m, t, Neut n, f]
    Fun s a _      -> foldlrev appTy (nType s) a

makeCaseFunPars te n = case neutType te n of
    (hnf -> TyCon (TyConName _ _ _ _ (CaseFunName _ _ pars)) xs) -> take pars xs
    x -> error $ "makeCaseFunPars: " ++ ppShow x

makeCaseFunPars' te n = case neutType' te n of
    (hnf -> TyCon (TyConName _ _ _ _ (CaseFunName _ _ pars)) xs) -> take pars xs

-------------------------------------------------------------------------------- inference

type ExpType' = CEnv ExpType

inferN :: forall m . Monad m => Env -> SExp2 -> IM m ExpType'
inferN e s = do
    b <- asks $ (TraceTypeCheck `elem`) . fst
    mapExceptT (mapReaderT $ mapWriterT $ fmap filt) $ inferN_ (if b then \s x m -> tell [ITrace s x] >> m else \_ _ m -> m) e s
  where
    filt (e@Right{}, is) = (e, filter f is)
    filt x = x

    f ITrace{} = False
    f _ = True

substTo i x = subst i x . up1_ (i+1)

inferN_ :: forall m . Monad m => (forall a . String -> String -> IM m a -> IM m a) -> Env -> SExp2 -> IM m ExpType'
inferN_ tellTrace = infer  where

    infer :: Env -> SExp2 -> IM m ExpType'
    infer te exp = tellTrace "infer" (showEnvSExp te exp) $ case exp of
        Parens x        -> infer te x
        SAnn x t        -> checkN (CheckIType x te) t TType
        SRHS x          -> infer (ERHS te) x
        SVar sn i       -> focusTell te exp $ ET (Var i) $ snd $ varType "C2" i te
        SLit si l       -> focusTell te exp $ ET (ELit l) (nType l)
        STyped et       -> focusTell' te exp et
        SGlobal (SIName si s) -> focusTell te exp =<< getDef te si s
        SLet le a b     -> infer (ELet1 le te b{-in-}) a{-let-} -- infer te SLamV b `SAppV` a)
        SApp_ si h a b  -> infer (EApp1 (si `validate` [sourceInfo a, sourceInfo b]) h te b) a
        SBind_ si h _ a b -> infer ((if h /= BMeta then CheckType_ (sourceInfo exp) TType else id) $ EBind1 si h te $ (if isPi h then TyType else id) b) a

    checkN :: Env -> SExp2 -> Type -> IM m ExpType'
    checkN te x t = tellTrace "check" (showEnvSExpType te x t) $ checkN_ te x t

    checkN_ te (Parens e) t = checkN_ te e t
    checkN_ te e t
        | x@(SGlobal (sName -> MatchName n)) `SAppV` SLamV (Wildcard _) `SAppV` a `SAppV` SVar siv v `SAppV` b <- e
            = infer te $ x `SAppV` SLam Visible SType (STyped (ET (subst (v+1) (Var 0) $ up 1 t) TType)) `SAppV` a `SAppV` SVar siv v `SAppV` b
            -- temporal hack
        | x@(SGlobal (sName -> CaseName "'Nat")) `SAppV` SLamV (Wildcard _) `SAppV` a `SAppV` b `SAppV` SVar siv v <- e
            = infer te $ x `SAppV` SLamV (STyped (ET (substTo (v+1) (Var 0) $ up 1 t) TType)) `SAppV` a `SAppV` b `SAppV` SVar siv v
            -- temporal hack
        | x@(SGlobal (sName -> CaseName "'VecS")) `SAppV` SLamV (SLamV (Wildcard _)) `SAppV` a `SAppV` b `SAppV` c `SAppV` SVar siv v <- e
        , TyConN FVecS [_, Var n'] <- snd $ varType "xx" v te
            = infer te $ x `SAppV` SLamV (SLamV (STyped (ET (substTo (n'+2) (Var 1) $ up 2 t) TType))) `SAppV` a `SAppV` b `SAppV` c `SAppV` SVar siv v

{-
            -- temporal hack
        | x@(SGlobal (si, "'HListCase")) `SAppV` SLamV (SLamV (Wildcard _)) `SAppV` a `SAppV` b `SAppV` SVar siv v <- e
        , TVec (Var n') _ <- snd $ varType "xx" v te
            = infer te $ x `SAppV` SLamV (SLamV (STyped (subst (n'+2) (Var 1) $ up1_ (n'+3) $ up 2 t, TType))) `SAppV` a `SAppV` b `SAppV` SVar siv v
-}
        | SRHS x <- e = checkN (ERHS te) x t
        | SApp_ si h a b <- e = infer (CheckAppType si h t te b) a
        | SLam h a b <- e, Pi h' x y <- t, h == h'  = do
--            tellType e t
            let same = checkSame te a x
            if same then checkN (EBind2 (BLam h) x te) b y else error $ "checkSame:\n" ++ ppShow a ++ "\nwith\n" ++ showEnvExp te (ET x TType)
        | Pi Hidden a b <- t = do
            bb <- notHiddenLam e
            if bb then checkN (EBind2 (BLam Hidden) a te) (up1 e) b
                 else infer (CheckType_ (sourceInfo e) t te) e
        | otherwise = infer (CheckType_ (sourceInfo e) t te) e
      where
        -- todo
        notHiddenLam = \case
            SLam Visible _ _ -> return True
            SGlobal (sName -> s) -> do
                nv <- asks snd
                case fromMaybe (error $ "infer: can't find: " ++ s) $ lookupName s nv of
                    ET (Lam _) (Pi Hidden _ _) -> return False
                    _ -> return True
            _ -> return False
{-
    -- todo
    checkSame te (Wildcard _) a = return (te, True)
    checkSame te x y = do
        (ex, _) <- checkN te x TType
        return $ ex == y
-}
    checkSame te (Wildcard _) a = True
    checkSame te SType TType = True
    checkSame te (SBind_ _ BMeta _ SType (STyped (ET (Var 0) _))) a = True
    checkSame te a b = error $ "checkSame: " ++ ppShow (a, b)

    hArgs (Pi Hidden _ b) = 1 + hArgs b
    hArgs _ = 0

    focusTell env si eet = tellType si (ty eet) >> focus_ env eet
    focusTell' env si eet = focus_ env eet

    focus_ :: Env -> ExpType -> IM m ExpType'
    focus_ env eet@(ET e et) = tellTrace "focus" (showEnvExp env eet) $ case env of
        ERHS te -> focus_ te (ET (RHS e) et)
--        CheckSame x te -> focus_ (EBind2_ (debugSI "focus_ CheckSame") BMeta (cstr x e) te) $ up 1 eet
        CheckAppType si h t te b   -- App1 h (CheckType t te) b
            | Pi h' x (down 0 -> Just y) <- et, h == h' -> case t of
                Pi Hidden t1 t2 | h == Visible -> focus_ (EApp1 si h (CheckType_ (sourceInfo b) t te) b) eet  -- <<e>> b : {t1} -> {t2}
                _ -> focus_ (EBind2_ (sourceInfo b) BMeta (cstr_ TType t y) $ EApp1 si h te b) $ up 1 eet
            | otherwise -> focus_ (EApp1 si h (CheckType_ (sourceInfo b) t te) b) eet
        EApp1 si h te b
            | Pi h' x y <- et, h == h' -> checkN (EApp2 si h eet te) b x
            | Pi Hidden x y  <- et, h == Visible -> focus_ (EApp1 mempty Hidden env $ Wildcard $ Wildcard SType) eet  --  e b --> e _ b
--            | CheckType (Pi Hidden _ _) te' <- te -> error "ok"
--            | CheckAppType Hidden _ te' _ <- te -> error "ok"
            | otherwise -> infer (CheckType_ (sourceInfo b) (Var 2) $ cstr' h (up 2 et) (Pi Visible (Var 1) (Var 1)) (up 2 e) $ EBind2_ (sourceInfo b) BMeta TType $ EBind2_ (sourceInfo b) BMeta TType te) (up 3 b)
          where
            cstr' h x y e = EApp2 mempty h (ET (evalCoe (up 1 x) (up 1 y) (Var 0) (up 1 e)) (up 1 y)) . EBind2_ (sourceInfo b) BMeta (cstr_ TType x y)
        ELet2 ln (ET x{-let-} xt) te -> focus_ te $ subst 0 (mkELet ln x xt te){-let-} eet{-in-}
        CheckIType x te -> checkN te x e
        CheckType_ si t te
            | hArgs et > hArgs t
                            -> focus_ (EApp1 mempty Hidden (CheckType_ si t te) $ Wildcard $ Wildcard SType) eet
            | hArgs et < hArgs t, Pi Hidden t1 t2 <- t
                            -> focus_ (CheckType_ si t2 $ EBind2 (BLam Hidden) t1 te) eet
            | otherwise    -> focus_ (EBind2_ si BMeta (cstr_ TType t et) te) $ up 1 eet
        EApp2 si h (ET a at) te    -> focusTell te si $ ET (app_ a e) (appTy at e)        --  h??
        EBind1 si h te b   -> infer (EBind2_ (sourceInfo b) h e te) b
        EBind2_ si (BLam h) a te -> focus_ te $ lamPi h a eet
        EBind2_ si (BPi h) a te -> focusTell te si $ ET (Pi h a e) TType
        _ -> focus2 env $ MEnd eet

    focus2 :: Env -> CEnv ExpType -> IM m ExpType'
    focus2 env eet = case env of
        ELet1 le te b{-in-} -> infer (ELet2 le (replaceMetas' eet{-let-}) te) b{-in-}
        EBind2_ si BMeta tt_ te
            | ERHS te'   <- te -> refocus (ERHS $ EBind2_ si BMeta tt_ te') eet
            | Unit <- tt    -> refocus te $ subst 0 TT eet
            | Empty msg <- tt -> throwError' $ ETypeError (text msg) si
            | CW (hnf -> T2 x y) <- tt, let te' = EBind2_ si BMeta (up 1 $ cw y) $ EBind2_ si BMeta (cw x) te
                            -> refocus te' $ subst 2 (t2C (Var 1) (Var 0)) $ up 2 eet
            | CW (hnf -> CstrT t a b) <- tt, Just r <- cst (ET a t) b -> r
            | CW (hnf -> CstrT t a b) <- tt, Just r <- cst (ET b t) a -> r
            | CW _ <- tt, EBind2 h x te' <- te, Just x' <- down 0 tt, x == x'
                            -> refocus te $ subst 1 (Var 0) eet
            | EBind2_ si' h x te' <- te, h /= BMeta, Just b' <- down 0 tt
                            -> refocus (EBind2_ si' h (up 1 x) $ EBind2_ si BMeta b' te') $ subst 2 (Var 0) $ up 1 eet
            | ELet2 le x te' <- te, Just b' <- down 0 tt
                            -> refocus (ELet2 le (up 1 x) $ EBind2_ si BMeta b' te') $ subst 2 (Var 0) $ up 1 eet
            | EBind1 si h te' x <- te -> refocus (EBind1 si h (EBind2_ si BMeta tt_ te') $ up1_ 1 x) eet
            | ELet1 le te' x     <- te, floatLetMeta $ ty $ replaceMetas' $ Meta tt_ eet
                                    -> refocus (ELet1 le (EBind2_ si BMeta tt_ te') $ up1_ 1 x) eet
            | CheckAppType si h t te' x <- te -> refocus (CheckAppType si h (up 1 t) (EBind2_ si BMeta tt_ te') $ up1 x) eet
            | EApp1 si h te' x <- te -> refocus (EApp1 si h (EBind2_ si BMeta tt_ te') $ up1 x) eet
            | EApp2 si h x te' <- te -> refocus (EApp2 si h (up 1 x) $ EBind2_ si BMeta tt_ te') eet
            | CheckType_ si t te' <- te -> refocus (CheckType_ si (up 1 t) $ EBind2_ si BMeta tt_ te') eet
--            | CheckIType x te' <- te -> refocus (CheckType_ si (up 1 t) $ EBind2_ si BMeta tt te') eet
            | otherwise             -> focus2 te $ Meta tt_ eet
          where
            tt = hnf tt_
            refocus = refocus_ focus2
            cst :: ExpType -> Exp -> Maybe (IM m ExpType')
            cst x = \case
                Var i | fst (varType "X" i te) == BMeta
                      , Just y <- down i x
                      -> Just $ join swapAssign (\i x -> refocus $ EAssign i x te) i y $ subst 0 {-ReflCstr y-}TT $ subst (i+1) (expr $ up 1 y) eet
                _ -> Nothing

        EAssign i b te -> case te of
            ERHS te'     -> refocus' (ERHS $ EAssign i b te') eet
            EBind2_ si h x te' | i > 0, Just b' <- down 0 b
                              -> refocus' (EBind2_ si h (subst (i-1) (expr b') x) (EAssign (i-1) b' te')) eet
            ELet2 le x te' | i > 0, Just b' <- down 0 b
                              -> refocus' (ELet2 le (subst (i-1) (expr b') x) (EAssign (i-1) b' te')) eet
            ELet1 le te' x    -> refocus' (ELet1 le (EAssign i b te') $ subst (i+1) (up 1 b) x) eet
            EBind1 si h te' x -> refocus' (EBind1 si h (EAssign i b te') $ subst (i+1) (up 1 b) x) eet
            CheckAppType si h t te' x -> refocus' (CheckAppType si h (subst i (expr b) t) (EAssign i b te') $ subst i b x) eet
            EApp1 si h te' x  -> refocus' (EApp1 si h (EAssign i b te') $ subst i b x) eet
            EApp2 si h x te'  -> refocus' (EApp2 si h (subst i (expr b) x) $ EAssign i b te') eet
            CheckType_ si t te'   -> refocus' (CheckType_ si (subst i (expr b) t) $ EAssign i b te') eet
            EAssign j a te' | i < j
                              -> refocus' (EAssign (j-1) (subst i (expr b) a) $ EAssign i (up1_ (j-1) b) te') eet
            t  | Just te' <- pull1 i b te -> refocus' te' eet
               | otherwise -> swapAssign (\i x -> focus2 te . Assign i x) (\i x -> refocus' $ EAssign i x te) i b eet
            -- todo: CheckSame Exp Env
          where
            refocus' = fix refocus_

            pull1 i b = \case
                EBind2_ si h x te | i > 0, Just b' <- down 0 b
                    -> EBind2_ si h (subst (i-1) (expr b') x) <$> pull1 (i-1) b' te
                EAssign j a te
                    | i < j  -> EAssign (j-1) (subst i (expr b) a) <$> pull1 i (up1_ (j-1) b) te
                    | j <= i -> EAssign j (subst i (expr b) a) <$> pull1 (i+1) (up1_ j b) te
                te  -> pull i te

            pull i = \case
                EBind2 BMeta _ te | i == 0 -> Just te
                EBind2_ si h x te | i > 0 -> EBind2_ si h <$> down (i-1) x <*> pull (i-1) te
                EAssign j a te  -> EAssign (if j <= i then j else j-1) <$> down i a <*> pull (if j <= i then i+1 else i) te
                _               -> Nothing

        EGlobal{} -> return eet
        _ -> case eet of
            MEnd x -> throwError' $ ErrorMsg $ "focus todo:" <+> pShow x
            _ -> throwError' $ ErrorMsg $ "focus checkMetas:" <+> pShow env <$$> pShow (expr <$> eet)
      where
        refocus_ :: (Env -> CEnv ExpType -> IM m ExpType') -> Env -> CEnv ExpType -> IM m ExpType'
        refocus_ _ e (MEnd at) = focus_ e at
        refocus_ f e (Meta x at) = f (EBind2 BMeta x e) at
        refocus_ _ e (Assign i x at) = focus2 (EAssign i x e) at

        replaceMetas' = replaceMetas $ lamPi Hidden

-------------------------------------------------------------------------------- re-checking

type Message = String

recheck :: Monad m => SIName -> Env -> ExpType -> m ExpType
recheck sn e = return . recheck' sn e

-- todo: check type also
recheck' :: SIName -> Env -> ExpType -> ExpType
recheck' sn e (ET x xt) = ET (recheck_ "main" (checkEnv e) (ET x xt)) xt
  where
    err s = error $ "At " ++ ppShow sn ++ "\n" ++ s

    checkEnv = \case
        e@EGlobal{} -> e
        EBind1 si h e b -> EBind1 si h (checkEnv e) b
        EBind2_ si h t e -> EBind2_ si h (checkType e t) $ checkEnv e            --  E [\(x :: t) -> e]    -> check  E [t]
        ELet1 le e b -> ELet1 le (checkEnv e) b
        ELet2 le x e -> ELet2 le (recheck'' "env" e x) $ checkEnv e
        EApp1 si h e b -> EApp1 si h (checkEnv e) b
        EApp2 si h a e -> EApp2 si h (recheck'' "env" e a) $ checkEnv e    --  E [a x]  ->  check
        EAssign i x e -> EAssign i (recheck'' "env" e $ up1_ i x) $ checkEnv e                -- __ <i := x>
        CheckType_ si x e -> CheckType_ si (checkType e x) $ checkEnv e
--        CheckSame x e -> CheckSame (recheck'' "env" e x) $ checkEnv e
        CheckAppType si h x e y -> CheckAppType si h (checkType e x) (checkEnv e) y

    recheck'' msg te a@(ET x xt) = ET (recheck_ msg te a) xt
    checkType te e = recheck_ "check" te (ET e TType)

    recheck_ msg te = \case
        ET (Var k) zt -> Var k    -- todo: check var type
        ET (Lam_ md b) (Pi h a bt) -> Lam_ md $ recheck_ "9" (EBind2 (BLam h) a te) (ET b bt)
        ET (Pi_ md h a b) TType -> Pi_ md h (checkType te a) $ checkType (EBind2 (BPi h) a te) b
        ET (ELit l) zt -> ELit l  -- todo: check literal type
        ET TType TType -> TType
        ET (Neut (App__ md a b)) zt
            | ET (Neut a') at <- recheck'' "app1" te $ ET (Neut a) (neutType te a)
            -> checkApps "a" [] zt (Neut . App__ md a' . head) te at [b]
        ET (Con_ md s n as) zt      -> checkApps (ppShow s) [] zt (Con_ md s n . drop (conParams s)) te (conType zt s) $ mkConPars n zt ++ as
        ET (TyCon_ md s as) zt      -> checkApps (ppShow s) [] zt (TyCon_ md s) te (nType s) as
        ET (CaseFun s@(CaseFunName _ t pars) as n) zt -> checkApps (ppShow s) [] zt (\xs -> evalCaseFun s (init $ drop pars xs) (last xs)) te (nType s) (makeCaseFunPars te n ++ as ++ [Neut n])
        ET (TyCaseFun s [m, t, f] n) zt  -> checkApps (ppShow s) [] zt (\[m, t, n, f] -> evalTyCaseFun s [m, t, f] n) te (nType s) [m, t, Neut n, f]
        ET (Neut (Fun_ md f a x)) zt -> checkApps "lab" [] zt (\xs -> Neut $ Fun_ md f (reverse xs) x) te (nType f) $ reverse a   -- TODO: recheck x
        ET (RHS x) zt -> RHS $ recheck_ msg te (ET x zt)
        ET Delta zt -> Delta
      where
        checkApps s acc zt f _ t []
            | t == zt = f $ reverse acc
            | otherwise = 
                     err $ "checkApps' " ++ s ++ " " ++ msg ++ "\n" ++ showEnvExp te{-todo-} (ET t TType) ++ "\n\n" ++ showEnvExp te (ET zt TType)
        checkApps s acc zt f te t@(hnf -> Pi h x y) (b_: xs) = checkApps (s++"+") (b: acc) zt f te (appTy t b) xs where b = recheck_ "checkApps" te (ET b_ x)
        checkApps s acc zt f te t _ =
             err $ "checkApps " ++ s ++ " " ++ msg ++ "\n" ++ showEnvExp te{-todo-} (ET t TType) ++ "\n\n" ++ showEnvExp e (ET x xt)

-------------------------------------------------------------------------------- inference for statements

inference :: MonadFix m => [Stmt] -> IM m [GlobalEnv]
inference [] = return []
inference (x:xs) = do
    y <- handleStmt x
    (y:) <$> withEnv y (inference xs)

handleStmt :: MonadFix m => Stmt -> IM m GlobalEnv
handleStmt = \case
  Primitive n t_ -> do
        t <- inferType n $ trSExp' t_
        tellType (sourceInfo n) t
        addToEnv n $ flip ET t $ lamify t $ DFun (mkFName n) t
  Let n mt t_ -> do
        let t__ = maybe id (flip SAnn) mt t_
        ET x t <- inferTerm n $ trSExp' $ addFix n t__
        tellType (sourceInfo n) t
        addToEnv n (ET (mkELet n x t EGlobal) t)
{-        -- hack
        when (snd (getParams t) == TType) $ do
            let ps' = fst $ getParams t
                t'' =   (TType :~> TType)
                  :~> addParams ps' (Var (length ps') `app_` DFun (FunName (snd n) t) (downTo 0 $ length ps'))
                  :~>  TType
                  :~> Var 2 `app_` Var 0
                  :~> Var 3 `app_` Var 1
            addToEnv (fst n, MatchName (snd n)) (lamify t'' $ \[m, tr, n', f] -> evalTyCaseFun (TyCaseFunName (snd n) t) [m, tr, f] n', t'')
-}
  PrecDef{} -> return mempty
  Data s (map (second trSExp') -> ps) (trSExp' -> t_@(UncurryS tl_ _)) cs -> do
    vty <- inferType s $ UncurryS ps t_
    tellType (sourceInfo s) vty
    let
        sint = mkFName s
        pnum' = length $ filter ((== Visible) . fst) ps
        inum = arity vty - length ps

        mkConstr j (cn, trSExp' -> ct@(UncurryS ctl (AppsS c (map snd -> xs))))
            | c == SGlobal s && take pnum' xs == downToS "a3" (length ctl) pnum'
            = do
                cty <- removeHiddenUnit <$> inferType cn (UncurryS [(Hidden, x) | (Visible, x) <- ps] ct)
--                tellType (sourceInfo cn) cty
                let     pars = zipWith (\x -> second $ STyped . flip ET TType . rUp (1+j) x) [0..] $ drop (length ps) $ fst $ getParams cty
                        act = length . fst . getParams $ cty
                        acts = map fst . fst . getParams $ cty
                        conn = ConName (mkFName cn) j cty
                e <- addToEnv cn $ ET (Con conn 0 []) cty
                return (e, ((conn, cty)
                       , UncurryS pars
                       $ (foldl SAppV (sVar ".cs" $ j + length pars) $ drop pnum' xs ++ [AppsS (SGlobal cn) (zip acts $ downToS ("a4 " ++ sName cn ++ " " ++ show (length ps)) (j+1+length pars) (length ps) ++ downToS "a5" 0 (act- length ps))]
                       :: SExp2)))
            | otherwise = throwError' $ ErrorMsg "illegal data definition (parameters are not uniform)" -- ++ show (c, cn, take pnum' xs, act)

        motive = UncurryS (replicate inum (Visible, Wildcard SType)) $
           SPi Visible (AppsS (SGlobal s) $ zip (map fst ps) (downToS "a6" inum $ length ps) ++ zip (map fst tl_) (downToS "a7" 0 inum)) SType

    (e1, es, tcn, cfn@(CaseFunName _ ct _), _, _) <- mfix $ \ ~(_, _, _, _, ct', cons') -> do
        let cfn = CaseFunName sint ct' $ length ps
        let tcn = TyConName sint inum vty (map fst cons') cfn
        e1 <- addToEnv s (ET (TyCon tcn []) vty)
        (unzip -> (mconcat -> es, cons)) <- withEnv e1 $ zipWithM mkConstr [0..] cs
        ct <- withEnv (e1 <> es) $ inferType s
            ( UncurryS
                ( [(Hidden, x) | (_, x) <- ps]
                ++ (Visible, motive)
                : map ((,) Visible . snd) cons
                ++ replicate inum (Hidden, Wildcard SType)
                ++ [(Visible, AppsS (SGlobal s) $ zip (map fst ps) (downToS "a8" (inum + length cs + 1) $ length ps) ++ zip (map fst tl_) (downToS "a9" 0 inum))]
                )
            $ foldl SAppV (sVar ".ct" $ length cs + inum + 1) $ downToS "a10" 1 inum ++ [sVar ".24" 0]
            )
        return (e1, es, tcn, cfn, ct, cons)

    e2 <- addToEnv (SIName (sourceInfo s) $ CaseName (sName s)) $ ET (lamify ct $ \xs -> evalCaseFun cfn (init $ drop (length ps) xs) (last xs)) ct
    let ps' = fst $ getParams vty
        t =   (TType :~> TType)
          :~> addParams ps' (Var (length ps') `app_` TyCon tcn (downTo 0 $ length ps'))
          :~>  TType
          :~> Var 2 `app_` Var 0
          :~> Var 3 `app_` Var 1
    e3 <- addToEnv (SIName (sourceInfo s) $ MatchName (sName s)) $ ET (lamify t $ \[m, tr, n, f] -> evalTyCaseFun (TyCaseFunName sint t) [m, tr, f] n) t
    return (e1 <> e2 <> e3 <> es)

  stmt -> error $ "handleStmt: " ++ ppShow stmt

inferTerm :: Monad m => SIName -> SExp2 -> IM m ExpType
inferTerm sn t = fmap closedExp $ recheck sn EGlobal . replaceMetas (lamPi Hidden) =<< inferN EGlobal t

inferType :: Monad m => SIName -> SExp2 -> IM m Type
inferType sn t = fmap (closedExp . expr)
    $ recheck sn EGlobal . flip ET TType . replaceMetas (Pi Hidden) . fmap expr
    =<< inferN (CheckType_ (sourceInfo sn) TType EGlobal) t


