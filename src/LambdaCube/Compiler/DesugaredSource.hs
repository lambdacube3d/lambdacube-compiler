{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
module LambdaCube.Compiler.DesugaredSource where

import Data.Monoid
import Data.Maybe
import Data.List
import Data.String
import Data.Function
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMap as IM
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Arrow hiding ((<+>))

import LambdaCube.Compiler.Utils

import qualified LambdaCube.Compiler.Pretty as Parser
import LambdaCube.Compiler.Pretty hiding (Doc, braces, parens)
import LambdaCube.Compiler.Lexer

-------------------------------------------------------------------------------- expression representation

data SExp' a
    = SLit    SI Lit
    | SGlobal SIName
    | SApp_   SI Visibility (SExp' a) (SExp' a)
    | SBind_  SI Binder (SData SIName){-parameter name-} (SExp' a) (SExp' a)
    | SVar_   (SData SIName) !Int
    | SLet_   SI (SData SIName) (SExp' a) (SExp' a)    -- let x = e in f   -->  SLet e f{-x is Var 0-}
    | STyped  a
  deriving (Eq, Show)

type SExp = SExp' Void

data Binder
    = BPi  Visibility
    | BLam Visibility
    | BMeta      -- a metavariable is like a floating hidden lambda
  deriving (Eq, Show)

data Visibility = Hidden | Visible
  deriving (Eq, Show)

dummyName s = SIName (debugSI s) ("v_" ++ s)
dummyName' = SData . dummyName
sVar = SVar . dummyName

pattern SBind v x a b <- SBind_ _ v x a b
  where SBind v x a b =  SBind_ (sourceInfo a <> sourceInfo b) v x a b
pattern SPi  h a b <- SBind (BPi  h) _ a b
  where SPi  h a b =  SBind (BPi  h) (dummyName' "SPi") a b
pattern SLam h a b <- SBind (BLam h) _ a b
  where SLam h a b =  SBind (BLam h) (dummyName' "SLam") a b
pattern Wildcard t <- SBind BMeta _ t (SVar _ 0)
  where Wildcard t =  SBind BMeta (dummyName' "Wildcard") t (sVar "Wildcard2" 0)
pattern SLet n a b <- SLet_ _ (SData n) a b
  where SLet n a b =  SLet_ (sourceInfo a <> sourceInfo b) (SData n) a b
pattern SLamV a  = SLam Visible (Wildcard SType) a
pattern SVar a b = SVar_ (SData a) b

pattern SApp h a b <- SApp_ _ h a b
  where SApp h a b =  SApp_ (sourceInfo a <> sourceInfo b) h a b
pattern SAppH a b    = SApp Hidden a b
pattern SAppV a b    = SApp Visible a b
pattern SAppV2 f a b = f `SAppV` a `SAppV` b

infixl 2 `SAppV`, `SAppH`

pattern SBuiltin s <- SGlobal (SIName _ s)
  where SBuiltin s =  SGlobal (SIName (debugSI $ "builtin " ++ s) s)

pattern SRHS a      = SBuiltin "^rhs"     `SAppV` a
pattern Section e   = SBuiltin "^section" `SAppV` e
pattern SType       = SBuiltin "'Type"
pattern Parens e    = SBuiltin "parens"   `SAppV` e
pattern SAnn a t    = SBuiltin "typeAnn"  `SAppH` t `SAppV` a
pattern TyType a    = SAnn a SType

-- builtin heterogenous list
pattern HList a   = SBuiltin "'HList" `SAppV` a
pattern HCons a b = SBuiltin "HCons" `SAppV` a `SAppV` b
pattern HNil      = SBuiltin "HNil"

-- builtin list
pattern BList a   = SBuiltin "'List" `SAppV` a
pattern BCons a b = SBuiltin "Cons" `SAppV` a `SAppV` b
pattern BNil      = SBuiltin "Nil"

getTTuple (HList (getList -> Just xs)) = xs
getTTuple x = [x]

getList BNil = Just []
getList (BCons x (getList -> Just y)) = Just (x:y)
getList _ = Nothing

sLit = SLit mempty

isPi (BPi _) = True
isPi _ = False

pattern UncurryS :: [(Visibility, SExp' a)] -> SExp' a -> SExp' a
pattern UncurryS ps t <- (getParamsS -> (ps, t))
  where UncurryS ps t = foldr (uncurry SPi) t ps

getParamsS (SPi h t x) = first ((h, t):) $ getParamsS x
getParamsS x = ([], x)

pattern AppsS :: SExp' a -> [(Visibility, SExp' a)] -> SExp' a
pattern AppsS f args  <- (getApps -> (f, args))
  where AppsS = foldl $ \a (v, b) -> SApp v a b

getApps = second reverse . run where
  run (SApp h a b) = second ((h, b):) $ run a
  run x = (x, [])

-- todo: remove
downToS err n m = [sVar (err ++ "_" ++ show i) (n + i) | i <- [m-1, m-2..0]]

instance SourceInfo (SExp' a) where
    sourceInfo = \case
        SGlobal sn        -> sourceInfo sn
        SBind_ si _ _ _ _ -> si
        SApp_ si _ _ _    -> si
        SLet_ si _ _ _    -> si
        SVar sn _         -> sourceInfo sn
        SLit si _         -> si
        STyped _          -> mempty

instance SetSourceInfo SExp where
    setSI si = \case
        SBind_ _ a b c d -> SBind_ si a b c d
        SApp_ _ a b c    -> SApp_ si a b c
        SLet_ _ le a b   -> SLet_ si le a b
        SVar sn i        -> SVar (setSI si sn) i
        SGlobal sn       -> SGlobal (setSI si sn)
        SLit _ l         -> SLit si l
        STyped v         -> elimVoid v

-------------------------------------------------------------------------------- low-level toolbox

class Up a where
    up_ :: Int -> Int -> a -> a
    up_ n i = iterateN n $ up1_ i
    up1_ :: Int -> a -> a
    up1_ = up_ 1

    foldVar :: Monoid e => (Int{-level-} -> Int{-index-} -> e) -> Int -> a -> e

    usedVar :: Int -> a -> Bool
    usedVar = (getAny .) . foldVar ((Any .) . (==))

    closedExp :: a -> a
    closedExp a = a

instance (Up a, Up b) => Up (a, b) where
    up_ n i (a, b) = (up_ n i a, up_ n i b)
    usedVar i (a, b) = usedVar i a || usedVar i b
    foldVar f i (a, b) = foldVar f i a <> foldVar f i b
    closedExp (a, b) = (closedExp a, closedExp b)

instance Up a => Up [a] where
    up_ i k = map (up_ i k)

up n = up_ n 0
up1 = up1_ 0

foldS
    :: Monoid m
    => (Int -> t -> m)
    -> (SIName -> Int -> m)
    -> (SIName -> Int -> Int -> m)
    -> Int
    -> SExp' t
    -> m
foldS h g f = fs
  where
    fs i = \case
        SApp _ a b -> fs i a <> fs i b
        SLet _ a b -> fs i a <> fs (i+1) b
        SBind_ _ _ _ a b -> fs i a <> fs (i+1) b
        SVar sn j -> f sn j i
        SGlobal sn -> g sn i
        x@SLit{} -> mempty
        STyped x -> h i x

foldName f = foldS (\_ -> elimVoid) (\sn _ -> f sn) mempty 0

usedS :: SIName -> SExp -> Bool
usedS n = getAny . foldName (Any . (== n))

mapS
    :: (Int -> a -> SExp' a)
    -> (SIName -> Int -> SExp' a)
    -> (SIName -> Int -> Int{-level-} -> SExp' a)
    -> Int
    -> SExp' a
    -> SExp' a
mapS hh gg f2 = g where
    g i = \case
        SApp_ si v a b -> SApp_ si v (g i a) (g i b)
        SLet_ si x a b -> SLet_ si x (g i a) (g (i+1) b)
        SBind_ si k si' a b -> SBind_ si k si' (g i a) (g (i+1) b)
        SVar sn j -> f2 sn j i
        SGlobal sn -> gg sn i
        STyped x -> hh i x
        x@SLit{} -> x

instance Up Void where
    up_ _ _ = elimVoid
    foldVar _ _ = elimVoid

instance Up a => Up (SExp' a) where
    up_ n = mapS (\i x -> STyped $ up_ n i x) (const . SGlobal) (\sn j i -> SVar sn $ if j < i then j else j+n)
    foldVar f = foldS (foldVar f) mempty $ \sn j i -> f j i

-- rearrange free variables
-- up_ n k == rearrange k (+n)
class Rearrange a where
    rearrange :: Int -> (Int -> Int) -> a -> a

rSubst :: Rearrange a => Int -> Int -> a -> a
rSubst i j = rearrange 0 $ \k -> if k == i then j else if k > i then k - 1 else k

rUp :: Rearrange a => Int -> Int -> a -> a
rUp n l = rearrange l $ \k -> if k >= 0 then k + n else k

instance Rearrange a => Rearrange [a] where
    rearrange l f = map $ rearrange l f

instance (Rearrange a, Rearrange b) => Rearrange (Either a b) where
    rearrange l f = rearrange l f +++ rearrange l f

instance (Rearrange a, Rearrange b) => Rearrange (a, b) where
    rearrange l f = rearrange l f *** rearrange l f

instance Rearrange SExp where
    rearrange i f = mapS (\_ -> elimVoid) (const . SGlobal) (\sn j i -> SVar sn $ if j < i then j else i + f (j - i)) i

-- replace names with de bruijn indices
class DeBruijnify a where
    deBruijnify_ :: Int -> [SIName] -> a -> a

deBruijnify = deBruijnify_ 0

instance (DeBruijnify a, DeBruijnify b) => DeBruijnify (a, b) where
    deBruijnify_ k ns = deBruijnify_ k ns *** deBruijnify_ k ns

instance (DeBruijnify a, DeBruijnify b) => DeBruijnify (Either a b) where
    deBruijnify_ k ns = deBruijnify_ k ns +++ deBruijnify_ k ns

instance (DeBruijnify a) => DeBruijnify [a] where
    deBruijnify_ k ns = fmap (deBruijnify_ k ns)

instance DeBruijnify SExp where
    deBruijnify_ j xs
        = mapS (\_ -> elimVoid) (\sn x -> maybe (SGlobal sn) (\i -> SVar sn $ i + x) $ elemIndex sn xs)
                                (\sn j k -> SVar sn $ if j >= k then j + l else j) j
      where
        l = length xs

trSExp :: (a -> b) -> SExp' a -> SExp' b
trSExp f = g where
    g = \case
        SApp_ si v a b -> SApp_ si v (g a) (g b)
        SLet_ si x a b -> SLet_ si x (g a) (g b)
        SBind_ si k si' a b -> SBind_ si k si' (g a) (g b)
        SVar sn j -> SVar sn j
        SGlobal sn -> SGlobal sn
        SLit si l -> SLit si l
        STyped a -> STyped $ f a

trSExp' :: SExp -> SExp' a
trSExp' = trSExp elimVoid

-------------------------------------------------------------------------------- statements

data Stmt
    = Let SIName (Maybe SExp) SExp
    | Data SIName [(Visibility, SExp)]{-parameters-} SExp{-type-} [(SIName, SExp)]{-constructor names and types-}
    | PrecDef SIName Fixity
    deriving (Show)

pattern Primitive n t <- Let n (Just t) (SBuiltin "undefined") where Primitive n t = Let n (Just t) $ SBuiltin "undefined"

instance PShow Stmt where
    pShowPrec p = \case
        Let n ty e -> text (sName n) </> "=" <+> maybe (pShow e) (\ty -> pShow e </> "::" <+> pShow ty) ty 
        Data n ps ty cs -> "data" <+> text (sName n)
        PrecDef n i -> "precedence" <+> text (sName n) <+> text (show i)

instance DeBruijnify Stmt where
    deBruijnify_ k v = \case
        Let sn mt e -> Let sn (deBruijnify_ k v <$> mt) (deBruijnify_ k v e)
        x -> error $ "deBruijnify @ " ++ show x

-------------------------------------------------------------------------------- declaration desugaring

data StmtNode = StmtNode
    { snId          :: !Int
    , snValue       :: Stmt
    , snChildren    :: [StmtNode]
    , snRevChildren :: [StmtNode]
    }

sortDefs :: [Stmt] -> [Stmt]
sortDefs xs = concatMap (desugarMutual . map snValue) $ scc snId snChildren snRevChildren nodes
  where
    nodes = zipWith mkNode [0..] xs
      where
        mkNode i s = StmtNode i s (nubBy ((==) `on` snId) $ catMaybes $ (`Map.lookup` defMap) <$> need)
                                  (fromMaybe [] $ IM.lookup i revMap)
          where
            need = Set.toList $ case s of
                PrecDef{} -> mempty
                Let _ mt e -> foldMap names mt <> names e
                Data _ ps t cs -> foldMap (names . snd) ps <> names t <> foldMap (names . snd) cs

            names = foldName Set.singleton

    revMap = IM.unionsWith (++) [IM.singleton (snId c) [n] | n <- nodes, c <- snChildren n]

    defMap = Map.fromList [(s, n) | n <- nodes, s <- def $ snValue n]
      where
        def = \case
            PrecDef{} -> mempty
            Let n _ _ -> [n]
            Data n _ _ cs -> n: map fst cs

desugarMutual [x] = [x]
desugarMutual xs = xs

-------------------------------------------------------------------------------- modules

data Module_ a = Module
    { extensions    :: Extensions
    , moduleImports :: [(SIName, ImportItems)]
    , moduleExports :: Maybe [Export]
    , definitions   :: a
    }

data Export = ExportModule SIName | ExportId SIName

data ImportItems
    = ImportAllBut [SIName]
    | ImportJust [SIName]

type Extensions = [Extension]

data Extension
    = NoImplicitPrelude
    | TraceTypeCheck
    deriving (Enum, Eq, Ord, Show)

extensionMap :: Map.Map String Extension
extensionMap = Map.fromList $ map (show &&& id) [toEnum 0 .. ]

-------------------------------------------------------------------------------- builtin precedences

data Prec
    = PrecAtom      --  ( _ )  ...
    | PrecAtom'
    | PrecAt        --  _@_                 {assoc}  -- in patterns
    | PrecProj      --  _ ._                {left}
    | PrecSwiz      --  _%_                 {left}
    | PrecApp       --  _ _                 {left}
    | PrecOp
    | PrecArr       --  _ -> _              {right}
    | PrecEq        --  _ ~ _
    | PrecAnn       --  _ :: _              {right}
    | PrecLet       --  _ := _
    | PrecLam       --  \ _ -> _            {right} {accum}
    deriving (Eq, Ord)

instance Up a => PShow (SExp' a) where
    pShowPrec _ = showDoc_ . sExpDoc

type Doc = NameDB PrecString

-- name De Bruijn indices
type NameDB a = StateT [String] (Reader [String]) a

showDoc :: Doc -> String
showDoc = str . flip runReader [] . flip evalStateT (flip (:) <$> iterate ('\'':) "" <*> ['a'..'z'])

showDoc_ :: Doc -> Parser.Doc
showDoc_ = text . str . flip runReader [] . flip evalStateT (flip (:) <$> iterate ('\'':) "" <*> ['a'..'z'])

sExpDoc :: Up a => SExp' a -> Doc
sExpDoc = \case
    SGlobal ns      -> pure $ shAtom $ sName ns
    SAnn a b        -> shAnn ":" False <$> sExpDoc a <*> sExpDoc b
    TyType a        -> shApp Visible (shAtom "tyType") <$> sExpDoc a
    SApp h a b      -> shApp h <$> sExpDoc a <*> sExpDoc b
    Wildcard t      -> shAnn ":" True (shAtom "_") <$> sExpDoc t
    SBind_ _ h _ a b -> join $ shLam (usedVar 0 b) h <$> sExpDoc a <*> pure (sExpDoc b)
    SLet _ a b      -> shLet_ (sExpDoc a) (sExpDoc b)
    STyped _{-(e,t)-}  -> pure $ shAtom "<<>>" -- todo: expDoc e
    SVar _ i        -> shAtom <$> shVar i
    SLit _ l        -> pure $ shAtom $ show l

shVar i = asks lookupVarName where
    lookupVarName xs | i < length xs && i >= 0 = xs !! i
    lookupVarName _ = "V" ++ show i

newName = gets head <* modify tail

shLet i a b = shAtom <$> shVar i >>= \i' -> local (dropNth i) $ shLam' <$> (cpar . shLet' (fmap inBlue i') <$> a) <*> b
shLet_ a b = newName >>= \i -> shLam' <$> (cpar . shLet' (shAtom i) <$> a) <*> local (i:) b
shLam usedVar h a b = newName >>= \i ->
    let lam = case h of
            BPi _ -> shArr
            _ -> shLam'
        p = case h of
            BMeta -> cpar . shAnn ":" True (shAtom $ inBlue i)
            BLam h -> vpar h
            BPi h -> vpar h
        vpar Hidden = brace . shAnn ":" True (shAtom $ inGreen i)
        vpar Visible = ann (shAtom $ inGreen i)
        ann | usedVar = shAnn ":" False
            | otherwise = const id
    in lam (p a) <$> local (i:) b

-----------------------------------------

data PS a = PS Prec a deriving (Functor)
type PrecString = PS String

getPrec (PS p _) = p
prec i s = PS i (s i)
str (PS _ s) = s

lpar, rpar :: PrecString -> Prec -> String
lpar (PS i s) j = par (i >. j) s  where
    PrecLam >. i = i > PrecAtom'
    i >. PrecLam = i >= PrecArr
    PrecApp >. PrecApp = False
    i >. j  = i >= j
rpar (PS i s) j = par (i >. j) s where
    PrecLam >. PrecLam = False
    PrecLam >. i = i > PrecAtom'
    PrecArr >. PrecArr = False
    PrecAnn >. PrecAnn = False
    i >. j  = i >= j

par True s = "(" ++ s ++ ")"
par False s = s

isAtom = (==PrecAtom) . getPrec
isAtom' = (<=PrecAtom') . getPrec

shAtom = PS PrecAtom
shAtom' = PS PrecAtom'
shTuple xs = prec PrecAtom $ \_ -> case xs of
    [x] -> "((" ++ str x ++ "))"
    xs -> "(" ++ intercalate ", " (map str xs) ++ ")"
shAnn _ True x y | str y `elem` ["Type", inGreen "Type"] = x
shAnn s simp x y | isAtom x && isAtom y = shAtom' $ str x <> s <> str y
shAnn s simp x y = prec PrecAnn $ lpar x <> " " <> const s <> " " <> rpar y
shApp Hidden x y = prec PrecApp $ lpar x <> " " <> const (str $ brace y)
shApp h x y = prec PrecApp $ lpar x <> " " <> rpar y
shArr x y | isAtom x && isAtom y = shAtom' $ str x <> "->" <> str y
shArr x y = prec PrecArr $ lpar x <> " -> " <> rpar y
shCstr x y | isAtom x && isAtom y = shAtom' $ str x <> "~" <> str y
shCstr x y = prec PrecEq $ lpar x <> " ~ " <> rpar y
shLet' x y | isAtom x && isAtom y = shAtom' $ str x <> ":=" <> str y
shLet' x y = prec PrecLet $ lpar x <> " := " <> rpar y
shLam' x y | PrecLam <- getPrec y = prec PrecLam $ "\\" <> lpar x <> " " <> pure (dropC $ str y)
  where
    dropC (ESC s (dropC -> x)) = ESC s x
    dropC (x: xs) = xs
shLam' x y | isAtom x && isAtom y = shAtom' $ "\\" <> str x <> "->" <> str y
shLam' x y = prec PrecLam $ "\\" <> lpar x <> " -> " <> rpar y
brace s = shAtom $ "{" <> str s <> "}"
cpar s | isAtom' s = s      -- TODO: replace with lpar, rpar
cpar s = shAtom $ par True $ str s
epar = fmap underlined

instance IsString (Prec -> String) where fromString = const

