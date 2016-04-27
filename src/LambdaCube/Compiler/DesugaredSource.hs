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
module LambdaCube.Compiler.DesugaredSource where

import Data.Monoid
import Data.Maybe
import Data.Char
import Data.List
import Data.Function
import Data.Bits
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMap as IM
import Control.Monad.Reader
import Control.Monad.State
import Control.Arrow hiding ((<+>))
import Control.DeepSeq

import LambdaCube.Compiler.Utils
import LambdaCube.Compiler.DeBruijn
import LambdaCube.Compiler.Pretty --hiding (braces, parens)

-------------------------------------------------------------------------------- simple name

type SName = String

pattern Ticked :: SName -> SName
pattern Ticked s = '\'': s

switchTick :: SName -> SName
switchTick (Ticked n) = n
switchTick n = Ticked n

-- TODO
--pattern CaseName :: SName -> SName
--pattern CaseName cs <- 'c':'a':'s':'e':cs where CaseName (c:cs) = "case" ++ cs
pattern CaseName :: SName -> SName
pattern CaseName cs <- (getCaseName -> Just cs) where CaseName (c:cs) = toLower c: cs ++ "Case"

getCaseName cs = case splitAt 4 $ reverse cs of
    (reverse -> "Case", xs) -> Just $ reverse xs
    _ -> Nothing

pattern MatchName :: SName -> SName
pattern MatchName cs <- 'm':'a':'t':'c':'h':cs where MatchName cs = "match" ++ cs


-------------------------------------------------------------------------------- fixity

data FixityDir = Infix | InfixL | InfixR
    deriving (Eq, Show)

data Fixity = Fixity !FixityDir !Int
    deriving (Eq, Show)

-------------------------------------------------------------------------------- file position

-- source position without file name
data SPos = SPos
    { row    :: !Int    -- 1, 2, 3, ...
    , column :: !Int    -- 1, 2, 3, ...
    }
  deriving (Eq, Ord)

instance PShow SPos where
    pShowPrec _ (SPos r c) = pShow r <> ":" <> pShow c

-------------------------------------------------------------------------------- file info

data FileInfo = FileInfo
    { fileId      :: !Int
    , filePath    :: FilePath
    , fileContent :: String
    }

instance Eq FileInfo where (==) = (==) `on` fileId
instance Ord FileInfo where compare = compare `on` fileId

instance PShow FileInfo where pShowPrec _ = text . filePath
instance Show FileInfo where show = ppShow

showPos :: FileInfo -> SPos -> Doc
showPos n p = pShow n <> ":" <> pShow p

-------------------------------------------------------------------------------- range

data Range = Range !FileInfo !SPos !SPos
    deriving (Eq, Ord)

instance NFData Range where
    rnf Range{} = ()

-- short version
instance PShow Range where pShowPrec _ (Range n b e) = pShow n <+> pShow b <> "-" <> pShow e
instance Show Range where show = ppShow

-- long version
showRange :: Range -> Doc
showRange (Range n p@(SPos r c) (SPos r' c')) = vcat
     $ (showPos n p <> ":")
     : map text (drop (r - 1) $ take r' $ lines $ fileContent n)
    ++ [text $ replicate (c - 1) ' ' ++ replicate (c' - c) '^' | r' == r]

joinRange :: Range -> Range -> Range
joinRange (Range n b e) (Range n' b' e') {- | n == n' -} = Range n (min b b') (max e e')

-------------------------------------------------------------------------------- source info

data SI
    = NoSI (Set.Set String) -- no source info, attached debug info
    | RangeSI Range

getRange (RangeSI r) = Just r
getRange _ = Nothing

instance NFData SI where
    rnf = \case
        NoSI x -> rnf x
        RangeSI r -> rnf r

instance Show SI where show _ = "SI"
instance Eq SI where _ == _ = True
instance Ord SI where _ `compare` _ = EQ

instance Monoid SI where
    mempty = NoSI Set.empty
    mappend (RangeSI r1) (RangeSI r2) = RangeSI (joinRange r1 r2)
    mappend (NoSI ds1) (NoSI ds2) = NoSI  (ds1 `Set.union` ds2)
    mappend r@RangeSI{} _ = r
    mappend _ r@RangeSI{} = r

instance PShow SI where
    pShowPrec _ (NoSI ds) = hsep $ map text $ Set.toList ds
    pShowPrec _ (RangeSI r) = pShow r

-- long version
showSI x = case sourceInfo x of
    RangeSI r -> show $ showRange r
    x -> ppShow x

hashPos :: FileInfo -> SPos -> Int
hashPos fn (SPos r c) = fileId fn `shiftL` 32 .|. r `shiftL` 16 .|. c

debugSI a = NoSI (Set.singleton a)

si@(RangeSI r) `validate` xs | r `notElem` [r | RangeSI r <- xs]  = si
_ `validate` _ = mempty

data SIName = SIName_ SI (Maybe Fixity) SName

pattern SIName si n <- SIName_ si _ n
  where SIName si n =  SIName_ si Nothing n

instance Eq SIName where (==) = (==) `on` sName
instance Ord SIName where compare = compare `on` sName
instance Show SIName where show = sName
instance PShow SIName where pShowPrec _ = text . sName

sName (SIName _ s) = s

--appName f (SIName si n) = SIName si $ f n

getFixity (SIName_ _ f _) = fromMaybe (Fixity InfixL 9) f

-------------

class SourceInfo a where
    sourceInfo :: a -> SI

instance SourceInfo SI where
    sourceInfo = id

instance SourceInfo SIName where
    sourceInfo (SIName si _) = si

instance SourceInfo si => SourceInfo [si] where
    sourceInfo = foldMap sourceInfo

class SetSourceInfo a where
    setSI :: SI -> a -> a

instance SetSourceInfo SIName where
    setSI si (SIName_ _ f s) = SIName_ si f s

-------------------------------------------------------------------------------- literal

data Lit
    = LInt    Integer
    | LChar   Char
    | LFloat  Double
    | LString String
  deriving (Eq)

instance Show Lit where
    show = \case
        LFloat x  -> show x
        LString x -> show x
        LInt x    -> show x
        LChar x   -> show x

-------------------------------------------------------------------------------- expression

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

instance Up a => Up (SExp' a) where
    foldVar f = foldS (foldVar f) mempty $ \sn j i -> f j i

instance Rearrange a => Rearrange (SExp' a) where
    rearrange i f = mapS (\i x -> STyped $ rearrange i f x) (const . SGlobal) (\sn j i -> SVar sn $ if j < i then j else i + f (j - i)) i

instance DeBruijnify SIName SExp where
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

-------------------------------------------------------------------------------- statement

data Stmt
    = Let SIName (Maybe SExp) SExp
    | Data SIName [(Visibility, SExp)]{-parameters-} SExp{-type-} [(SIName, SExp)]{-constructor names and types-}
    | PrecDef SIName Fixity
    deriving (Show)

pattern Primitive n t = Let n (Just t) (SBuiltin "undefined")

instance PShow Stmt where
    pShowPrec p = \case
        Let n ty e -> text (sName n) </> "=" <+> maybe (pShow e) (\ty -> pShow e </> "::" <+> pShow ty) ty 
        Data n ps ty cs -> "data" <+> text (sName n)
        PrecDef n i -> "precedence" <+> text (sName n) <+> text (show i)

instance DeBruijnify SIName Stmt where
    deBruijnify_ k v = \case
        Let sn mt e -> Let sn (deBruijnify_ k v <$> mt) (deBruijnify_ k v e)
        x -> error $ "deBruijnify @ " ++ show x

-------------------------------------------------------------------------------- statement with dependencies

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

-------------------------------------------------------------------------------- module

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

-------------------------------------------------------------------------------- pretty print

data NDoc
    = DAtom String
    | DOp Fixity NDoc String NDoc
    | DPar String NDoc String
    | DLam String [NDoc] String NDoc
    | DVar Int
    | DFreshName Bool{-False: dummy-} NDoc
    | DUp Int NDoc
    | DColor Color NDoc
    -- add wl-pprint combinators as necessary here
    deriving (Eq)

pattern DParen x = DPar "(" x ")"
pattern DBrace x = DPar "{" x "}"
pattern DArr x y = DOp (Fixity InfixR (-1)) x "->" y
pattern DAnn x y = DOp (Fixity InfixR (-3)) x ":" y

data Color = Green | Blue | Underlined
    deriving (Eq)

inGreen' = DColor Green
inBlue' = DColor Blue
epar = DColor Underlined

strip = \case
    DColor _ x -> strip x
    DUp _ x -> strip x
    DFreshName _ x -> strip x
    x -> x

simple x = case strip x of
    DAtom{} -> True
    DVar{} -> True
    DPar{} -> True
    _ -> False

renderDocX :: NDoc -> Doc
renderDocX = render . addPar (-10) . flip runReader [] . flip evalStateT (flip (:) <$> iterate ('\'':) "" <*> ['a'..'z']) . showVars
  where
    showVars x = case x of
        DAtom s -> pure x
        DColor c x -> DColor c <$> showVars x
        DPar l x r -> DPar l <$> showVars x <*> pure r
        DOp pr x s y -> DOp pr <$> showVars x <*> pure s <*> showVars y
        DVar i -> asks $ DAtom . lookupVarName i
        -- hack, remove
        DFreshName True (DArr (DAnn a (DUp 0 b)) y) -> do
            b' <- showVars b
            newName $ showVars $ DArr (DAnn a b') y
        -- hack, remove
        DFreshName True (DArr (DUp 0 b) y) -> do
            b' <- showVars b
            newName $ showVars $ DArr b' y
        DFreshName True x -> newName $ showVars x
        DFreshName False x -> local ("?":) $ showVars x
        DUp i x -> local (dropNth i) $ showVars x
        DLam lam vs arr e -> DLam lam <$> (mapM showVars vs) <*> pure arr <*> showVars e
      where
        lookupVarName i xs | i < length xs && i >= 0 = xs !! i
        lookupVarName i _ = "V" ++ show i -- TODO: better names here

    addPar :: Int -> NDoc -> NDoc
    addPar pr x = case x of
        DColor c x -> DColor c $ addPar pr x
        DAtom{} -> x
        DPar l x r -> DPar l (addPar (-20) x) r
        DOp pr' x s y -> (if simple x' && simple y' && s `notElem` ["", ","] then id else paren) $ DOp pr' x' s y'
          where
            x' = addPar (precL pr') x
            y' = addPar (precR pr') y
        DLam lam vs arr e -> paren $ DLam lam (addPar 10 <$> vs) arr (addPar (-10) e)
      where
        paren d
            | protect x = DParen d
            | otherwise = d
          where
            protect x = case x of
                DAtom{} -> False
                DPar{} -> False
                DOp (Fixity _ pr') _ _ _ -> pr' < pr
                DLam{} -> -10 < pr 
                DColor _ x     -> protect x

        precL (Fixity Infix  i) = i+1
        precL (Fixity InfixL i) = i
        precL (Fixity InfixR i) = i+1
        precR (Fixity Infix  i) = i+1
        precR (Fixity InfixL i) = i+1
        precR (Fixity InfixR i) = i

    render x = case x of
        DColor Green x -> text $ inGreen $ show $ render x -- TODO
        DColor Blue x -> text $ inBlue $ show $ render x -- TODO
        DColor Underlined x -> text $ underlined $ show $ render x -- TODO
        DAtom s -> text s
        DPar l x r -> text l <> render x <> text r
        DOp _ x s y -> case s of
            "" -> render x <+> render y
            _ | simple x && simple y && s /= "," -> render x <> text s <> render y
              | otherwise -> (render x <++> s) <+> render y
        DLam lam vs arr e -> text lam <> hsep (render <$> vs) <+> text arr <+> render e
      where
        x <++> "," = x <> text ","
        x <++> s = x <+> text s
        
instance Up a => PShow (SExp' a) where
    pShowPrec _ = showDoc_ . sExpDoc

-- name De Bruijn indices
type NameDB a = StateT [String] (Reader [String]) a

showDoc :: NDoc -> String
showDoc = show . renderDocX

showDoc_ :: NDoc -> Doc
showDoc_ = renderDocX

sExpDoc :: Up a => SExp' a -> NDoc
sExpDoc = \case
    SGlobal ns      -> shAtom $ sName ns
    SAnn a b        -> shAnn ":" False (sExpDoc a) (sExpDoc b)
    TyType a        -> shApp Visible (shAtom "tyType") (sExpDoc a)
    SApp h a b      -> shApp h (sExpDoc a) (sExpDoc b)
    Wildcard t      -> shAnn ":" True (shAtom "_") (sExpDoc t)
    SBind_ _ h _ a b -> shLam (usedVar 0 b) h (sExpDoc a) (sExpDoc b)
    SLet _ a b      -> shLet_ (sExpDoc a) (sExpDoc b)
    STyped _{-(e,t)-}  -> shAtom "<<>>" -- todo: expDoc e
    SVar _ i        -> shVar i
    SLit _ l        -> shAtom $ show l

shVar = DVar

newName p = gets head >>= \n -> modify tail >> local (n:) p

shLet i a b = shLam' (cpar . shLet' (inBlue' $ shVar i) $ DUp i a) (DUp i b)
shLet_ a b = DFreshName True $ shLam' (cpar . shLet' (shVar 0) $ DUp 0 a) b

shLam usedVar h a b = DFreshName True $ lam (p $ DUp 0 a) b
  where
    lam = case h of
        BPi{} -> shArr
        _ -> shLam'

    p = case h of
        BMeta -> cpar . shAnn ":" True (inBlue' $ DVar 0)
        BLam h -> vpar h
        BPi h -> vpar h

    vpar Hidden = (\p -> DBrace p) . shAnn ":" True (inGreen' $ DVar 0)
    vpar Visible = ann (inGreen' $ DVar 0)

    ann | usedVar = shAnn ":" False
        | otherwise = const id

-----------------------------------------

shAtom = DAtom

shTuple [] = DAtom "()"
shTuple [x] = DParen $ DParen x
shTuple xs = DParen $ foldr1 (\x y -> DOp (Fixity InfixR (-20)) x "," y) xs

shAnn _ True x y | strip y == DAtom "Type" = x
shAnn s _ x y = DOp (Fixity InfixR (-3)) x s y

shApp _ x y = DOp (Fixity InfixL 10) x "" y

shArr = DArr

shCstr x y = DOp (Fixity Infix (-2)) x "~" y

shLet' x y = DOp (Fixity Infix (-4)) x ":=" y

getFN (DFreshName True a) = first (+1) $ getFN a
getFN a = (0, a)

shLam' x (getFN -> (i, DLam "\\" xs "->" y)) = iterateN i (DFreshName True) $ DLam "\\" (iterateN i (DUp 0) x: xs) "->" y
shLam' x y = DLam "\\" [x] "->" y

cpar s | simple s = s
cpar s = DParen s


