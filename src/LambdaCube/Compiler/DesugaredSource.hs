{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric #-}
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
module LambdaCube.Compiler.DesugaredSource
    ( module LambdaCube.Compiler.DesugaredSource
    , Fixity(..)
    )where

import System.IO.Unsafe
import Text.Printf
import qualified Data.ByteString.Char8 as BS

import Data.Binary
import GHC.Generics (Generic)
import qualified System.FilePath.Posix as FilePath

--import Data.Text (Text)
import Data.Monoid
import Data.Maybe
import Data.List
import Data.Function
import Data.Bits
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Arrow hiding ((<+>))

import LambdaCube.Compiler.Utils
import LambdaCube.Compiler.DeBruijn
import LambdaCube.Compiler.Pretty --hiding (braces, parens)

import Paths_lambdacube_compiler (getDataDir)

-------------------------------------------------------------------------------- simple name

-- TODO: move to Text
type SName = String

pattern Ticked :: SName -> SName
pattern Ticked s = '\'': s

untick :: SName -> SName
untick (Ticked s) = s
untick s = s

switchTick :: SName -> SName
switchTick (Ticked n) = n
switchTick n = Ticked n

pattern CaseName :: SName -> SName
pattern CaseName cs <- 'c':'a':'s':'e':cs where CaseName cs = "case" ++ cs

pattern MatchName :: SName -> SName
pattern MatchName cs <- 'm':'a':'t':'c':'h':cs where MatchName cs = "match" ++ cs

-------------------------------------------------------------------------------- file position

-- source position without file name
newtype SPos = SPos_ Int
  deriving (Eq, Ord, Generic)

instance Binary SPos

row :: SPos -> Int
row (SPos_ i) = i `shiftR` 16

column :: SPos -> Int
column (SPos_ i) = i .&. 0xffff

pattern SPos :: Int -> Int -> SPos
pattern SPos a b <- ((row &&& column) -> (a, b))
  where SPos a b =  SPos_ $ (a `shiftL` 16) .|. b

instance PShow SPos where
    pShow (SPos r c) = pShow r <> ":" <> pShow c

-------------------------------------------------------------------------------- file info

data FileInfo = FileInfo
    { fileId      :: !Int
    , filePath    :: FilePath
    , fileModule  :: String   -- module name
    }
    deriving Generic

instance Binary FileInfo

fileContent :: FileInfo -> String
fileContent fi = unsafePerformIO $ do
  let fname = filePath fi
  --BS.putStrLn $ BS.pack $ printf "load source %s" fname
  readFile fname

instance Eq FileInfo where (==) = (==) `on` fileId
instance Ord FileInfo where compare = compare `on` fileId

instance PShow FileInfo where
  pShow fi = let path = filePath fi
             in text $ if isPrefixOf lcPreludePath path
                        then "<<installed-prelude-path>>" ++ drop (length lcPreludePath) path
                        else path

lcPreludePath :: String
lcPreludePath = unsafePerformIO $ (FilePath.</> "lc") <$> getDataDir

showPos :: FileInfo -> SPos -> Doc
showPos n p = pShow n <> ":" <> pShow p

-------------------------------------------------------------------------------- range

data Range = Range
    { rangeFile  :: !FileInfo
    , rangeStart :: !SPos
    , rangeStop  :: !SPos
    }
    deriving (Eq, Ord, Generic)

instance Binary Range

instance Show Range where show = ppShow
instance PShow Range
  where
    pShow (Range n b@(SPos r c) e@(SPos r' c')) = expand (pShow n <+> pShow b <> "-" <> pShow e)
      $ vcat $ (showPos n b <> ":")
             : map text (drop (r - 1) $ take r' $ lines $ fileContent n)
            ++ [text $ replicate (c - 1) ' ' ++ replicate (c' - c) '^' | r' == r]

showRangeWithoutFileName :: Range -> Doc
showRangeWithoutFileName (Range _ b e) = pShow b <> "-" <> pShow e

joinRange :: Range -> Range -> Range
joinRange (Range n b e) (Range n' b' e') = Range n (min b b') (max e e')
-- TODO: check (n == n') ?

-------------------------------------------------------------------------------- source info

data SI
    = NoSI (Set.Set String) -- no source info, attached debug info
    | RangeSI Range
    deriving Generic

instance Binary SI

getRange :: SI -> Maybe Range
getRange (RangeSI r) = Just r
getRange _ = Nothing

--instance Show SI where show _ = "SI"
instance Eq SI where _ == _ = True
instance Ord SI where _ `compare` _ = EQ

instance Monoid SI where
    mempty = NoSI Set.empty
#if !MIN_VERSION_base(4,11,0)
    mappend (RangeSI r1) (RangeSI r2) = RangeSI (joinRange r1 r2)
    mappend (NoSI ds1) (NoSI ds2) = NoSI  (ds1 `Set.union` ds2)
    mappend r@RangeSI{} _ = r
    mappend _ r@RangeSI{} = r
#else
instance Semigroup SI where
    (<>) (RangeSI r1) (RangeSI r2) = RangeSI (joinRange r1 r2)
    (<>) (NoSI ds1) (NoSI ds2) = NoSI  (ds1 `Set.union` ds2)
    (<>) r@RangeSI{} _ = r
    (<>) _ r@RangeSI{} = r
#endif

instance PShow SI where
    pShow (NoSI ds) = hsep $ map text $ Set.toList ds
    pShow (RangeSI r) = pShow r

hashPos :: FileInfo -> SPos -> Int
hashPos fn (SPos_ p) = (1 + fileId fn) `shiftL` 32 .|. p

debugSI :: String -> SI
debugSI a = NoSI (Set.singleton a)

validate :: SI -> [SI] -> SI
si@(RangeSI r) `validate` xs | r `notElem` [r | RangeSI r <- xs]  = si
_ `validate` _ = mempty

-------------------------------------------------------------------------------- type classes for source info

class SourceInfo a where
    sourceInfo :: a -> SI

instance SourceInfo SI where
    sourceInfo = id

instance SourceInfo si => SourceInfo [si] where
    sourceInfo = foldMap sourceInfo

class SetSourceInfo a where
    setSI :: SI -> a -> a

-------------------------------------------------------------------------------- name with source info

data SIName = SIName__ { nameHash :: Int, nameSI :: SI, nameFixity :: Maybe Fixity, sName :: SName }
    deriving Generic

instance Binary SIName

pattern SIName_ :: SI -> Maybe Fixity -> SName -> SIName
pattern SIName_ si f n <- SIName__ _ si f n
  where SIName_ si f n =  SIName__ (fnameHash si n) si f n

pattern SIName :: SI -> SName -> SIName
pattern SIName si n <- SIName_ si _ n
  where SIName si n =  SIName_ si Nothing n

instance Eq SIName where (==) = (==) `on` sName
instance Ord SIName where compare = compare `on` sName
instance Show SIName where show = sName
instance PShow SIName
  where
    pShow (SIName_ si f n) = expand (if isOpName n then DOp0 n (defaultFixity f) else maybe (text n) (DOp0 n) f) $ case si of
        NoSI{} -> text n --maybe (text n) (DOp0 n) f
        _ -> pShow si

instance SourceInfo SIName where
    sourceInfo (SIName si _) = si

instance SetSourceInfo SIName where
    setSI si (SIName_ _ f s) = SIName_ si f s

-------------------------------------------------------------------------------- hashed names

newtype FName = FName { fName :: SIName }
    deriving Generic

instance Binary FName

instance Eq    FName where (==) = (==) `on` nameHash . fName
instance Ord   FName where compare = compare `on` nameHash . fName
instance Show  FName where show = show . fName
instance PShow FName where pShow = pShow . fName

data FNameTag
    -- type constructors & constructors
    = F'Type
    | F'Empty
    | F'Unit        | FTT
    | F'Constraint  | FCUnit | FCEmpty
    | F'Nat         | FZero | FSucc
    | F'Bool        | FFalse | FTrue
    | F'Ordering    | FLT | FGT | FEQ
    | F'List        | FNil | FCons
    | F'HList       | FHCons | FHNil
    | F'VecS        | FV2 | FV3 | FV4
                    | FRecordCons
                    | FRecItem
                    | FSx | FSy | FSz | FSw
    | F'Int
    | F'Word
    | F'Float
    | F'String
    | F'Char
    | F'Output
    -- type functions
    | F'T2 | F'EqCT | F'CW | F'Split | F'VecScalar
    -- functions
    | Fcoe | FparEval | Ft2C | FprimFix
    | Fparens | FtypeAnn | Fundefined | Fotherwise | FprimIfThenElse | FfromTo | FconcatMap | FfromInt | Fproject | Fswizzscalar | Fswizzvector

    | FunsafeCoerce | FreflCstr | FhlistNilCase | FhlistConsCase
    | FprimAddInt | FprimSubInt | FprimModInt | FprimSqrtFloat | FprimRound | FprimIntToFloat | FprimIntToNat
    | FprimCompareInt | FprimCompareFloat | FprimCompareChar | FprimCompareString
    | FPrimGreaterThan | FPrimGreaterThanEqual | FPrimLessThan | FPrimLessThanEqual | FPrimEqualV | FPrimNotEqualV | FPrimEqual | FPrimNotEqual
    | FPrimSubS | FPrimSub | FPrimAddS | FPrimAdd | FPrimMulS | FPrimMul | FPrimDivS | FPrimDiv | FPrimModS | FPrimMod
    | FPrimNeg | FPrimAnd | FPrimOr | FPrimXor | FPrimNot

    -- other
    | F_rhs | F_section
    deriving (Eq, Ord, Show, Enum, Bounded, Generic)

instance Binary FNameTag

tagName :: FNameTag -> String
tagName FCons = ":"
tagName t = case show t of 'F': s -> s

pattern Tag :: FNameTag -> SIName
pattern Tag t <- (toTag . nameHash -> Just t)
  where Tag t =  SIName__ (fromEnum t) (tagSI t) (tagFixity t) (tagName t)

pattern FTag :: FNameTag -> FName
pattern FTag t = FName (Tag t)

toTag :: Int -> Maybe FNameTag
toTag i
    | i <= fromEnum (maxBound :: FNameTag) = Just (toEnum i)
    | otherwise = Nothing

tagFixity :: FNameTag -> Maybe Fixity
tagFixity FCons = Just $ InfixR 5
tagFixity _ = Nothing

tagSI :: FNameTag -> SI
tagSI t = NoSI $ Set.singleton $ tagName t

fnameHash :: SI -> SName -> Int
fnameHash (RangeSI (Range fn p _)) s = maybe (hashPos fn p) fromEnum $ Map.lookup s fntable
fnameHash _ s = 0xffff -- TODO error $ "mkFName: " ++ show s

fntable :: Map.Map String FNameTag
fntable = Map.fromList $ (tagName &&& id) <$> [minBound ..]

-------------------------------------------------------------------------------- literal

data Lit
    = LInt    Integer
    | LChar   Char
    | LFloat  Double
    | LString String
  deriving (Eq, Generic)

instance Binary Lit

instance PShow Lit where
    pShow = \case
        LFloat x  -> pShow x
        LString x -> text $ show x
        LInt x    -> pShow x
        LChar x   -> pShow x

-------------------------------------------------------------------------------- expression

data SExp' a
    = SLit    SI Lit
    | SGlobal SIName
    | SApp_   SI Visibility (SExp' a) (SExp' a)
    | SBind_  SI Binder (SData SIName){-parameter name-} (SExp' a) (SExp' a)
    | SVar_   (SData SIName) !Int
    | SLet_   SI (SData SIName) (SExp' a) (SExp' a)    -- let x = e in f   -->  SLet e f{-x is Var 0-}
    | SLHS    SIName (SExp' a)
    | STyped  a
  deriving (Eq, Generic)

instance Binary SExp

sLHS :: SIName -> SExp' a -> SExp' a
sLHS _ (SRHS x) = x
sLHS n x = SLHS n x

type SExp = SExp' Void

data Binder
    = BPi  Visibility
    | BLam Visibility
    | BMeta      -- a metavariable is like a floating hidden lambda
  deriving (Eq, Generic)

instance Binary Binder

instance PShow Binder where
    pShow = \case
        BPi v -> "BPi" `DApp` pShow v
        BLam v -> "BLam" `DApp` pShow v
        BMeta -> "BMeta"

data Visibility = Hidden | Visible
  deriving (Eq, Generic)

instance Binary Visibility

instance PShow Visibility where
    pShow = \case
        Hidden -> "Hidden"
        Visible -> "Visible"

dummyName :: String -> SIName
dummyName s = SIName (debugSI s) "" --("v_" ++ s)

dummyName' :: String -> SData SIName
dummyName' = SData . dummyName

sVar :: String -> Int -> SExp' a
sVar = SVar . dummyName

pattern SBind :: Binder -> SData SIName -> SExp' a -> SExp' a -> SExp' a
pattern SBind v x a b <- SBind_ _ v x a b
  where SBind v x a b =  SBind_ (sourceInfo a <> sourceInfo b) v x a b

pattern SPi :: Visibility -> SExp' a -> SExp' a -> SExp' a
pattern SPi  h a b <- SBind (BPi  h) _ a b
  where SPi  h a b =  SBind (BPi  h) (dummyName' "SPi") a b

pattern SLam :: Visibility -> SExp' a -> SExp' a -> SExp' a
pattern SLam h a b <- SBind (BLam h) _ a b
  where SLam h a b =  SBind (BLam h) (dummyName' "SLam") a b

pattern Wildcard :: SExp' a -> SExp' a
pattern Wildcard t <- SBind BMeta _ t (SVar _ 0)
  where Wildcard t =  SBind BMeta (dummyName' "Wildcard") t (sVar "Wildcard2" 0)

pattern SLet :: SIName -> SExp' a -> SExp' a -> SExp' a
pattern SLet n a b <- SLet_ _ (SData n) a b
  where SLet n a b =  SLet_ (sourceInfo a <> sourceInfo b) (SData n) a b

pattern SLamV :: SExp' a -> SExp' a
pattern SLamV a  = SLam Visible (Wildcard SType) a

pattern SVar :: SIName -> Int -> SExp' a
pattern SVar a b = SVar_ (SData a) b

pattern SApp :: Visibility -> SExp' a -> SExp' a -> SExp' a
pattern SApp h a b <- SApp_ _ h a b
  where SApp h a b =  SApp_ (sourceInfo a <> sourceInfo b) h a b

pattern SAppH :: SExp' a -> SExp' a -> SExp' a
pattern SAppH a b    = SApp Hidden a b

pattern SAppV :: SExp' a -> SExp' a -> SExp' a
pattern SAppV a b    = SApp Visible a b

pattern SAppV2 :: SExp' a -> SExp' a -> SExp' a -> SExp' a
pattern SAppV2 f a b = f `SAppV` a `SAppV` b

infixl 2 `SAppV`, `SAppH`
------------------------------------------------------------------------------------------------- ****************************************
pattern SBuiltin :: FNameTag -> SExp' a
pattern SBuiltin s = SGlobal (Tag s)

pattern SRHS a      = SBuiltin F_rhs     `SAppV` a
pattern Section e   = SBuiltin F_section `SAppV` e
pattern SType       = SBuiltin F'Type
pattern SConstraint = SBuiltin F'Constraint
pattern Parens e    = SBuiltin Fparens   `SAppV` e
pattern SAnn a t    = SBuiltin FtypeAnn  `SAppH` t `SAppV` a
pattern SCW a       = SBuiltin F'CW      `SAppV` a

pattern TyType :: SExp' a -> SExp' a
pattern TyType a    = SAnn a SType

-- builtin heterogenous list
pattern HList a   = SBuiltin F'HList `SAppV` a
pattern HCons a b = SBuiltin FHCons  `SAppV` a `SAppV` b
pattern HNil      = SBuiltin FHNil

-- builtin list
pattern BList a   = SBuiltin F'List `SAppV` a
pattern BCons a b = SBuiltin FCons `SAppV` a `SAppV` b
pattern BNil      = SBuiltin FNil

getTTuple :: SExp' a -> [SExp' a]
getTTuple (HList (getList -> Just xs)) = xs
getTTuple x = [x]

getList :: SExp' a -> Maybe [SExp' a]
getList BNil = Just []
getList (BCons x (getList -> Just y)) = Just (x:y)
getList _ = Nothing

sLit :: Lit -> SExp' a
sLit = SLit mempty

isPi :: Binder -> Bool
isPi (BPi _) = True
isPi _ = False

pattern UncurryS :: [(Visibility, SExp' a)] -> SExp' a -> SExp' a
pattern UncurryS ps t <- (getParamsS -> (ps, t))
  where UncurryS ps t = foldr (uncurry SPi) t ps

getParamsS :: SExp' a -> ([(Visibility, SExp' a)], SExp' a)
getParamsS (SPi h t x) = first ((h, t):) $ getParamsS x
getParamsS x = ([], x)

pattern AppsS :: SExp' a -> [(Visibility, SExp' a)] -> SExp' a
pattern AppsS f args  <- (getApps -> (f, args))
  where AppsS = foldl $ \a (v, b) -> SApp v a b

getApps :: SExp' a -> (SExp' a, [(Visibility, SExp' a)])
getApps = second reverse . run where
  run (SApp h a b) = second ((h, b):) $ run a
  run x = (x, [])

-- todo: remove
downToS :: String -> Int -> Int -> [SExp' a]
downToS err n m = [sVar (err ++ "_" ++ show i) (n + i) | i <- [m-1, m-2..0]]

instance SourceInfo (SExp' a) where
    sourceInfo = \case
        SGlobal sn        -> sourceInfo sn
        SBind_ si _ _ _ _ -> si
        SApp_ si _ _ _    -> si
        SLet_ si _ _ _    -> si
        SVar sn _         -> sourceInfo sn
        SLit si _         -> si
        SLHS n x          -> sourceInfo x
        STyped _          -> mempty

instance SetSourceInfo SExp where
    setSI si = \case
        SBind_ _ a b c d -> SBind_ si a b c d
        SApp_ _ a b c    -> SApp_ si a b c
        SLet_ _ le a b   -> SLet_ si le a b
        SVar sn i        -> SVar (setSI si sn) i
        SGlobal sn       -> SGlobal (setSI si sn)
        SLit _ l         -> SLit si l
        SLHS n x         -> SLHS n $ setSI si x
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
        SLHS _ x -> fs i x
        STyped x -> h i x

foldName :: Monoid m => (SIName -> m) -> SExp' Void -> m
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
        SLHS n x -> SLHS n $ g i x
        STyped x -> hh i x
        x@SLit{} -> x

instance HasFreeVars a => HasFreeVars (SExp' a) where
    getFreeVars = foldS (\l x -> shiftFreeVars (-l) $ getFreeVars x) mempty (\sn i l -> if i >= l then freeVar $ i - l else mempty) 0

instance Rearrange a => Rearrange (SExp' a) where
    rearrange i f = mapS (\i x -> STyped $ rearrange i f x) (const . SGlobal) (\sn j i -> SVar sn $ if j < i then j else i + rearrangeFun f (j - i)) i

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
        SLHS n x -> SLHS n (g x)
        STyped a -> STyped $ f a

trSExp' :: SExp -> SExp' a
trSExp' = trSExp elimVoid

instance (HasFreeVars a, PShow a) => PShow (SExp' a) where
    pShow = \case
        SGlobal ns      -> pShow ns
        Parens x        -> pShow x     -- TODO: remove
        SAnn a b        -> shAnn (pShow a) (pShow b)
        TyType a        -> text "tyType" `DApp` pShow a
        SApp h a b      -> shApp h (pShow a) (pShow b)
        Wildcard SType  -> text "_"
        Wildcard t      -> shAnn (text "_") (pShow t)
        SBind_ _ h (SData n) SType b -> shLam_ (usedVar' 0 b $ sName n) h Nothing (pShow b)
        SBind_ _ h (SData n) a b -> shLam (usedVar' 0 b $ sName n) h (pShow a) (pShow b)
        SLet _ a b      -> shLet_ (pShow a) (pShow b)
        SLHS n x        -> "_lhs" `DApp` pShow n `DApp` pShow x
        STyped a        -> pShow a
        SVar _ i        -> shVar i
        SLit _ l        -> pShow l

shApp :: Visibility -> Doc -> Doc -> Doc
shApp Visible a b = DApp a b
shApp Hidden a b = DApp a (DAt b)

usedVar' :: HasFreeVars a => Int -> a -> x -> Maybe x
usedVar' a b s | usedVar a b = Just s
               | otherwise = Nothing

shLam :: Maybe String -> Binder -> Doc -> Doc -> Doc
shLam usedVar h a b = shLam_ usedVar h (Just a) b

simpleFo :: Doc -> Doc
simpleFo (DExpand x _) = x
simpleFo x = x

shLam_ :: Maybe String -> Binder -> Maybe Doc -> Doc -> Doc
shLam_ Nothing (BPi Hidden) (Just ((simpleFo -> DText "'CW") `DApp` a)) b = DFreshName Nothing $ showContext (DUp 0 a) b
  where
    showContext :: Doc -> Doc -> Doc
    showContext x (DFreshName u d) = DFreshName u $ showContext (DUp 0 x) d
    showContext x (DParContext xs y) = DParContext (DComma x xs) y
    showContext x (DContext xs y) = DParContext (DComma x xs) y
    showContext x y = DContext x y

shLam_ usedVar h a b = DFreshName usedVar $ lam (p $ DUp 0 <$> a) b
  where
    lam :: Doc -> Doc -> Doc
    lam = case h of
        BPi Visible
            | isJust usedVar   -> showForall "->"
            | otherwise -> shArr
        BPi Hidden
            | isJust usedVar   -> showForall "."
            | otherwise -> showContext
        _ -> showLam

    shAnn' :: Doc -> Maybe Doc -> Doc
    shAnn' a = maybe a (shAnn a)

    p :: Maybe Doc -> Doc
    p = case h of
        BMeta -> shAnn' (blue $ DVar 0)
        BLam Hidden -> DAt . shAnn' (DVar 0)
        BLam Visible -> shAnn' (DVar 0)
        _ -> ann

    ann :: Maybe Doc -> Doc
    ann | isJust usedVar = shAnn' (DVar 0)
        | otherwise = fromMaybe (text "Type")

    showForall :: String -> Doc -> Doc -> Doc
    showForall s x (DFreshName u d) = DFreshName u $ showForall s (DUp 0 x) d
    showForall s x (DForall s' xs y) | s == s' = DForall s (DSep (InfixR 11) x xs) y
    showForall s x y = DForall s x y

    showContext :: Doc -> Doc -> Doc
    showContext x y = DContext' x y

showLam :: Doc -> Doc -> Doc
showLam x (DFreshName u d) = DFreshName u $ showLam (DUp 0 x) d
showLam x (DLam xs y) = DLam (DSep (InfixR 11) x xs) y
showLam x y = DLam x y

shLet :: Int -> Doc -> Doc -> Doc
shLet i a b = DLet' (DLet "=" (blue $ shVar i) $ DUp i a) (DUp i b)

showLet :: Doc -> Doc -> Doc
showLet x (DFreshName u d) = DFreshName u $ showLet (DUp 0 x) d
showLet x (DLet' xs y) = DLet' (DSemi x xs) y
showLet x y = DLet' x y

shLet_ :: Doc -> Doc -> Doc
shLet_ a b = DFreshName (Just "") $ showLet (DLet "=" (shVar 0) $ DUp 0 a) b

-------------------------------------------------------------------------------- statement

data Stmt
    = StmtLet SIName SExp
    | Data SIName [(Visibility, SExp)]{-parameters-} SExp{-type-} [(SIName, SExp)]{-constructor names and types-}
    | PrecDef SIName Fixity
    deriving Generic

instance Binary Stmt

pattern StLet :: SIName -> Maybe (SExp' Void) -> SExp' Void -> Stmt
pattern StLet n mt x <- StmtLet n (getSAnn -> (x, mt))
  where StLet n mt x =  StmtLet n $ maybe x (SAnn x) mt

getSAnn :: SExp' a -> (SExp' a, Maybe (SExp' a))
getSAnn (SAnn x t) = (x, Just t)
getSAnn x = (x, Nothing)

pattern Primitive :: SIName -> SExp' Void -> Stmt
pattern Primitive n t = StLet n (Just t) (SBuiltin Fundefined)

instance PShow Stmt where
    pShow stmt = vcat . map DResetFreshNames $ case stmt of
        Primitive n t -> pure $ shAnn (pShow n) (pShow t)
        StLet n ty e -> [shAnn (pShow n) (pShow t) | Just t <- [ty]] ++ [DLet "=" (pShow n) (pShow e)]
        Data n ps ty cs -> pure $ nest 2 $ "data" <+> nest 2 (shAnn (foldl DApp (DTypeNamespace True $ pShow n) [shAnn (text "_") (pShow t) | (v, t) <- ps]) (pShow ty)) </> "where" <> nest 2 (hardline <> vcat [shAnn (pShow n) $ pShow $ UncurryS (first (const Hidden) <$> ps) t | (n, t) <- cs])
        PrecDef n i -> pure $ pShow i <+> text (sName n) --DOp0 (sName n) i

instance DeBruijnify SIName Stmt where
    deBruijnify_ k v = \case
        StmtLet sn e -> StmtLet sn (deBruijnify_ k v e)
        x@PrecDef{} -> x
        x -> error $ "deBruijnify @ " ++ ppShow x

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

