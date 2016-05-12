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

import Data.Monoid
import Data.Maybe
import Data.List
import Data.Function
import Data.Bits
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMap as IM
import Control.Arrow hiding ((<+>))
import Control.DeepSeq

import LambdaCube.Compiler.Utils
import LambdaCube.Compiler.DeBruijn
import LambdaCube.Compiler.Pretty --hiding (braces, parens)

-------------------------------------------------------------------------------- simple name

type SName = String

pattern Ticked :: SName -> SName
pattern Ticked s = '\'': s

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
  deriving (Eq, Ord)

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
    , fileContent :: String
    }

instance Eq FileInfo where (==) = (==) `on` fileId
instance Ord FileInfo where compare = compare `on` fileId

instance PShow FileInfo where pShow = text . filePath

showPos :: FileInfo -> SPos -> Doc
showPos n p = pShow n <> ":" <> pShow p

-------------------------------------------------------------------------------- range

data Range = Range !FileInfo !SPos !SPos
    deriving (Eq, Ord)

instance NFData Range where
    rnf Range{} = ()

instance Show Range where show = ppShow
instance PShow Range
  where
    pShow (Range n b@(SPos r c) e@(SPos r' c')) = expand (pShow n <+> pShow b <> "-" <> pShow e)
      $ vcat $ (showPos n b <> ":")
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

--instance Show SI where show _ = "SI"
instance Eq SI where _ == _ = True
instance Ord SI where _ `compare` _ = EQ

instance Monoid SI where
    mempty = NoSI Set.empty
    mappend (RangeSI r1) (RangeSI r2) = RangeSI (joinRange r1 r2)
    mappend (NoSI ds1) (NoSI ds2) = NoSI  (ds1 `Set.union` ds2)
    mappend r@RangeSI{} _ = r
    mappend _ r@RangeSI{} = r

instance PShow SI where
    pShow (NoSI ds) = hsep $ map text $ Set.toList ds
    pShow (RangeSI r) = pShow r

hashPos :: FileInfo -> SPos -> Int
hashPos fn (SPos_ p) = (1 + fileId fn) `shiftL` 32 .|. p

debugSI a = NoSI (Set.singleton a)

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

pattern SIName_ si f n <- SIName__ _ si f n
  where SIName_ si f n =  SIName__ (fnameHash si n) si f n

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
                    | FRecordCons
                    | FRecItem
    -- type constructors
    | F'Int | F'Word | F'Float | F'String | F'Char | F'VecS | F'Output
    -- functions
    | Fcoe | FparEval | Ft2C | FprimFix
    | F'T2 | F'EqCT | F'CW | F'Split | F'VecScalar
    | Fparens | FtypeAnn | Fundefined | Fotherwise | FprimIfThenElse | FfromTo | FconcatMap | FfromInt | Fproject | Fswizzscalar | Fswizzvector
    -- other
    | F_rhs | F_section
    deriving (Eq, Ord, Show, Enum, Bounded)

tagName FCons = ":"
tagName t = case show t of 'F': s -> s

pattern Tag :: FNameTag -> SIName
pattern Tag t <- (toTag . nameHash -> Just t)
  where Tag t =  SIName__ (fromEnum t) (tagSI t) (tagFixity t) (tagName t)

pattern FTag t = FName (Tag t)

toTag i
    | i <= fromEnum (maxBound :: FNameTag) = Just (toEnum i)
    | otherwise = Nothing

tagFixity FCons = Just $ InfixR 5
tagFixity _ = Nothing

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
  deriving (Eq)

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
  deriving (Eq)

sLHS _ (SRHS x) = x
sLHS n x = SLHS n x

type SExp = SExp' Void

data Binder
    = BPi  Visibility
    | BLam Visibility
    | BMeta      -- a metavariable is like a floating hidden lambda
  deriving (Eq)

instance PShow Binder where
    pShow = \case
        BPi v -> "BPi" `DApp` pShow v
        BLam v -> "BLam" `DApp` pShow v
        BMeta -> "BMeta"

data Visibility = Hidden | Visible
  deriving (Eq)

instance PShow Visibility where
    pShow = \case
        Hidden -> "Hidden"
        Visible -> "Visible"

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

pattern SBuiltin' s <- SGlobal (SIName _ s)
  where SBuiltin' s =  SGlobal (SIName (debugSI $ "builtin " ++ s) s)

pattern SBuiltin s = SGlobal (Tag s)

pattern ConsName <- SIName _ ":"
  where ConsName =  SIName_ mempty (Just $ InfixR 5) ":"

pattern SRHS a      = SBuiltin F_rhs     `SAppV` a
pattern Section e   = SBuiltin F_section `SAppV` e
pattern SType       = SBuiltin F'Type
pattern SConstraint = SBuiltin F'Constraint
pattern Parens e    = SBuiltin Fparens   `SAppV` e
pattern SAnn a t    = SBuiltin FtypeAnn  `SAppH` t `SAppV` a
pattern TyType a    = SAnn a SType
pattern SCW a       = SBuiltin F'CW      `SAppV` a

-- builtin heterogenous list
pattern HList a   = SBuiltin F'HList `SAppV` a
pattern HCons a b = SBuiltin FHCons  `SAppV` a `SAppV` b
pattern HNil      = SBuiltin FHNil

-- builtin list
pattern BList a   = SBuiltin F'List `SAppV` a
pattern BCons a b = SGlobal ConsName `SAppV` a `SAppV` b
pattern BNil      = SBuiltin FNil

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
--        SGlobal op | Just p <- nameFixity op -> DOp0 (sName op) p
        SGlobal ns      -> pShow ns
        Parens x        -> pShow x     -- TODO: remove
        SAnn a b        -> shAnn (pShow a) (pShow b)
        TyType a        -> text "tyType" `DApp` pShow a
        SApp h a b      -> shApp h (pShow a) (pShow b)
        Wildcard SType  -> text "_"
        Wildcard t      -> shAnn (text "_") (pShow t)
        SBind_ _ h _ SType b -> shLam_ (usedVar 0 b) h Nothing (pShow b)
        SBind_ _ h _ a b -> shLam (usedVar 0 b) h (pShow a) (pShow b)
        SLet _ a b      -> shLet_ (pShow a) (pShow b)
        SLHS n x        -> "_lhs" `DApp` pShow n `DApp` pShow x
        STyped a        -> pShow a
        SVar _ i        -> shVar i
        SLit _ l        -> pShow l

shApp Visible a b = DApp a b
shApp Hidden a b = DApp a (DAt b)

shLam usedVar h a b = shLam_ usedVar h (Just a) b

simpleFo (DExpand x _) = x
simpleFo x = x

shLam_ False (BPi Hidden) (Just ((simpleFo -> DText "'CW") `DApp` a)) b = DFreshName False $ showContext (DUp 0 a) b
  where
    showContext x (DFreshName u d) = DFreshName u $ showContext (DUp 0 x) d
    showContext x (DParContext xs y) = DParContext (DComma x xs) y
    showContext x (DContext xs y) = DParContext (DComma x xs) y
    showContext x y = DContext x y

shLam_ usedVar h a b = DFreshName usedVar $ lam (p $ DUp 0 <$> a) b
  where
    lam = case h of
        BPi Visible
            | usedVar   -> showForall "->"
            | otherwise -> shArr
        BPi Hidden
            | usedVar   -> showForall "."
            | otherwise -> showContext
        _ -> showLam

    shAnn' a = maybe a (shAnn a)

    p = case h of
        BMeta -> shAnn' (blue $ DVar 0)
        BLam Hidden -> DAt . shAnn' (DVar 0)
        BLam Visible -> shAnn' (DVar 0)
        _ -> ann

    ann | usedVar = shAnn' (DVar 0)
        | otherwise = fromMaybe (text "Type")

    showForall s x (DFreshName u d) = DFreshName u $ showForall s (DUp 0 x) d
    showForall s x (DForall s' xs y) | s == s' = DForall s (DSep (InfixR 11) x xs) y
    showForall s x y = DForall s x y

    showContext x y = DContext' x y

showLam x (DFreshName u d) = DFreshName u $ showLam (DUp 0 x) d
showLam x (DLam xs y) = DLam (DSep (InfixR 11) x xs) y
showLam x y = DLam x y

shLet i a b = DLet' (DLet "=" (blue $ shVar i) $ DUp i a) (DUp i b)

showLet x (DFreshName u d) = DFreshName u $ showLet (DUp 0 x) d
showLet x (DLet' xs y) = DLet' (DSemi x xs) y
showLet x y = DLet' x y

shLet_ a b = DFreshName True $ showLet (DLet "=" (shVar 0) $ DUp 0 a) b

-------------------------------------------------------------------------------- statement

data Stmt
    = StLet SIName (Maybe SExp) SExp
    | Data SIName [(Visibility, SExp)]{-parameters-} SExp{-type-} [(SIName, SExp)]{-constructor names and types-}
    | PrecDef SIName Fixity

pattern Primitive n t = StLet n (Just t) (SBuiltin Fundefined)

instance PShow Stmt where
    pShow stmt = vcat . map DResetFreshNames $ case stmt of
        Primitive n t -> pure $ shAnn (pShow n) (pShow t)
        StLet n ty e -> [shAnn (pShow n) (pShow t) | Just t <- [ty]] ++ [DLet "=" (pShow n) (pShow e)]
        Data n ps ty cs -> pure $ nest 2 $ "data" <+> nest 2 (shAnn (foldl DApp (DTypeNamespace True $ pShow n) [shAnn (text "_") (pShow t) | (v, t) <- ps]) (pShow ty)) </> "where" <> nest 2 (hardline <> vcat [shAnn (pShow n) $ pShow $ UncurryS (first (const Hidden) <$> ps) t | (n, t) <- cs])
        PrecDef n i -> pure $ pShow i <+> text (sName n) --DOp0 (sName n) i

instance DeBruijnify SIName Stmt where
    deBruijnify_ k v = \case
        StLet sn mt e -> StLet sn (deBruijnify_ k v <$> mt) (deBruijnify_ k v e)
        x -> error $ "deBruijnify @ " ++ ppShow x

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
    nodes = zipWith mkNode [0..] xs
      where
        mkNode i s = StmtNode i s (nubBy ((==) `on` snId) $ catMaybes $ (`Map.lookup` defMap) <$> need)
                                  (fromMaybe [] $ IM.lookup i revMap)
          where
            need = Set.toList $ case s of
                PrecDef{} -> mempty
                StLet _ mt e -> foldMap names mt <> names e
                Data _ ps t cs -> foldMap (names . snd) ps <> names t <> foldMap (names . snd) cs

            names = foldName Set.singleton

    revMap = IM.unionsWith (++) [IM.singleton (snId c) [n] | n <- nodes, c <- snChildren n]

    defMap = Map.fromList [(s, n) | n <- nodes, s <- def $ snValue n]
      where
        def = \case
            PrecDef{} -> mempty
            StLet n _ _ -> [n]
            Data n _ _ cs -> n: map fst cs

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

