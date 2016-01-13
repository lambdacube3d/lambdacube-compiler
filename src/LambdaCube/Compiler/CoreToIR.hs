{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
module LambdaCube.Compiler.CoreToIR
    ( compilePipeline
    , Exp, toExp, tyOf, outputType, boolType, trueExp
    ) where

import Data.Char
import Data.List
import Data.Maybe
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Vector (Vector,(!))
import qualified Data.Vector as Vector
import Control.Applicative
import Control.Arrow hiding ((<+>))
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Identity
import Text.Parsec.Pos
import Debug.Trace

import IR(Backend(..))
import qualified IR as IR
import qualified "lambdacube-ir" Linear as IR

import LambdaCube.Compiler.Pretty hiding (parens)
import qualified LambdaCube.Compiler.Infer as I
import LambdaCube.Compiler.Infer (SName, Lit(..), Visibility(..))

--------------------------------------------------------------------------

type CG = State IR.Pipeline

pattern TFrameBuffer a b <- A2 "FrameBuffer" a b

emptyPipeline b = IR.Pipeline b mempty mempty mempty mempty mempty mempty mempty
update i x xs = xs Vector.// [(i,x)]

newTexture :: Int -> Int -> IR.ImageSemantic -> CG IR.TextureName
newTexture width height semantic = do
  let sampleDescriptor = IR.SamplerDescriptor
        { IR.samplerWrapS       = IR.Repeat
        , IR.samplerWrapT       = Nothing
        , IR.samplerWrapR       = Nothing
        , IR.samplerMinFilter   = IR.Linear 
        , IR.samplerMagFilter   = IR.Linear
        , IR.samplerBorderColor = IR.VV4F (IR.V4 0 0 0 1)
        , IR.samplerMinLod      = Nothing
        , IR.samplerMaxLod      = Nothing
        , IR.samplerLodBias     = 0
        , IR.samplerCompareFunc = Nothing
        }

      textureDescriptor = IR.TextureDescriptor
        { IR.textureType      = IR.Texture2D (if semantic == IR.Color then IR.FloatT IR.RGBA else IR.FloatT IR.Red) 1
        , IR.textureSize      = IR.VV2U $ IR.V2 (fromIntegral width) (fromIntegral height)
        , IR.textureSemantic  = semantic
        , IR.textureSampler   = sampleDescriptor
        , IR.textureBaseLevel = 0
        , IR.textureMaxLevel  = 0
        }
  tv <- gets IR.textures
  modify (\s -> s {IR.textures = tv <> pure textureDescriptor})
  return $ length tv

newFrameBufferTarget :: Ty -> CG IR.RenderTargetName
newFrameBufferTarget (TFrameBuffer _ a) = do
  let t = IR.RenderTarget $ Vector.fromList [IR.TargetItem s (Just (IR.Framebuffer s)) | s <- compSemantic a]
  tv <- gets IR.targets
  modify (\s -> s {IR.targets = tv <> pure t})
  return $ length tv
newFrameBufferTarget x = error $ "newFrameBufferTarget illegal target type: " ++ ppShow x

newTextureTarget :: Int -> Int -> Ty -> CG IR.RenderTargetName
newTextureTarget w h (TFrameBuffer _ a) = do
  tl <- forM (compSemantic a) $ \s -> do
    texture <- newTexture w h s
    return $ IR.TargetItem s (Just (IR.TextureImage texture 0 Nothing))
  tv <- gets IR.targets
  modify (\s -> s {IR.targets = tv <> pure (IR.RenderTarget $ Vector.fromList tl)})
  return $ Vector.length tv
newTextureTarget _ _ x = error $ "newTextureTarget illegal target type: " ++ ppShow x

compilePipeline :: IR.Backend -> Exp -> IR.Pipeline
compilePipeline b e = flip execState (emptyPipeline b) $ do
    (subCmds,cmds) <- getCommands e
    modify (\s -> s {IR.commands = Vector.fromList subCmds <> Vector.fromList cmds})

mergeSlot a b = a
  { IR.slotUniforms = IR.slotUniforms a <> IR.slotUniforms b
  , IR.slotStreams  = IR.slotStreams a <> IR.slotStreams b
  , IR.slotPrograms = IR.slotPrograms a <> IR.slotPrograms b
  }

getSlot :: Exp -> CG (IR.Command,[(String,IR.InputType)])
getSlot e@(A2 "Fetch" (EString slotName) attrs) = do
  let input = compAttribute attrs
      slot = IR.Slot
        { IR.slotName       = slotName
        , IR.slotUniforms   = mempty
        , IR.slotStreams    = Map.fromList input
        , IR.slotPrimitive  = compFetchPrimitive $ getPrim $ tyOf e
        , IR.slotPrograms   = mempty
        }
  sv <- gets IR.slots
  case Vector.findIndex ((slotName ==) . IR.slotName) sv of
    Nothing -> do
      modify (\s -> s {IR.slots = sv <> pure slot})
      return (IR.RenderSlot $ length sv,input)
    Just i -> do
      modify (\s -> s {IR.slots = update i (mergeSlot (sv ! i) slot) sv})
      return (IR.RenderSlot i,input)
getSlot e@(A1 "FetchArrays" attrs) = do
  let (input,values) = unzip [((name,ty),(name,value)) | (i,(ty,value)) <- zip [0..] (compAttributeValue attrs), let name = "attribute_" ++ show i]
      stream = IR.StreamData
        { IR.streamData       = Map.fromList values
        , IR.streamType       = Map.fromList input
        , IR.streamPrimitive  = compFetchPrimitive $ getPrim $ tyOf e
        , IR.streamPrograms   = mempty
        }
  sv <- gets IR.streams
  modify (\s -> s {IR.streams = sv <> pure stream})
  return (IR.RenderStream $ length sv,input)
getSlot x = error $ "getSlot: " ++ ppShow x

getPrim (A2 "VertexStream" p _) = p

addProgramToSlot :: IR.ProgramName -> IR.Command -> CG ()
addProgramToSlot prgName (IR.RenderSlot slotName) = do
  sv <- gets IR.slots
  pv <- gets IR.programs
  let slot = sv ! slotName
      prg = pv ! prgName
      slot' = slot
        { IR.slotUniforms = IR.slotUniforms slot <> IR.programUniforms prg
        , IR.slotPrograms = IR.slotPrograms slot <> pure prgName
        }
  modify (\s -> s {IR.slots = update slotName slot' sv})
addProgramToSlot prgName (IR.RenderStream streamName) = do
  sv <- gets IR.streams
  pv <- gets IR.programs
  let stream = sv ! streamName
      prg = pv ! prgName
      stream' = stream
        { IR.streamPrograms = IR.streamPrograms stream <> pure prgName
        }
  modify (\s -> s {IR.streams = update streamName stream' sv})

getProgram :: [(String,IR.InputType)] -> IR.Command -> Exp -> Exp -> Exp -> CG IR.ProgramName
getProgram input slot vert frag ffilter = do
  backend <- gets IR.backend
  let ((vertexInput,vertOut),vertSrc) = genVertexGLSL backend vert
      fragSrc = genFragmentGLSL backend vertOut frag ffilter
      prg = IR.Program
        { IR.programUniforms    = Map.fromList $ Set.toList $ getUniforms vert <> getUniforms frag
        , IR.programStreams     = Map.fromList $ zip vertexInput $ map (uncurry IR.Parameter) input
        , IR.programInTextures  = Map.fromList $ Set.toList $ getSamplerUniforms vert <> getSamplerUniforms frag
        , IR.programOutput      = pure $ IR.Parameter "f0" IR.V4F -- TODO
        , IR.vertexShader       = vertSrc
        , IR.geometryShader     = mempty -- TODO
        , IR.fragmentShader     = fragSrc
        }
  pv <- gets IR.programs
  modify (\s -> s {IR.programs = pv <> pure prg})
  let prgName = length pv
  addProgramToSlot prgName slot
  return prgName

getRenderTextures :: Exp -> [Exp]
getRenderTextures e = case e of
  ELet (PVar (A0 "Sampler") _) (A3 "Sampler" _ _ (A2 "Texture2D" _ _)) _ -> [e]
  Exp e -> foldMap getRenderTextures e

type SamplerBinding = (IR.UniformName,IR.ImageRef)

getRenderTextureCommands :: Exp -> CG ([SamplerBinding],[IR.Command])
getRenderTextureCommands e = (\f -> foldM (\(a,b) x -> f x >>= (\(c,d) -> return (c:a,d ++ b))) mempty (getRenderTextures e)) $ \case
  ELet (PVar t n) (A3 "Sampler" _ _ (A2 "Texture2D" (A2 "V2" (EInt w) (EInt h)) (A1 "PrjImageColor" a))) _ -> do
    rt <- newTextureTarget (fromIntegral w) (fromIntegral h) (tyOf a)
    tv <- gets IR.targets
    let IR.RenderTarget (Vector.toList -> [_,IR.TargetItem IR.Color (Just (IR.TextureImage texture _ _))]) = tv ! rt
    (subCmds,cmds) <- getCommands a
    return ((n,IR.TextureImage texture 0 Nothing), subCmds <> (IR.SetRenderTarget rt:cmds))
  ELet (PVar t n) (A3 "Sampler" _ _ (A2 "Texture2D" (A2 "V2" (EInt w) (EInt h)) (A1 "PrjImage" a))) _ -> do
    rt <- newTextureTarget (fromIntegral w) (fromIntegral h) (tyOf a)
    tv <- gets IR.targets
    let IR.RenderTarget (Vector.toList -> [IR.TargetItem IR.Color (Just (IR.TextureImage texture _ _))]) = tv ! rt
    (subCmds,cmds) <- getCommands a
    return ((n,IR.TextureImage texture 0 Nothing), subCmds <> (IR.SetRenderTarget rt:cmds))
  x -> error $ "getRenderTextureCommands: not supported render texture exp: " ++ ppShow x

getCommands :: Exp -> CG ([IR.Command],[IR.Command])
getCommands e = case e of
  A1 "ScreenOut" a -> do
    rt <- newFrameBufferTarget (tyOf a)
    (subCmds,cmds) <- getCommands a
    return (subCmds,IR.SetRenderTarget rt : cmds)
  A5 "Accumulate" actx ffilter frag (A2 "Rasterize" rctx (A2 "Transform" vert input)) fbuf -> do
    (smpBindingsV,vertCmds) <- getRenderTextureCommands vert
    (smpBindingsF,fragCmds) <- getRenderTextureCommands frag
    (renderCommand,input) <- getSlot input
    prog <- getProgram input renderCommand vert frag ffilter
    (subFbufCmds, fbufCommands) <- getCommands fbuf
    programs <- gets IR.programs
    let textureUniforms = [IR.SetSamplerUniform n textureUnit | ((n,IR.FTexture2D),textureUnit) <- zip (Map.toList $ IR.programUniforms $ programs ! prog) [0..]]
        cmds =
          [ IR.SetProgram prog ] <>
          textureUniforms <>
          concat -- TODO: generate IR.SetSamplerUniform commands for texture slots
          [ [ IR.SetTexture textureUnit texture
            , IR.SetSamplerUniform name textureUnit
            ] | (textureUnit,(name,IR.TextureImage texture _ _)) <- zip [length textureUniforms..] (smpBindingsV <> smpBindingsF)
          ] <>
          [ IR.SetRasterContext (compRC rctx)
          , IR.SetAccumulationContext (compAC actx)
          , renderCommand
          ]
    return (subFbufCmds <> vertCmds <> fragCmds, fbufCommands <> cmds)
  A1 "FrameBuffer" a -> return ([],[IR.ClearRenderTarget (Vector.fromList $ map (uncurry IR.ClearImage) $ compFrameBuffer a)])
  x -> error $ "getCommands " ++ ppShow x

getSamplerUniforms :: Exp -> Set (String,IR.InputType)
getSamplerUniforms e = case e of
  ELet (PVar _ _) (A3 "Sampler" _ _ (A1 "Texture2DSlot" (EString s))) _ -> Set.singleton (s, IR.FTexture2D{-compInputType $ tyOf e-}) -- TODO
  ELet (PVar _ n) (A3 "Sampler" _ _ (A2 "Texture2D" _ _)) _ -> Set.singleton ((n, IR.FTexture2D))
  Exp e -> foldMap getSamplerUniforms e

getUniforms :: Exp -> Set (String,IR.InputType)
getUniforms e = case e of
  Uniform (EString s) -> Set.singleton (s, compInputType $ tyOf e)
  ELet (PVar _ _) (A3 "Sampler" _ _ (A1 "Texture2DSlot" (EString s))) _ -> Set.singleton (s, IR.FTexture2D{-compInputType $ tyOf e-}) -- TODO
  ELet (PVar _ _) (A3 "Sampler" _ _ (A2 "Texture2D" _ _)) _ -> mempty
  Exp e -> foldMap getUniforms e

compFrameBuffer x = case x of
  ETuple a -> concatMap compFrameBuffer a
  A1 "DepthImage" a -> [(IR.Depth, compValue a)]
  A1 "ColorImage" a -> [(IR.Color, compValue a)]
  x -> error $ "compFrameBuffer " ++ ppShow x

compSemantic x = case x of
  TTuple t       -> concatMap compSemantic t
  A1 "Depth" _   -> return IR.Depth
  A1 "Stencil" _ -> return IR.Stencil
  A1 "Color" _   -> return IR.Color
  x -> error $ "compSemantic " ++ ppShow x

compAC x = case x of
  A1 "AccumulationContext" (ETuple a) -> IR.AccumulationContext Nothing (map compFrag a)
  A1 "AccumulationContext" a -> IR.AccumulationContext Nothing [compFrag a]
  x -> error $ "compAC " ++ ppShow x

compBlending x = case x of
  A0 "NoBlending" -> IR.NoBlending
  A1 "BlendLogicOp" a -> IR.BlendLogicOp (compLO a)
  A3 "Blend" (ETuple [a,b]) (ETuple [ETuple [c,d],ETuple [e,f]]) (compValue -> IR.VV4F g) -> IR.Blend (compBE a) (compBE b) (compBF c) (compBF d) (compBF e) (compBF f) g
  x -> error $ "compBlending " ++ ppShow x

compBF x = case x of
  A0 "Zero'" -> IR.Zero
  A0 "One" -> IR.One
  A0 "SrcColor" -> IR.SrcColor
  A0 "OneMinusSrcColor" -> IR.OneMinusSrcColor
  A0 "DstColor" -> IR.DstColor
  A0 "OneMinusDstColor" -> IR.OneMinusDstColor
  A0 "SrcAlpha" -> IR.SrcAlpha
  A0 "OneMinusSrcAlpha" -> IR.OneMinusSrcAlpha
  A0 "DstAlpha" -> IR.DstAlpha
  A0 "OneMinusDstAlpha" -> IR.OneMinusDstAlpha
  A0 "ConstantColor" -> IR.ConstantColor
  A0 "OneMinusConstantColor" -> IR.OneMinusConstantColor
  A0 "ConstantAlpha" -> IR.ConstantAlpha
  A0 "OneMinusConstantAlpha" -> IR.OneMinusConstantAlpha
  A0 "SrcAlphaSaturate" -> IR.SrcAlphaSaturate
  x -> error $ "compBF " ++ ppShow x

compBE x = case x of
  A0 "FuncAdd" -> IR.FuncAdd
  A0 "FuncSubtract" -> IR.FuncSubtract
  A0 "FuncReverseSubtract" -> IR.FuncReverseSubtract
  A0 "Min" -> IR.Min
  A0 "Max" -> IR.Max
  x -> error $ "compBE " ++ ppShow x

compLO x = case x of
  A0 "Clear" -> IR.Clear
  A0 "And" -> IR.And
  A0 "AndReverse" -> IR.AndReverse
  A0 "Copy" -> IR.Copy
  A0 "AndInverted" -> IR.AndInverted
  A0 "Noop" -> IR.Noop
  A0 "Xor" -> IR.Xor
  A0 "Or" -> IR.Or
  A0 "Nor" -> IR.Nor
  A0 "Equiv" -> IR.Equiv
  A0 "Invert" -> IR.Invert
  A0 "OrReverse" -> IR.OrReverse
  A0 "CopyInverted" -> IR.CopyInverted
  A0 "OrInverted" -> IR.OrInverted
  A0 "Nand" -> IR.Nand
  A0 "Set" -> IR.Set
  x -> error $ "compLO " ++ ppShow x

compComparisonFunction x = case x of
  A0 "Never" -> IR.Never
  A0 "Less" -> IR.Less
  A0 "Equal" -> IR.Equal
  A0 "Lequal" -> IR.Lequal
  A0 "Greater" -> IR.Greater
  A0 "Notequal" -> IR.Notequal
  A0 "Gequal" -> IR.Gequal
  A0 "Always" -> IR.Always
  x -> error $ "compComparisonFunction " ++ ppShow x

compBool x = case x of
  A0 "True" -> True
  A0 "False" -> False
  x -> error $ "compBool " ++ ppShow x

compFrag x = case x of
  A2 "DepthOp" (compComparisonFunction -> a) (compBool -> b) -> IR.DepthOp a b
  A2 "ColorOp" (compBlending -> b) (compValue -> v) -> IR.ColorOp b v
  x -> error $ "compFrag " ++ ppShow x

compInputType x = case x of
  TFloat          -> IR.Float
  TVec 2 TFloat   -> IR.V2F
  TVec 3 TFloat   -> IR.V3F
  TVec 4 TFloat   -> IR.V4F
  TBool           -> IR.Bool
  TVec 2 TBool    -> IR.V2B
  TVec 3 TBool    -> IR.V3B
  TVec 4 TBool    -> IR.V4B
  TInt            -> IR.Int
  TVec 2 TInt     -> IR.V2I
  TVec 3 TInt     -> IR.V3I
  TVec 4 TInt     -> IR.V4I
  TWord           -> IR.Word
  TVec 2 TWord    -> IR.V2U
  TVec 3 TWord    -> IR.V3U
  TVec 4 TWord    -> IR.V4U
  TMat 2 2 TFloat -> IR.M22F
  TMat 2 3 TFloat -> IR.M23F
  TMat 2 4 TFloat -> IR.M24F
  TMat 3 2 TFloat -> IR.M32F
  TMat 3 3 TFloat -> IR.M33F
  TMat 3 4 TFloat -> IR.M34F
  TMat 4 2 TFloat -> IR.M42F
  TMat 4 3 TFloat -> IR.M43F
  TMat 4 4 TFloat -> IR.M44F
  x -> error $ "compInputType " ++ ppShow x

compAttribute x = case x of
  ETuple a -> concatMap compAttribute a
  Prim1 "Attribute" (EString s) -> [(s, compInputType $ tyOf x)]
  x -> error $ "compAttribute " ++ ppShow x

compAttributeValue :: Exp -> [(IR.InputType,IR.ArrayValue)]
compAttributeValue x = let
    compList (A2 "Cons" a x) = compValue a : compList x
    compList (A0 "Nil") = []
    compList x = error $ "compList: " ++ ppShow x
    emptyArray t | t `elem` [IR.Float,IR.V2F,IR.V3F,IR.V4F,IR.M22F,IR.M23F,IR.M24F,IR.M32F,IR.M33F,IR.M34F,IR.M42F,IR.M43F,IR.M44F] = IR.VFloatArray mempty
    emptyArray t | t `elem` [IR.Int,IR.V2I,IR.V3I,IR.V4I] = IR.VIntArray mempty
    emptyArray t | t `elem` [IR.Word,IR.V2U,IR.V3U,IR.V4U] = IR.VWordArray mempty
    emptyArray t | t `elem` [IR.Bool,IR.V2B,IR.V3B,IR.V4B] = IR.VBoolArray mempty
    emptyArray _ = error "compAttributeValue - emptyArray"
    flatten IR.Float (IR.VFloat x) (IR.VFloatArray l) = IR.VFloatArray $ pure x <> l
    flatten IR.V2F (IR.VV2F (IR.V2 x y)) (IR.VFloatArray l) = IR.VFloatArray $ pure x <> pure y <> l
    flatten IR.V3F (IR.VV3F (IR.V3 x y z)) (IR.VFloatArray l) = IR.VFloatArray $ pure x <> pure y <> pure z <> l
    flatten IR.V4F (IR.VV4F (IR.V4 x y z w)) (IR.VFloatArray l) = IR.VFloatArray $ pure x <> pure y <> pure z <> pure w <> l
    flatten _ _ _ = error "compAttributeValue"
    checkLength l@((a,_):_) = case all (\(i,_) -> i == a) l of
      True  -> snd $ unzip l
      False -> error "FetchArrays array length mismatch!"
    go = \case
      ETuple a -> concatMap go a
      a -> let A1 "List" (compInputType -> t) = tyOf a
               values = compList a
           in
            [(length values,(t,foldr (flatten t) (emptyArray t) values))]
  in checkLength $ go x

compFetchPrimitive x = case x of
  A0 "Point" -> IR.Points
  A0 "Line" -> IR.Lines
  A0 "Triangle" -> IR.Triangles
  A0 "LineAdjacency" -> IR.LinesAdjacency
  A0 "TriangleAdjacency" -> IR.TrianglesAdjacency
  x -> error $ "compFetchPrimitive " ++ ppShow x

compValue x = case x of
  EFloat a -> IR.VFloat $ realToFrac a
  EInt a -> IR.VInt $ fromIntegral a
  A2 "V2" (EFloat a) (EFloat b) -> IR.VV2F $ IR.V2 (realToFrac a) (realToFrac b)
  A3 "V3" (EFloat a) (EFloat b) (EFloat c) -> IR.VV3F $ IR.V3 (realToFrac a) (realToFrac b) (realToFrac c)
  A4 "V4" (EFloat a) (EFloat b) (EFloat c) (EFloat d) -> IR.VV4F $ IR.V4 (realToFrac a) (realToFrac b) (realToFrac c) (realToFrac d)
  A2 "V2" (compBool -> a) (compBool -> b) -> IR.VV2B $ IR.V2 a b
  A3 "V3" (compBool -> a) (compBool -> b) (compBool -> c) -> IR.VV3B $ IR.V3 a b c
  A4 "V4" (compBool -> a) (compBool -> b) (compBool -> c) (compBool -> d) -> IR.VV4B $ IR.V4 a b c d
  x -> error $ "compValue " ++ ppShow x

compRC x = case x of
  A3 "PointCtx" a (EFloat b) c -> IR.PointCtx (compPS a) (realToFrac b) (compPSCO c)
  A2 "LineCtx" (EFloat a) b -> IR.LineCtx (realToFrac a) (compPV b)
  A4 "TriangleCtx" a b c d -> IR.TriangleCtx (compCM a) (compPM b) (compPO c) (compPV d)
  x -> error $ "compRC " ++ ppShow x

compPSCO x = case x of
  A0 "LowerLeft" -> IR.LowerLeft
  A0 "UpperLeft" -> IR.UpperLeft
  x -> error $ "compPSCO " ++ ppShow x

compCM x = case x of
  A0 "CullNone" -> IR.CullNone
  A1 "CullFront" a -> IR.CullFront $ compFF a
  A1 "CullBack" a -> IR.CullBack $ compFF a
  x -> error $ "compCM " ++ ppShow x

compFF x = case x of
  A0 "CW" -> IR.CW
  A0 "CCW" -> IR.CCW
  x -> error $ "compFF " ++ ppShow x

compPM x = case x of
  A0 "PolygonFill" -> IR.PolygonFill
  A1 "PolygonLine" (EFloat a) -> IR.PolygonLine $ realToFrac a
  A1 "PolygonPoint" a  -> IR.PolygonPoint $ compPS a
  x -> error $ "compPM " ++ ppShow x

compPS x = case x of
  A1 "PointSize" (EFloat a) -> IR.PointSize $ realToFrac a
  A0 "ProgramPointSize" -> IR.ProgramPointSize
  x -> error $ "compPS " ++ ppShow x

compPO x = case x of
  A2 "Offset" (EFloat a) (EFloat b) -> IR.Offset (realToFrac a) (realToFrac b)
  A0 "NoOffset" -> IR.NoOffset
  x -> error $ "compPO " ++ ppShow x

compPV x = case x of
    A0 "FirstVertex" -> IR.FirstVertex
    A0 "LastVertex" -> IR.LastVertex
    x -> error $ "compPV " ++ ppShow x

--------------------------------------------------------------- GLSL generation

{-
mangleIdent :: String -> String
mangleIdent n = '_': concatMap encodeChar n
  where
    encodeChar = \case
        c | isAlphaNum c -> [c]
        '_'  -> "__"
        '.'  -> "_dot"
        '$'  -> "_dollar"
        '~'  -> "_tilde"
        '='  -> "_eq"
        '<'  -> "_less"
        '>'  -> "_greater"
        '!'  -> "_bang"
        '#'  -> "_hash"
        '%'  -> "_percent"
        '^'  -> "_up"
        '&'  -> "_amp"
        '|'  -> "_bar"
        '*'  -> "_times"
        '/'  -> "_div"
        '+'  -> "_plus"
        '-'  -> "_minus"
        ':'  -> "_colon"
        '\\' -> "_bslash"
        '?'  -> "_qmark"
        '@'  -> "_at"
        '\'' -> "_prime"
        c    -> '$' : show (ord c)
-}

genUniforms :: Exp -> Set [String]
genUniforms e = case e of
  Uniform (EString s) -> Set.singleton [unwords ["uniform",toGLSLType "1" $ tyOf e,s,";"]]
  ELet (PVar _ _) (A3 "Sampler" _ _ (A1 "Texture2DSlot" (EString n))) _ -> Set.singleton [unwords ["uniform","sampler2D",n,";"]]
  ELet (PVar _ n) (A3 "Sampler" _ _ (A2 "Texture2D" _ _)) _ -> Set.singleton [unwords ["uniform","sampler2D",n,";"]]
  Exp e -> foldMap genUniforms e

type GLSL = Writer [String]

genStreamInput :: Backend -> Pat -> GLSL [String]
genStreamInput backend i = fmap concat $ mapM input $ case i of
    PTuple l -> l
    x -> [x]
  where
    input (PVar t n) = tell [unwords [inputDef,toGLSLType (n ++ "\n") t,n,";"]] >> return [n]
    input a = error $ "genStreamInput " ++ ppShow a
    inputDef = case backend of
        OpenGL33  -> "in"
        WebGL1    -> "attribute"

genStreamOutput :: Backend -> Exp -> GLSL [(String, String, String)]
genStreamOutput backend (eTuple -> l) = fmap concat $ zipWithM go (map (("v" ++) . show) [0..]) l
  where
    go var (A1 (f -> i) (toGLSLType "3" . tyOf -> t)) = do
        tell $ case backend of
          WebGL1    -> [unwords ["varying",t,var,";"]]
          OpenGL33  -> [unwords [i,"out",t,var,";"]]
        return [(i,t,var)]
    f "Smooth" = "smooth"
    f "Flat" = "flat"
    f "NoPerspective" = "noperspective"

eTuple (ETuple l) = l
eTuple x = [x]

genFragmentInput :: Backend -> [(String, String, String)] -> GLSL ()
genFragmentInput OpenGL33 s = tell [unwords [i,"in",t,n,";"] | (i,t,n) <- s]
genFragmentInput WebGL1 s = tell [unwords ["varying",t,n,";"] | (i,t,n) <- s]
genFragmentOutput backend (tyOf -> a@(toGLSLType "4" -> t)) = case a of
  TUnit -> return False
  _ -> case backend of
    OpenGL33  -> tell [unwords ["out",t,"f0",";"]] >> return True
    WebGL1    -> return True

genVertexGLSL :: Backend -> Exp -> (([String],[(String,String,String)]),String)
genVertexGLSL backend e@(etaRed -> ELam i (A4 "VertexOut" p s c o)) = id *** unlines $ runWriter $ do
  case backend of
    OpenGL33 -> do
      tell ["#version 330 core"]
      tell ["vec4 texture2D(sampler2D s, vec2 uv){return texture(s,uv);}"]
    WebGL1 -> do
      tell ["#version 100"]
      tell ["precision highp float;"]
      tell ["precision highp int;"]
  mapM_ tell $ genUniforms e
  input <- genStreamInput backend i
  out <- genStreamOutput backend o
  tell ["void main() {"]
  unless (null out) $ sequence_ [tell $ [var <> " = " <> genGLSL x <> ";"] | ((_,_,var),x) <- zip out $ eTuple o]
  tell ["gl_Position = "  <> genGLSL p <> ";"]
  tell ["gl_PointSize = " <> genGLSL s <> ";"]
  tell ["}"]
  return (input,out)
genVertexGLSL _ e = error $ "genVertexGLSL: " ++ ppShow e

genGLSL :: Exp -> String
genGLSL e = show $ genGLSLSubst mempty e

genFragmentGLSL :: Backend -> [(String,String,String)] -> Exp -> Exp -> String
genFragmentGLSL backend s e@(etaRed -> ELam i fragOut) ffilter{-TODO-} = unlines $ execWriter $ do
  case backend of
    OpenGL33 -> do
      tell ["#version 330 core"]
      tell ["vec4 texture2D(sampler2D s, vec2 uv){return texture(s,uv);}"]
    WebGL1 -> do
      tell ["#version 100"]
      tell ["precision highp float;"]
      tell ["precision highp int;"]
  mapM_ tell $ genUniforms e
  genFragmentInput backend s
  let o = case fragOut of
        A1 "FragmentOutRastDepth" o -> o
        A1 "FragmentOut" o -> o
        _ -> error $ "genFragmentGLSL fragOut " ++ ppShow fragOut
  hasOutput <- genFragmentOutput backend o
  tell ["void main() {"]
  case ffilter of
    A0 "PassAll" -> return ()
    A1 "Filter" (etaRed -> ELam i o) -> tell ["if (!(" <> show (genGLSLSubst (makeSubst i s) o) <> ")) discard;"]
  when hasOutput $ case backend of
    OpenGL33  -> tell ["f0 = " <> show (genGLSLSubst (makeSubst i s) o) <> ";"]
    WebGL1    -> tell ["gl_FragColor = " <> show (genGLSLSubst (makeSubst i s) o) <> ";"]
  tell ["}"]
genFragmentGLSL _ _ e ff = error $ "genFragmentGLSL: " ++ ppShow e ++ ppShow ff

makeSubst (PVar _ x) [(_,_,n)] = Map.singleton x n
makeSubst (PTuple l) x = Map.fromList $ go l x where
    go [] [] = []
    go (PVar _ x: al) ((_,_,n):bl) = (x,n) : go al bl
    go i s = error $ "genFragmentGLSL illegal input " ++ ppShow i ++ " " ++ show s

parens a = "(" <+> a <+> ")"

-- todo: (on hold) name mangling to prevent name collisions
-- todo: reader monad
genGLSLSubst :: Map String String -> Exp -> Doc
genGLSLSubst s e = case e of
  ELit a -> text $ show a
  EVar a -> text $ Map.findWithDefault a a s
  Uniform (EString s) -> text s
  -- texturing
  A3 "Sampler" _ _ _ -> error $ "sampler GLSL codegen is not supported"
  PrimN "texture2D" xs -> functionCall "texture2D" xs
  -- interpolation
  A1 "Smooth" a -> gen a
  A1 "Flat" a -> gen a
  A1 "NoPerspecitve" a -> gen a

  -- temp builtins FIXME: get rid of these
  Prim1 "primIntToWord" a -> error $ "WebGL 1 does not support uint types: " ++ ppShow e
  Prim1 "primIntToFloat" a -> gen a -- FIXME: does GLSL support implicit int to float cast???
  Prim2 "primCompareInt" a b -> error $ "GLSL codegen does not support: " ++ ppShow e
  Prim2 "primCompareWord" a b -> error $ "GLSL codegen does not support: " ++ ppShow e
  Prim2 "primCompareFloat" a b -> error $ "GLSL codegen does not support: " ++ ppShow e
  Prim1 "primNegateInt" a -> text "-" <+> parens (gen a)
  Prim1 "primNegateWord" a -> error $ "WebGL 1 does not support uint types: " ++ ppShow e
  Prim1 "primNegateFloat" a -> text "-" <+> parens (gen a)

  -- vectors
  AN n xs | n `elem` ["V2", "V3", "V4"], Just s <- vecConName $ tyOf e -> functionCall s xs
  -- bool
  A0 "True"  -> text "true"
  A0 "False" -> text "false"
  -- matrices
  AN "M22F" xs -> functionCall "mat2" xs
  AN "M23F" xs -> error "WebGL 1 does not support matrices with this dimension"
  AN "M24F" xs -> error "WebGL 1 does not support matrices with this dimension"
  AN "M32F" xs -> error "WebGL 1 does not support matrices with this dimension"
  AN "M33F" xs -> functionCall "mat3" xs
  AN "M34F" xs -> error "WebGL 1 does not support matrices with this dimension"
  AN "M42F" xs -> error "WebGL 1 does not support matrices with this dimension"
  AN "M43F" xs -> error "WebGL 1 does not support matrices with this dimension"
  AN "M44F" xs -> functionCall "mat4" xs -- where gen = gen

  Prim3 "primIfThenElse" a b c -> gen a <+> "?" <+> gen b <+> ":" <+> gen c
  -- TODO: Texture Lookup Functions
  SwizzProj a x -> "(" <+> gen a <+> (")." <> text x)
  ELam _ _ -> error "GLSL codegen for lambda function is not supported yet"
  ELet (PVar _ _) (A3 "Sampler" _ _ (A1 "Texture2DSlot" (EString n))) _ -> text n
  ELet (PVar _ n) (A3 "Sampler" _ _ (A2 "Texture2D" _ _)) _ -> text n
  ELet _ _ _ -> error "GLSL codegen for let is not supported yet"
  ETuple _ -> error "GLSL codegen for tuple is not supported yet"

  -- Primitive Functions
  PrimN ('P':'r':'i':'m':n) xs | n'@(_:_) <- trName (dropS n) -> case n' of
      (c:_) | isAlpha c -> functionCall n' xs
      [op, '_']         -> prefixOp [op] xs
      n'                -> binOp n' xs
    where
      ifType p a b = if all (p . tyOf) xs then a else b

      dropS n
        | last n == 'S' && init n `elem` ["Add", "Sub", "Div", "Mod", "BAnd", "BOr", "BXor", "BShiftL", "BShiftR", "Min", "Max", "Clamp", "Mix", "Step", "SmoothStep"] = init n
        | otherwise = n

      trName = \case

        -- Arithmetic Functions
        "Add"               -> "+"
        "Sub"               -> "-"
        "Neg"               -> "-_"
        "Mul"               -> ifType isMatrix "matrixCompMult" "*"
        "MulS"              -> "*"
        "Div"               -> "/"
        "Mod"               -> ifType isIntegral "%" "mod"

        -- Bit-wise Functions
        "BAnd"              -> "&"
        "BOr"               -> "|"
        "BXor"              -> "^"
        "BNot"              -> "~_"
        "BShiftL"           -> "<<"
        "BShiftR"           -> ">>"

        -- Logic Functions
        "And"               -> "&&"
        "Or"                -> "||"
        "Xor"               -> "^"
        "Not"               -> ifType isScalar "!_" "not"

        -- Integer/Float Conversion Functions
        "FloatBitsToInt"    -> "floatBitsToInt"
        "FloatBitsToUInt"   -> "floatBitsToUint"
        "IntBitsToFloat"    -> "intBitsToFloat"
        "UIntBitsToFloat"   -> "uintBitsToFloat"

        -- Matrix Functions
        "OuterProduct"      -> "outerProduct"
        "MulMatVec"         -> "*"
        "MulVecMat"         -> "*"
        "MulMatMat"         -> "*"

        -- Fragment Processing Functions
        "DFdx"              -> "dFdx"
        "DFdy"              -> "dFdy"

        -- Vector and Scalar Relational Functions
        "LessThan"          -> ifType isScalarNum "<"  "lessThan"
        "LessThanEqual"     -> ifType isScalarNum "<=" "lessThanEqual"
        "GreaterThan"       -> ifType isScalarNum ">"  "greaterThan"
        "GreaterThanEqual"  -> ifType isScalarNum ">=" "greaterThanEqual"
        "Equal"             -> "=="
        "EqualV"            -> ifType isScalar "==" "equal"
        "NotEqual"          -> "!="
        "NotEqualV"         -> ifType isScalar "!=" "notEqual"

        -- Angle and Trigonometry Functions
        "ATan2"             -> "atan"
        -- Exponential Functions
        "InvSqrt"           -> "inversesqrt"
        -- Common Functions
        "RoundEven"         -> "roundEven"
        "ModF"              -> error "PrimModF is not implemented yet!" -- TODO
        "MixB"              -> "mix"

        n | n `elem`
            -- Logic Functions
            [ "Any", "All"
            -- Angle and Trigonometry Functions
            , "ACos", "ACosH", "ASin", "ASinH", "ATan", "ATanH", "Cos", "CosH", "Degrees", "Radians", "Sin", "SinH", "Tan", "TanH"
            -- Exponential Functions
            , "Pow", "Exp", "Exp2", "Log2", "Sqrt"
            -- Common Functions
            , "IsNan", "IsInf", "Abs", "Sign", "Floor", "Trunc", "Round", "Ceil", "Fract", "Min", "Max", "Mix", "Step", "SmoothStep"
            -- Geometric Functions
            , "Length", "Distance", "Dot", "Cross", "Normalize", "FaceForward", "Reflect", "Refract"
            -- Matrix Functions
            , "Transpose", "Determinant", "Inverse"
            -- Fragment Processing Functions
            , "FWidth"
            -- Noise Functions
            , "Noise1", "Noise2", "Noise3", "Noise4"
            ] -> map toLower n

        _ -> ""

  x -> error $ "GLSL codegen - unsupported expression: " ++ ppShow x
  where
    prefixOp o [a] = text o <+> parens (gen a)
    binOp o [a, b] = parens (gen a) <+> text o <+> parens (gen b)
    functionCall f a = text f <+> parens (hcat $ intersperse "," $ map gen a)

    gen = genGLSLSubst s

isMatrix :: Ty -> Bool
isMatrix (TMat{}) = True
isMatrix _ = False

isIntegral :: Ty -> Bool
isIntegral TWord = True
isIntegral TInt = True
isIntegral (TVec _ TWord) = True
isIntegral (TVec _ TInt) = True
isIntegral _ = False

isScalarNum :: Ty -> Bool
isScalarNum = \case
    TInt -> True
    TWord -> True
    TFloat -> True
    _ -> False

isScalar :: Ty -> Bool
isScalar = isJust . scalarType

scalarType = \case
    TBool  -> Just "b"
    TWord  -> Just "u"
    TInt   -> Just "i"
    TFloat -> Just ""
    _ -> Nothing

vecConName = \case
    TVec n t | is234 n, Just s <- scalarType t -> Just $ s ++ "vec" ++ show n
    t -> Nothing

toGLSLType msg = \case
    TBool  -> "bool"
    TWord  -> "uint"
    TInt   -> "int"
    TFloat -> "float"
    x@(TVec n t) | Just s <- vecConName x -> s
    TMat i j TFloat | is234 i && is234 j -> "mat" ++ if i == j then show i else show i ++ "x" ++ show j
    TTuple []         -> "void"
    t -> error $ "toGLSLType: " ++ msg ++ " " ++ ppShow t

is234 = (`elem` [2,3,4])


--------------------------------------------------------------------------------

data Exp_ a
    = Pi_ Visibility SName a a
    | Lam_ Visibility Pat a a
    | Con_ SName a [a]
    | ELit_ Lit
    | Fun_ SName a [a]
    | App_ a a
    | Var_ SName a
    | TType_
    | Let_ Pat a a
  deriving (Show, Eq, Functor, Foldable, Traversable)

instance PShow Exp where
    pShowPrec p = \case
        Var n t -> text n
        TType -> "Type"
        ELit a -> text $ show a
        Con n t ps -> pApps p (text n) ps
        Fun n t ps -> pApps p (text n) ps
        EApp a b -> pApp p a b
        Lam h n t e -> pParens True $ "\\" <> showVis h <> pShow n </> "->" <+> pShow e
        Pi h n t e -> pParens True $ showVis h <> pShow n </> "->" <+> pShow e
        ELet pat x e -> pParens (p > 0) $ "let" <+> pShow pat </> "=" <+> pShow x </> "in" <+> pShow e
      where
        showVis Visible = ""
        showVis Hidden = "@"

pattern Pi h n a b = Exp (Pi_ h n a b)
pattern Lam h n a b = Exp (Lam_ h n a b)
pattern Con n a b = Exp (Con_ (UntickName n) a b)
pattern ELit a = Exp (ELit_ a)
pattern Fun n a b = Exp (Fun_ (UntickName n) a b)
pattern EApp a b = Exp (App_ a b)
pattern Var a b = Exp (Var_ a b)
pattern TType = Exp TType_
pattern ELet a b c = Exp (Let_ a b c)

pattern UntickName n <- (untick -> n) where UntickName = untick

pattern EString s = ELit (LString s)
pattern EFloat s = ELit (LFloat s)
pattern EInt s = ELit (LInt s)

newtype Exp = Exp (Exp_ Exp)
  deriving (Show, Eq)

makeTE [] = I.EGlobal (error "makeTE - no source") I.initEnv $ error "makeTE"
makeTE ((_, t): vs) = I.EBind2 (I.BLam Visible) t $ makeTE vs

toExp :: I.Exp -> Exp
toExp = flip runReader [] . flip evalStateT freshTypeVars . f
  where
    freshTypeVars = (flip (:) <$> map show [0..] <*> ['a'..'z'])
    newName = gets head <* modify tail
    f x = asks makeTE >>= \te -> f_ te x
    f_ te = \case
        e | isSampler (I.expType_ te e) -> newName >>= \n -> do
            t <- f $ I.expType_ te e
            ELet (PVar t n) <$> f__ e <*> pure (Var n t)
        e -> f__ e
    f__ = \case
        I.Var i -> asks $ fst . (!!! i)
        I.Pi b x (I.downE 0 -> Just y) -> Pi b "" <$> f x <*> f y
        I.Pi b x y -> newName >>= \n -> do
            t <- f x
            Pi b n t <$> local ((Var n t, x):) (f y)
        I.Lam b x y -> newName >>= \n -> do
            t <- f x
            Lam b (PVar t n) t <$> local ((Var n t, x):) (f y)
        I.Con (I.ConName s _ _ t) xs -> Con s <$> f t <*> mapM f xs
        I.TyCon (I.TyConName s _ _ t _ _) xs -> Con s <$> f t <*> mapM f xs
        I.ELit l -> pure $ ELit l
        I.Fun (I.FunName s _ t) xs -> Fun s <$> f t <*> mapM f xs
        I.CaseFun x@(I.CaseFunName _ t _) xs -> Fun (show x) <$> f t <*> mapM f xs
        I.App a b -> EApp <$> f a <*> f b
        I.TType -> pure TType
        I.PMLabel x _ -> f x
        I.FixLabel _ x -> f x
--        I.LabelEnd x -> f x   -- not possible
        z -> error $ "toExp: " ++ show z

    xs !!! i | i < 0 || i >= length xs = error $ show xs ++ " !! " ++ show i
    xs !!! i = xs !! i

isSampler (I.TyCon n _) = show n == "'Sampler"
isSampler _ = False

untick ('\'': s) = s
untick s = s

freeVars :: Exp -> Set.Set SName
freeVars = \case
    Var n _ -> Set.singleton n
    Con _ _ xs -> Set.unions $ map freeVars xs
    ELit _ -> mempty
    Fun _ _ xs -> Set.unions $ map freeVars xs
    EApp a b -> freeVars a `Set.union` freeVars b
    Pi _ n a b -> freeVars a `Set.union` (Set.delete n $ freeVars b)
    Lam _ n a b -> freeVars a `Set.union` (foldr Set.delete (freeVars b) (patVars n))
    TType -> mempty
    ELet n a b -> freeVars a `Set.union` (foldr Set.delete (freeVars b) (patVars n))

type Ty = Exp

tyOf :: Exp -> Ty
tyOf = \case
    Lam h (PVar _ n) t x -> Pi h n t $ tyOf x
    EApp f x -> app (tyOf f) x
    Var _ t -> t
    Pi{} -> TType
    Con _ t xs -> foldl app t xs
    Fun _ t xs -> foldl app t xs
    ELit l -> toExp $ I.litType l
    TType -> TType
    ELet a b c -> tyOf $ EApp (ELam a c) b
    x -> error $ "tyOf: " ++ ppShow x
  where
    app (Pi _ n a b) x = substE n x b

substE n x = \case
    z@(Var n' _) | n' == n -> x
                 | otherwise -> z 
    Pi h n' a b | n == n' -> Pi h n' (substE n x a) b
    Pi h n' a b -> Pi h n' (substE n x a) (substE n x b)
    Lam h n' a b -> Lam h n' (substE n x a) $ if n `elem` patVars n' then b else substE n x b
    Con n' cn xs -> Con n' cn (map (substE n x) xs)
    Fun n' cn xs -> Fun n' cn (map (substE n x) xs)
    TType -> TType
    EApp a b -> app' (substE n x a) (substE n x b)
    z -> error $ "substE: " ++ ppShow z

app' (Lam _ (PVar _ n) _ x) b = substE n b x
app' a b = EApp a b

-------------------------------------------------------------------------------- Exp conversion -- TODO: remove

data Pat
    = PVar Exp SName
    | PTuple [Pat]
    deriving (Eq, Show)

instance PShow Pat where
    pShowPrec p = \case
        PVar t n -> text n
        PTuple ps -> tupled $ map pShow ps

patVars (PVar _ n) = [n]
patVars (PTuple ps) = concatMap patVars ps

patTy (PVar t _) = t
patTy (PTuple ps) = Con ("Tuple" ++ show (length ps)) (tupTy $ length ps) $ map patTy ps

tupTy n = foldr (:~>) TType $ replicate n TType

-- workaround for backward compatibility
etaRed (ELam (PVar _ n) (EApp f (EVar n'))) | n == n' && n `Set.notMember` freeVars f = f
etaRed (ELam (PVar _ n) (Prim3 (tupCaseName -> Just k) _ x (EVar n'))) | n == n' && n `Set.notMember` freeVars x = uncurry (\ps e -> ELam (PTuple ps) e) $ getPats k x
etaRed x = x

tupCaseName "Tuple2Case" = Just 2
tupCaseName "Tuple3Case" = Just 3
tupCaseName "Tuple4Case" = Just 4
tupCaseName "Tuple5Case" = Just 5
tupCaseName "Tuple6Case" = Just 6
tupCaseName "Tuple7Case" = Just 7
tupCaseName _ = Nothing

getPats 0 e = ([], e)
getPats i (ELam p e) = (p:) *** id $ getPats (i-1) e

-------------

pattern EVar n <- Var n _

pattern ELam n b <- Lam Visible n _ b where ELam n b = Lam Visible n (patTy n) b

pattern a :~> b = Pi Visible "" a b
infixr 1 :~>

pattern PrimN n xs <- Fun n t (filterRelevant (n, 0) t -> xs) where PrimN n xs = Fun n (builtinType n) xs
pattern Prim1 n a = PrimN n [a]
pattern Prim2 n a b = PrimN n [a, b]
pattern Prim3 n a b c <- PrimN n [a, b, c]
pattern Prim4 n a b c d <- PrimN n [a, b, c, d]
pattern Prim5 n a b c d e <- PrimN n [a, b, c, d, e]

builtinType = \case
    "Output"    -> TType
    "Bool"      -> TType
    "Float"     -> TType
    "Nat"       -> TType
    "Zero"      -> TNat
    "Succ"      -> TNat :~> TNat
    "String"    -> TType
    "Sampler"   -> TType
    "VecS"      -> TType :~> TNat :~> TType
    n -> error $ "type of " ++ ppShow n

filterRelevant _ _ [] = []
filterRelevant i (Pi h n t t') (x: xs) = (if h == Visible then (x:) else id) $ filterRelevant (id *** (+1) $ i) (substE n x t') xs

pattern AN n xs <- Con n t (filterRelevant (n, 0) t -> xs) where AN n xs = Con n (builtinType n) xs
pattern A0 n = AN n []
pattern A1 n a = AN n [a]
pattern A2 n a b = AN n [a, b]
pattern A3 n a b c <- AN n [a, b, c]
pattern A4 n a b c d <- AN n [a, b, c, d]
pattern A5 n a b c d e <- AN n [a, b, c, d, e]

pattern TCon0 n = A0 n
pattern TCon t n = Con n t []

pattern TUnit  <- A0 "Tuple0"
pattern TBool  = A0 "Bool"
pattern TWord  <- A0 "Word"
pattern TInt   <- A0 "Int"
pattern TNat   = A0 "Nat"
pattern TFloat = A0 "Float"
pattern TString = A0 "String"

pattern Uniform n   <- Prim1 "Uniform" n

pattern Zero = A0 "Zero"
pattern Succ n = A1 "Succ" n

pattern TVec n a = A2 "VecS" a (Nat n)
pattern TMat i j a <- A3 "Mat" (Nat i) (Nat j) a

pattern Nat n <- (fromNat -> Just n) where Nat = toNat

toNat :: Int -> Exp
toNat 0 = Zero
toNat n = Succ (toNat $ n-1)

fromNat :: Exp -> Maybe Int
fromNat Zero = Just 0
fromNat (Succ n) = (1 +) <$> fromNat n
fromNat _ = Nothing

pattern TTuple xs <- (getTuple -> Just xs)
pattern ETuple xs <- (getTuple -> Just xs)

getTuple (AN (tupName -> Just n) xs) | length xs == n = Just xs
getTuple _ = Nothing

tupName = \case
    "Tuple0" -> Just 0
    "Tuple2" -> Just 2
    "Tuple3" -> Just 3
    "Tuple4" -> Just 4
    "Tuple5" -> Just 5
    "Tuple6" -> Just 6
    "Tuple7" -> Just 7
    _ -> Nothing

pattern SwizzProj a b <- (getSwizzProj -> Just (a, b))

getSwizzProj = \case
    Prim2 "swizzscalar" e (getSwizzChar -> Just s) -> Just (e, [s])
    Prim2 "swizzvector" e (AN ((`elem` ["V2","V3","V4"]) -> True) (traverse getSwizzChar -> Just s)) -> Just (e, s)
    _ -> Nothing

getSwizzChar = \case
    A0 "Sx" -> Just 'x'
    A0 "Sy" -> Just 'y'
    A0 "Sz" -> Just 'z'
    A0 "Sw" -> Just 'w'
    _ -> Nothing

outputType = TCon0 "Output"
boolType = TBool
trueExp = TCon TBool "True"

