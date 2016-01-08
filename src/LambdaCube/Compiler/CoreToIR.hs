{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PackageImports #-}
module LambdaCube.Compiler.CoreToIR
    ( compilePipeline
    ) where

import Debug.Trace
import Control.Applicative
import Control.Monad.State
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Vector (Vector,(!))
import qualified Data.Vector as Vector

import LambdaCube.Compiler.Pretty
import LambdaCube.Compiler.CGExp
import LambdaCube.Compiler.CoreToGLSL
import qualified IR as IR
import qualified "lambdacube-ir" Linear as IR

type CG = State IR.Pipeline

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

-- creates names for Samplers
letifySamplers :: Exp -> Exp
letifySamplers = flip evalState 0 . f  where
    f :: Exp -> State Int Exp
    f = \case
        e_@(Exp e) | t == TCon0 "Sampler" -> do
            i <- get
            modify (+1)
            let n = ExpN $ "sampler" ++ show i
            ELet (PVar t n) <$> (Exp <$> traverse f e) <*> pure (TVar t n)
          where t = tyOf e_
        Exp e -> Exp <$> traverse f e

compilePipeline :: Bool -> IR.Backend -> Exp -> IR.Pipeline
compilePipeline doLetifySamplers b e = flip execState (emptyPipeline b) $ do
    (subCmds,cmds) <- getCommands $ letifySamplers e
    modify (\s -> s {IR.commands = Vector.fromList subCmds <> Vector.fromList cmds})

mergeSlot a b = a
  { IR.slotUniforms = IR.slotUniforms a <> IR.slotUniforms b
  , IR.slotStreams  = IR.slotStreams a <> IR.slotStreams b
  , IR.slotPrograms = IR.slotPrograms a <> IR.slotPrograms b
  }

getSlot :: Exp -> CG (IR.Command,[(String,IR.InputType)])
getSlot (A3 "Fetch" (ELit (LString slotName)) prim attrs) = do
  let input = compAttribute attrs
      slot = IR.Slot
        { IR.slotName       = slotName
        , IR.slotUniforms   = mempty
        , IR.slotStreams    = Map.fromList input
        , IR.slotPrimitive  = compFetchPrimitive prim
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
getSlot (A2 "FetchArrays" prim attrs) = do
  let (input,values) = unzip [((name,ty),(name,value)) | (i,(ty,value)) <- zip [0..] (compAttributeValue attrs), let name = "attribute_" ++ show i]
      stream = IR.StreamData
        { IR.streamData       = Map.fromList values
        , IR.streamType       = Map.fromList input
        , IR.streamPrimitive  = compFetchPrimitive prim
        , IR.streamPrograms   = mempty
        }
  sv <- gets IR.streams
  modify (\s -> s {IR.streams = sv <> pure stream})
  return (IR.RenderStream $ length sv,input)
getSlot x = error $ "getSlot: " ++ ppShow x

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
  ELet (PVar _ _) (A3 "Sampler" _ _ (A2 "Texture2D" _ _)) _
    | tyOf e == TSampler -> [e]
  Exp e -> foldMap getRenderTextures e

type SamplerBinding = (IR.UniformName,IR.ImageRef)

getRenderTextureCommands :: Exp -> CG ([SamplerBinding],[IR.Command])
getRenderTextureCommands e = (\f -> foldM (\(a,b) x -> f x >>= (\(c,d) -> return (c:a,d ++ b))) mempty (getRenderTextures e)) $ \case
  ELet (PVar t n) (A3 "Sampler" _ _ (A2 "Texture2D" (A2 "V2" (ELit (LInt w)) (ELit (LInt h))) (A1 "PrjImageColor" a))) _ -> do
    rt <- newTextureTarget (fromIntegral w) (fromIntegral h) (tyOf a)
    tv <- gets IR.targets
    let IR.RenderTarget (Vector.toList -> [_,IR.TargetItem IR.Color (Just (IR.TextureImage texture _ _))]) = tv ! rt
    (subCmds,cmds) <- getCommands a
    return ((showN n,IR.TextureImage texture 0 Nothing), subCmds <> (IR.SetRenderTarget rt:cmds))
  ELet (PVar t n) (A3 "Sampler" _ _ (A2 "Texture2D" (A2 "V2" (ELit (LInt w)) (ELit (LInt h))) (A1 "PrjImage" a))) _ -> do
    rt <- newTextureTarget (fromIntegral w) (fromIntegral h) (tyOf a)
    tv <- gets IR.targets
    let IR.RenderTarget (Vector.toList -> [IR.TargetItem IR.Color (Just (IR.TextureImage texture _ _))]) = tv ! rt
    (subCmds,cmds) <- getCommands a
    return ((showN n,IR.TextureImage texture 0 Nothing), subCmds <> (IR.SetRenderTarget rt:cmds))
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
  ELet (PVar _ _) (A3 "Sampler" _ _ (A1 "Texture2DSlot" (ELString s))) _ -> Set.singleton (s, IR.FTexture2D{-compInputType $ tyOf e-}) -- TODO
  ELet (PVar _ n) (A3 "Sampler" _ _ (A2 "Texture2D" _ _)) _ -> Set.singleton ((n, IR.FTexture2D))
  Exp e -> foldMap getSamplerUniforms e

getUniforms :: Exp -> Set (String,IR.InputType)
getUniforms e = case e of
  Uniform (ELString s) -> Set.singleton (s, compInputType $ tyOf e)
  ELet (PVar _ _) (A3 "Sampler" _ _ (A1 "Texture2DSlot" (ELString s))) _ -> Set.singleton (s, IR.FTexture2D{-compInputType $ tyOf e-}) -- TODO
  ELet (PVar _ _) (A3 "Sampler" _ _ (A2 "Texture2D" _ _)) _ -> mempty
  Exp e -> foldMap getUniforms e

compFrameBuffer x = case x of
  ETuple a -> concatMap compFrameBuffer a
  A1 "DepthImage" a -> [(IR.Depth, compValue a)]
  A1 "ColorImage" a -> [(IR.Color, compValue a)]
  x -> error $ "compFrameBuffer " ++ ppShow x

compSemantic x = case x of
  TTuple t  -> concatMap compSemantic t
  Depth _   -> return IR.Depth
  Stencil _ -> return IR.Stencil
  Color _   -> return IR.Color
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
  Attribute (ELString s) -> [(s, compInputType $ tyOf x)]
  x -> error $ "compAttribute " ++ ppShow x

compAttributeValue :: Exp -> [(IR.InputType,IR.ArrayValue)]
compAttributeValue x = let
    compList (A2 "Cons" a x) = compValue a : compList x
    compList (A0 "Nil") = []
    compList x = error $ "compList: " ++ show x
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
      a -> let TList (compInputType -> t) = tyOf a
               values = compList a
           in
            [(length values,(t,foldr (flatten t) (emptyArray t) values))]
  in checkLength $ go x

compFetchPrimitive x = case x of
  A0 "Points" -> IR.Points
  A0 "Lines" -> IR.Lines
  A0 "Triangles" -> IR.Triangles
  A0 "LinesAdjacency" -> IR.LinesAdjacency
  A0 "TrianglesAdjacency" -> IR.TrianglesAdjacency
  x -> error $ "compFetchPrimitive " ++ ppShow x

compValue x = case x of
  ELit (LFloat a) -> IR.VFloat $ realToFrac a
  ELit (LInt a) -> IR.VInt $ fromIntegral a
  A2 "V2" (ELit (LFloat a)) (ELit (LFloat b)) -> IR.VV2F $ IR.V2 (realToFrac a) (realToFrac b)
  A3 "V3" (ELit (LFloat a)) (ELit (LFloat b)) (ELit (LFloat c)) -> IR.VV3F $ IR.V3 (realToFrac a) (realToFrac b) (realToFrac c)
  A4 "V4" (ELit (LFloat a)) (ELit (LFloat b)) (ELit (LFloat c)) (ELit (LFloat d)) -> IR.VV4F $ IR.V4 (realToFrac a) (realToFrac b) (realToFrac c) (realToFrac d)
  A2 "V2" (compBool -> a) (compBool -> b) -> IR.VV2B $ IR.V2 a b
  A3 "V3" (compBool -> a) (compBool -> b) (compBool -> c) -> IR.VV3B $ IR.V3 a b c
  A4 "V4" (compBool -> a) (compBool -> b) (compBool -> c) (compBool -> d) -> IR.VV4B $ IR.V4 a b c d
  x -> error $ "compValue " ++ ppShow x

compRC x = case x of
  A3 "PointCtx" a (ELit (LFloat b)) c -> IR.PointCtx (compPS a) (realToFrac b) (compPSCO c)
  A2 "LineCtx" (ELit (LFloat a)) b -> IR.LineCtx (realToFrac a) (compPV b)
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
  A1 "PolygonLine" (ELit (LFloat a)) -> IR.PolygonLine $ realToFrac a
  A1 "PolygonPoint" a  -> IR.PolygonPoint $ compPS a
  x -> error $ "compPM " ++ ppShow x

compPS x = case x of
  A1 "PointSize" (ELit (LFloat a)) -> IR.PointSize $ realToFrac a
  A0 "ProgramPointSize" -> IR.ProgramPointSize
  x -> error $ "compPS " ++ ppShow x

compPO x = case x of
  A2 "Offset" (ELit (LFloat a)) (ELit (LFloat b)) -> IR.Offset (realToFrac a) (realToFrac b)
  A0 "NoOffset" -> IR.NoOffset
  x -> error $ "compPO " ++ ppShow x

compPV x = case x of
    A0 "FirstVertex" -> IR.FirstVertex
    A0 "LastVertex" -> IR.LastVertex
    x -> error $ "compPV " ++ ppShow x
