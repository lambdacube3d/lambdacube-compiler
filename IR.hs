-- generated file, do not modify!
-- 2015-08-28T15:35:15.972Z

module IR where

import Data.Int
import Data.Word
import Data.Map
import Linear

type StreamName = Int

type ProgramName = Int

type TextureName = Int

type SamplerName = Int

type UniformName = String

type SlotName = Int

type FrameBufferComponent = Int

type TextureUnit = Int

type RenderTargetName = Int

type TextureUnitMapping = Map UniformName TextureUnit

data ArrayValue
  = VBoolArray [Bool]
  | VIntArray [Int32]
  | VWordArray [Word32]
  | VFloatArray [Float]
  deriving (Show, Eq, Ord)

data Value
  = VBool Bool
  | VV2B V2B
  | VV3B V3B
  | VV4B V4B
  | VWord Word32
  | VV2U V2U
  | VV3U V3U
  | VV4U V4U
  | VInt Int32
  | VV2I V2I
  | VV3I V3I
  | VV4I V4I
  | VFloat Float
  | VV2F V2F
  | VV3F V3F
  | VV4F V4F
  | VM22F M22F
  | VM23F M23F
  | VM24F M24F
  | VM32F M32F
  | VM33F M33F
  | VM34F M34F
  | VM42F M42F
  | VM43F M43F
  | VM44F M44F
  deriving (Show, Eq, Ord)

data InputType
  = Bool
  | V2B
  | V3B
  | V4B
  | Word
  | V2U
  | V3U
  | V4U
  | Int
  | V2I
  | V3I
  | V4I
  | Float
  | V2F
  | V3F
  | V4F
  | M22F
  | M23F
  | M24F
  | M32F
  | M33F
  | M34F
  | M42F
  | M43F
  | M44F
  | STexture1D
  | STexture2D
  | STextureCube
  | STexture1DArray
  | STexture2DArray
  | STexture2DRect
  | FTexture1D
  | FTexture2D
  | FTexture3D
  | FTextureCube
  | FTexture1DArray
  | FTexture2DArray
  | FTexture2DMS
  | FTexture2DMSArray
  | FTextureBuffer
  | FTexture2DRect
  | ITexture1D
  | ITexture2D
  | ITexture3D
  | ITextureCube
  | ITexture1DArray
  | ITexture2DArray
  | ITexture2DMS
  | ITexture2DMSArray
  | ITextureBuffer
  | ITexture2DRect
  | UTexture1D
  | UTexture2D
  | UTexture3D
  | UTextureCube
  | UTexture1DArray
  | UTexture2DArray
  | UTexture2DMS
  | UTexture2DMSArray
  | UTextureBuffer
  | UTexture2DRect
  deriving (Show, Eq, Ord)

data PointSpriteCoordOrigin
  = LowerLeft
  | UpperLeft
  deriving (Show, Eq, Ord)

data PointSize
  = PointSize Float
  | ProgramPointSize
  deriving (Show, Eq, Ord)

data PolygonOffset
  = NoOffset
  | Offset Float Float
  deriving (Show, Eq, Ord)

data FrontFace
  = CCW
  | CW
  deriving (Show, Eq, Ord)

data PolygonMode
  = PolygonPoint PointSize
  | PolygonLine Float
  | PolygonFill
  deriving (Show, Eq, Ord)

data ProvokingVertex
  = FirstVertex
  | LastVertex
  deriving (Show, Eq, Ord)

data CullMode
  = CullNone
  | CullFront FrontFace
  | CullBack FrontFace
  deriving (Show, Eq, Ord)

data ComparisonFunction
  = Never
  | Less
  | Equal
  | Lequal
  | Greater
  | Notequal
  | Gequal
  | Always
  deriving (Show, Eq, Ord)

type DepthFunction = ComparisonFunction

data StencilOperation
  = OpZero
  | OpKeep
  | OpReplace
  | OpIncr
  | OpIncrWrap
  | OpDecr
  | OpDecrWrap
  | OpInvert
  deriving (Show, Eq, Ord)

data BlendEquation
  = FuncAdd
  | FuncSubtract
  | FuncReverseSubtract
  | Min
  | Max
  deriving (Show, Eq, Ord)

data BlendingFactor
  = Zero
  | One
  | SrcColor
  | OneMinusSrcColor
  | DstColor
  | OneMinusDstColor
  | SrcAlpha
  | OneMinusSrcAlpha
  | DstAlpha
  | OneMinusDstAlpha
  | ConstantColor
  | OneMinusConstantColor
  | ConstantAlpha
  | OneMinusConstantAlpha
  | SrcAlphaSaturate
  deriving (Show, Eq, Ord)

data LogicOperation
  = Clear
  | And
  | AndReverse
  | Copy
  | AndInverted
  | Noop
  | Xor
  | Or
  | Nor
  | Equiv
  | Invert
  | OrReverse
  | CopyInverted
  | OrInverted
  | Nand
  | Set
  deriving (Show, Eq, Ord)

data StencilOps
  = StencilOps
  { frontStencilOp :: StencilOperation
  , backStencilOp :: StencilOperation
  }

  deriving (Show, Eq, Ord)

data StencilTests
  = StencilTests StencilTest StencilTest
  deriving (Show, Eq, Ord)

data StencilTest
  = StencilTest
  { stencilComparision :: ComparisonFunction
  , stencilReference :: Int32
  , stencilMask :: Word32
  }

  deriving (Show, Eq, Ord)

data FetchPrimitive
  = Points
  | Lines
  | Triangles
  | LinesAdjacency
  | TrianglesAdjacency
  deriving (Show, Eq, Ord)

data OutputPrimitive
  = TrianglesOutput
  | LinesOutput
  | PointsOutput
  deriving (Show, Eq, Ord)

data ColorArity
  = Red
  | RG
  | RGB
  | RGBA
  deriving (Show, Eq, Ord)

data Blending
  = NoBlending
  | BlendLogicOp LogicOperation
  | Blend (BlendEquation,BlendEquation) ((BlendingFactor,BlendingFactor),(BlendingFactor,BlendingFactor)) V4F
  deriving (Show, Eq, Ord)

data RasterContext
  = PointCtx PointSize Float PointSpriteCoordOrigin
  | LineCtx Float ProvokingVertex
  | TriangleCtx CullMode PolygonMode PolygonOffset ProvokingVertex
  deriving (Show, Eq, Ord)

data FragmentOperation
  = DepthOp DepthFunction Bool
  | StencilOp StencilTests StencilOps StencilOps
  | ColorOp Blending Value
  deriving (Show, Eq, Ord)

data AccumulationContext
  = AccumulationContext
  { accViewportName :: Maybe String
  , accOperations :: [FragmentOperation]
  }

  deriving (Show, Eq, Ord)

data TextureDataType
  = FloatT ColorArity
  | IntT ColorArity
  | WordT ColorArity
  | ShadowT
  deriving (Show, Eq, Ord)

data TextureType
  = Texture1D TextureDataType Int
  | Texture2D TextureDataType Int
  | Texture3D TextureDataType
  | TextureCube TextureDataType
  | TextureRect TextureDataType
  | Texture2DMS TextureDataType Int Int Bool
  | TextureBuffer TextureDataType
  deriving (Show, Eq, Ord)

data MipMap
  = Mip Int Int
  | NoMip
  | AutoMip Int Int
  deriving (Show, Eq, Ord)

data Filter
  = Nearest
  | Linear
  | NearestMipmapNearest
  | NearestMipmapLinear
  | LinearMipmapNearest
  | LinearMipmapLinear
  deriving (Show, Eq, Ord)

data EdgeMode
  = Repeat
  | MirroredRepeat
  | ClampToEdge
  | ClampToBorder
  deriving (Show, Eq, Ord)

data ImageRef
  = TextureImage TextureName Int (Maybe Int)
  | Framebuffer ImageSemantic
  deriving (Show, Eq, Ord)

data ImageSemantic
  = Depth
  | Stencil
  | Color
  deriving (Show, Eq, Ord)

data Command
  = SetRasterContext RasterContext
  | SetAccumulationContext AccumulationContext
  | SetRenderTarget RenderTargetName
  | SetProgram ProgramName
  | SetSamplerUniform UniformName TextureUnit
  | SetTexture TextureUnit TextureName
  | SetSampler TextureUnit (Maybe SamplerName)
  | RenderSlot SlotName
  | RenderStream StreamName
  | ClearRenderTarget [(ImageSemantic,Value)]
  | GenerateMipMap TextureUnit
  | SaveImage FrameBufferComponent ImageRef
  | LoadImage ImageRef FrameBufferComponent
  deriving (Show, Eq, Ord)

data TextureDescriptor
  = TextureDescriptor
  { textureType :: TextureType
  , textureSize :: Value
  , textureSemantic :: ImageSemantic
  , textureSampler :: SamplerDescriptor
  , textureBaseLevel :: Int
  , textureMaxLevel :: Int
  }

  deriving (Show, Eq, Ord)

data SamplerDescriptor
  = SamplerDescriptor
  { samplerWrapS :: EdgeMode
  , samplerWrapT :: Maybe EdgeMode
  , samplerWrapR :: Maybe EdgeMode
  , samplerMinFilter :: Filter
  , samplerMagFilter :: Filter
  , samplerBorderColor :: Value
  , samplerMinLod :: Maybe Float
  , samplerMaxLod :: Maybe Float
  , samplerLodBias :: Float
  , samplerCompareFunc :: Maybe ComparisonFunction
  }

  deriving (Show, Eq, Ord)

data Program
  = Program
  { programUniforms :: Map UniformName InputType
  , programStreams :: Map UniformName (String,InputType)
  , programInTextures :: Map UniformName InputType
  , programOutput :: [(String,InputType)]
  , vertexShader :: String
  , geometryShader :: Maybe String
  , fragmentShader :: String
  }

  deriving (Show, Eq, Ord)

data Slot
  = Slot
  { slotName :: String
  , slotStreams :: Map String InputType
  , slotUniforms :: Map UniformName InputType
  , slotPrimitive :: FetchPrimitive
  , slotPrograms :: [ProgramName]
  }

  deriving (Show, Eq, Ord)

data StreamData
  = StreamData
  { streamData :: Map String ArrayValue
  , streamType :: Map String InputType
  , streamPrimitive :: FetchPrimitive
  , streamPrograms :: [ProgramName]
  }

  deriving (Show, Eq, Ord)

data RenderTarget
  = RenderTarget
  { renderTargets :: [(ImageSemantic,Maybe ImageRef)]
  }

  deriving (Show, Eq, Ord)

data Backend
  = WebGL1
  | OpenGL33
  deriving (Show, Eq, Ord)

data Pipeline
  = Pipeline
  { backend :: Backend
  , textures :: [TextureDescriptor]
  , samplers :: [SamplerDescriptor]
  , targets :: [RenderTarget]
  , programs :: [Program]
  , slots :: [Slot]
  , streams :: [StreamData]
  , commands :: [Command]
  }

  deriving (Show, Eq, Ord)

