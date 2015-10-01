-- generated file, do not modify!
-- 2015-09-15T22:39:08.045384000000Z

{-# LANGUAGE OverloadedStrings, RecordWildCards #-}
module IR where

import Data.Int
import Data.Word
import Data.Map
import Data.Vector (Vector(..))
import Linear

import Data.Text
import Data.Aeson hiding (Value,Bool)
import Data.Aeson.Types hiding (Value,Bool)
import Control.Monad


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
  = VBoolArray (Vector Bool)
  | VIntArray (Vector Int32)
  | VWordArray (Vector Word32)
  | VFloatArray (Vector Float)
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

data StencilTest
  = StencilTest
  { stencilComparision :: ComparisonFunction
  , stencilReference :: Int32
  , stencilMask :: Word32
  }

  deriving (Show, Eq, Ord)

data StencilTests
  = StencilTests StencilTest StencilTest
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
  | Blend
  { colorEqSrc :: BlendEquation
  , alphaEqSrc :: BlendEquation
  , colorFSrc :: BlendingFactor
  , colorFDst :: BlendingFactor
  , alphaFSrc :: BlendingFactor
  , alphaFDst :: BlendingFactor
  , color :: V4F
  }

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

data ImageSemantic
  = Depth
  | Stencil
  | Color
  deriving (Show, Eq, Ord)

data ImageRef
  = TextureImage TextureName Int (Maybe Int)
  | Framebuffer ImageSemantic
  deriving (Show, Eq, Ord)

data ClearImage
  = ClearImage
  { imageSemantic :: ImageSemantic
  , clearValue :: Value
  }

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
  | ClearRenderTarget (Vector ClearImage)
  | GenerateMipMap TextureUnit
  | SaveImage FrameBufferComponent ImageRef
  | LoadImage ImageRef FrameBufferComponent
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

data Parameter
  = Parameter
  { name :: String
  , ty :: InputType
  }

  deriving (Show, Eq, Ord)

data Program
  = Program
  { programUniforms :: Map UniformName InputType
  , programStreams :: Map UniformName Parameter
  , programInTextures :: Map UniformName InputType
  , programOutput :: Vector Parameter
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
  , slotPrograms :: Vector ProgramName
  }

  deriving (Show, Eq, Ord)

data StreamData
  = StreamData
  { streamData :: Map String ArrayValue
  , streamType :: Map String InputType
  , streamPrimitive :: FetchPrimitive
  , streamPrograms :: Vector ProgramName
  }

  deriving (Show, Eq, Ord)

data TargetItem
  = TargetItem
  { targetSemantic :: ImageSemantic
  , targetRef :: Maybe ImageRef
  }

  deriving (Show, Eq, Ord)

data RenderTarget
  = RenderTarget
  { renderTargets :: Vector TargetItem
  }

  deriving (Show, Eq, Ord)

data Backend
  = WebGL1
  | OpenGL33
  deriving (Show, Eq, Ord)

data Pipeline
  = Pipeline
  { backend :: Backend
  , textures :: Vector TextureDescriptor
  , samplers :: Vector SamplerDescriptor
  , targets :: Vector RenderTarget
  , programs :: Vector Program
  , slots :: Vector Slot
  , streams :: Vector StreamData
  , commands :: Vector Command
  }

  deriving (Show, Eq, Ord)


instance ToJSON ArrayValue where
  toJSON v = case v of
    VBoolArray arg0 -> object [ "tag" .= ("VBoolArray" :: Text), "arg0" .= arg0]
    VIntArray arg0 -> object [ "tag" .= ("VIntArray" :: Text), "arg0" .= arg0]
    VWordArray arg0 -> object [ "tag" .= ("VWordArray" :: Text), "arg0" .= arg0]
    VFloatArray arg0 -> object [ "tag" .= ("VFloatArray" :: Text), "arg0" .= arg0]

instance FromJSON ArrayValue where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "VBoolArray" -> VBoolArray <$> obj .: "arg0"
      "VIntArray" -> VIntArray <$> obj .: "arg0"
      "VWordArray" -> VWordArray <$> obj .: "arg0"
      "VFloatArray" -> VFloatArray <$> obj .: "arg0"
  parseJSON _ = mzero

instance ToJSON Value where
  toJSON v = case v of
    VBool arg0 -> object [ "tag" .= ("VBool" :: Text), "arg0" .= arg0]
    VV2B arg0 -> object [ "tag" .= ("VV2B" :: Text), "arg0" .= arg0]
    VV3B arg0 -> object [ "tag" .= ("VV3B" :: Text), "arg0" .= arg0]
    VV4B arg0 -> object [ "tag" .= ("VV4B" :: Text), "arg0" .= arg0]
    VWord arg0 -> object [ "tag" .= ("VWord" :: Text), "arg0" .= arg0]
    VV2U arg0 -> object [ "tag" .= ("VV2U" :: Text), "arg0" .= arg0]
    VV3U arg0 -> object [ "tag" .= ("VV3U" :: Text), "arg0" .= arg0]
    VV4U arg0 -> object [ "tag" .= ("VV4U" :: Text), "arg0" .= arg0]
    VInt arg0 -> object [ "tag" .= ("VInt" :: Text), "arg0" .= arg0]
    VV2I arg0 -> object [ "tag" .= ("VV2I" :: Text), "arg0" .= arg0]
    VV3I arg0 -> object [ "tag" .= ("VV3I" :: Text), "arg0" .= arg0]
    VV4I arg0 -> object [ "tag" .= ("VV4I" :: Text), "arg0" .= arg0]
    VFloat arg0 -> object [ "tag" .= ("VFloat" :: Text), "arg0" .= arg0]
    VV2F arg0 -> object [ "tag" .= ("VV2F" :: Text), "arg0" .= arg0]
    VV3F arg0 -> object [ "tag" .= ("VV3F" :: Text), "arg0" .= arg0]
    VV4F arg0 -> object [ "tag" .= ("VV4F" :: Text), "arg0" .= arg0]
    VM22F arg0 -> object [ "tag" .= ("VM22F" :: Text), "arg0" .= arg0]
    VM23F arg0 -> object [ "tag" .= ("VM23F" :: Text), "arg0" .= arg0]
    VM24F arg0 -> object [ "tag" .= ("VM24F" :: Text), "arg0" .= arg0]
    VM32F arg0 -> object [ "tag" .= ("VM32F" :: Text), "arg0" .= arg0]
    VM33F arg0 -> object [ "tag" .= ("VM33F" :: Text), "arg0" .= arg0]
    VM34F arg0 -> object [ "tag" .= ("VM34F" :: Text), "arg0" .= arg0]
    VM42F arg0 -> object [ "tag" .= ("VM42F" :: Text), "arg0" .= arg0]
    VM43F arg0 -> object [ "tag" .= ("VM43F" :: Text), "arg0" .= arg0]
    VM44F arg0 -> object [ "tag" .= ("VM44F" :: Text), "arg0" .= arg0]

instance FromJSON Value where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "VBool" -> VBool <$> obj .: "arg0"
      "VV2B" -> VV2B <$> obj .: "arg0"
      "VV3B" -> VV3B <$> obj .: "arg0"
      "VV4B" -> VV4B <$> obj .: "arg0"
      "VWord" -> VWord <$> obj .: "arg0"
      "VV2U" -> VV2U <$> obj .: "arg0"
      "VV3U" -> VV3U <$> obj .: "arg0"
      "VV4U" -> VV4U <$> obj .: "arg0"
      "VInt" -> VInt <$> obj .: "arg0"
      "VV2I" -> VV2I <$> obj .: "arg0"
      "VV3I" -> VV3I <$> obj .: "arg0"
      "VV4I" -> VV4I <$> obj .: "arg0"
      "VFloat" -> VFloat <$> obj .: "arg0"
      "VV2F" -> VV2F <$> obj .: "arg0"
      "VV3F" -> VV3F <$> obj .: "arg0"
      "VV4F" -> VV4F <$> obj .: "arg0"
      "VM22F" -> VM22F <$> obj .: "arg0"
      "VM23F" -> VM23F <$> obj .: "arg0"
      "VM24F" -> VM24F <$> obj .: "arg0"
      "VM32F" -> VM32F <$> obj .: "arg0"
      "VM33F" -> VM33F <$> obj .: "arg0"
      "VM34F" -> VM34F <$> obj .: "arg0"
      "VM42F" -> VM42F <$> obj .: "arg0"
      "VM43F" -> VM43F <$> obj .: "arg0"
      "VM44F" -> VM44F <$> obj .: "arg0"
  parseJSON _ = mzero

instance ToJSON InputType where
  toJSON v = case v of
    Bool -> object [ "tag" .= ("Bool" :: Text)]
    V2B -> object [ "tag" .= ("V2B" :: Text)]
    V3B -> object [ "tag" .= ("V3B" :: Text)]
    V4B -> object [ "tag" .= ("V4B" :: Text)]
    Word -> object [ "tag" .= ("Word" :: Text)]
    V2U -> object [ "tag" .= ("V2U" :: Text)]
    V3U -> object [ "tag" .= ("V3U" :: Text)]
    V4U -> object [ "tag" .= ("V4U" :: Text)]
    Int -> object [ "tag" .= ("Int" :: Text)]
    V2I -> object [ "tag" .= ("V2I" :: Text)]
    V3I -> object [ "tag" .= ("V3I" :: Text)]
    V4I -> object [ "tag" .= ("V4I" :: Text)]
    Float -> object [ "tag" .= ("Float" :: Text)]
    V2F -> object [ "tag" .= ("V2F" :: Text)]
    V3F -> object [ "tag" .= ("V3F" :: Text)]
    V4F -> object [ "tag" .= ("V4F" :: Text)]
    M22F -> object [ "tag" .= ("M22F" :: Text)]
    M23F -> object [ "tag" .= ("M23F" :: Text)]
    M24F -> object [ "tag" .= ("M24F" :: Text)]
    M32F -> object [ "tag" .= ("M32F" :: Text)]
    M33F -> object [ "tag" .= ("M33F" :: Text)]
    M34F -> object [ "tag" .= ("M34F" :: Text)]
    M42F -> object [ "tag" .= ("M42F" :: Text)]
    M43F -> object [ "tag" .= ("M43F" :: Text)]
    M44F -> object [ "tag" .= ("M44F" :: Text)]
    STexture1D -> object [ "tag" .= ("STexture1D" :: Text)]
    STexture2D -> object [ "tag" .= ("STexture2D" :: Text)]
    STextureCube -> object [ "tag" .= ("STextureCube" :: Text)]
    STexture1DArray -> object [ "tag" .= ("STexture1DArray" :: Text)]
    STexture2DArray -> object [ "tag" .= ("STexture2DArray" :: Text)]
    STexture2DRect -> object [ "tag" .= ("STexture2DRect" :: Text)]
    FTexture1D -> object [ "tag" .= ("FTexture1D" :: Text)]
    FTexture2D -> object [ "tag" .= ("FTexture2D" :: Text)]
    FTexture3D -> object [ "tag" .= ("FTexture3D" :: Text)]
    FTextureCube -> object [ "tag" .= ("FTextureCube" :: Text)]
    FTexture1DArray -> object [ "tag" .= ("FTexture1DArray" :: Text)]
    FTexture2DArray -> object [ "tag" .= ("FTexture2DArray" :: Text)]
    FTexture2DMS -> object [ "tag" .= ("FTexture2DMS" :: Text)]
    FTexture2DMSArray -> object [ "tag" .= ("FTexture2DMSArray" :: Text)]
    FTextureBuffer -> object [ "tag" .= ("FTextureBuffer" :: Text)]
    FTexture2DRect -> object [ "tag" .= ("FTexture2DRect" :: Text)]
    ITexture1D -> object [ "tag" .= ("ITexture1D" :: Text)]
    ITexture2D -> object [ "tag" .= ("ITexture2D" :: Text)]
    ITexture3D -> object [ "tag" .= ("ITexture3D" :: Text)]
    ITextureCube -> object [ "tag" .= ("ITextureCube" :: Text)]
    ITexture1DArray -> object [ "tag" .= ("ITexture1DArray" :: Text)]
    ITexture2DArray -> object [ "tag" .= ("ITexture2DArray" :: Text)]
    ITexture2DMS -> object [ "tag" .= ("ITexture2DMS" :: Text)]
    ITexture2DMSArray -> object [ "tag" .= ("ITexture2DMSArray" :: Text)]
    ITextureBuffer -> object [ "tag" .= ("ITextureBuffer" :: Text)]
    ITexture2DRect -> object [ "tag" .= ("ITexture2DRect" :: Text)]
    UTexture1D -> object [ "tag" .= ("UTexture1D" :: Text)]
    UTexture2D -> object [ "tag" .= ("UTexture2D" :: Text)]
    UTexture3D -> object [ "tag" .= ("UTexture3D" :: Text)]
    UTextureCube -> object [ "tag" .= ("UTextureCube" :: Text)]
    UTexture1DArray -> object [ "tag" .= ("UTexture1DArray" :: Text)]
    UTexture2DArray -> object [ "tag" .= ("UTexture2DArray" :: Text)]
    UTexture2DMS -> object [ "tag" .= ("UTexture2DMS" :: Text)]
    UTexture2DMSArray -> object [ "tag" .= ("UTexture2DMSArray" :: Text)]
    UTextureBuffer -> object [ "tag" .= ("UTextureBuffer" :: Text)]
    UTexture2DRect -> object [ "tag" .= ("UTexture2DRect" :: Text)]

instance FromJSON InputType where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "Bool" -> pure Bool
      "V2B" -> pure V2B
      "V3B" -> pure V3B
      "V4B" -> pure V4B
      "Word" -> pure Word
      "V2U" -> pure V2U
      "V3U" -> pure V3U
      "V4U" -> pure V4U
      "Int" -> pure Int
      "V2I" -> pure V2I
      "V3I" -> pure V3I
      "V4I" -> pure V4I
      "Float" -> pure Float
      "V2F" -> pure V2F
      "V3F" -> pure V3F
      "V4F" -> pure V4F
      "M22F" -> pure M22F
      "M23F" -> pure M23F
      "M24F" -> pure M24F
      "M32F" -> pure M32F
      "M33F" -> pure M33F
      "M34F" -> pure M34F
      "M42F" -> pure M42F
      "M43F" -> pure M43F
      "M44F" -> pure M44F
      "STexture1D" -> pure STexture1D
      "STexture2D" -> pure STexture2D
      "STextureCube" -> pure STextureCube
      "STexture1DArray" -> pure STexture1DArray
      "STexture2DArray" -> pure STexture2DArray
      "STexture2DRect" -> pure STexture2DRect
      "FTexture1D" -> pure FTexture1D
      "FTexture2D" -> pure FTexture2D
      "FTexture3D" -> pure FTexture3D
      "FTextureCube" -> pure FTextureCube
      "FTexture1DArray" -> pure FTexture1DArray
      "FTexture2DArray" -> pure FTexture2DArray
      "FTexture2DMS" -> pure FTexture2DMS
      "FTexture2DMSArray" -> pure FTexture2DMSArray
      "FTextureBuffer" -> pure FTextureBuffer
      "FTexture2DRect" -> pure FTexture2DRect
      "ITexture1D" -> pure ITexture1D
      "ITexture2D" -> pure ITexture2D
      "ITexture3D" -> pure ITexture3D
      "ITextureCube" -> pure ITextureCube
      "ITexture1DArray" -> pure ITexture1DArray
      "ITexture2DArray" -> pure ITexture2DArray
      "ITexture2DMS" -> pure ITexture2DMS
      "ITexture2DMSArray" -> pure ITexture2DMSArray
      "ITextureBuffer" -> pure ITextureBuffer
      "ITexture2DRect" -> pure ITexture2DRect
      "UTexture1D" -> pure UTexture1D
      "UTexture2D" -> pure UTexture2D
      "UTexture3D" -> pure UTexture3D
      "UTextureCube" -> pure UTextureCube
      "UTexture1DArray" -> pure UTexture1DArray
      "UTexture2DArray" -> pure UTexture2DArray
      "UTexture2DMS" -> pure UTexture2DMS
      "UTexture2DMSArray" -> pure UTexture2DMSArray
      "UTextureBuffer" -> pure UTextureBuffer
      "UTexture2DRect" -> pure UTexture2DRect
  parseJSON _ = mzero

instance ToJSON PointSpriteCoordOrigin where
  toJSON v = case v of
    LowerLeft -> object [ "tag" .= ("LowerLeft" :: Text)]
    UpperLeft -> object [ "tag" .= ("UpperLeft" :: Text)]

instance FromJSON PointSpriteCoordOrigin where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "LowerLeft" -> pure LowerLeft
      "UpperLeft" -> pure UpperLeft
  parseJSON _ = mzero

instance ToJSON PointSize where
  toJSON v = case v of
    PointSize arg0 -> object [ "tag" .= ("PointSize" :: Text), "arg0" .= arg0]
    ProgramPointSize -> object [ "tag" .= ("ProgramPointSize" :: Text)]

instance FromJSON PointSize where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "PointSize" -> PointSize <$> obj .: "arg0"
      "ProgramPointSize" -> pure ProgramPointSize
  parseJSON _ = mzero

instance ToJSON PolygonOffset where
  toJSON v = case v of
    NoOffset -> object [ "tag" .= ("NoOffset" :: Text)]
    Offset arg0 arg1 -> object [ "tag" .= ("Offset" :: Text), "arg0" .= arg0, "arg1" .= arg1]

instance FromJSON PolygonOffset where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "NoOffset" -> pure NoOffset
      "Offset" -> Offset <$> obj .: "arg0" <*> obj .: "arg1"
  parseJSON _ = mzero

instance ToJSON FrontFace where
  toJSON v = case v of
    CCW -> object [ "tag" .= ("CCW" :: Text)]
    CW -> object [ "tag" .= ("CW" :: Text)]

instance FromJSON FrontFace where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "CCW" -> pure CCW
      "CW" -> pure CW
  parseJSON _ = mzero

instance ToJSON PolygonMode where
  toJSON v = case v of
    PolygonPoint arg0 -> object [ "tag" .= ("PolygonPoint" :: Text), "arg0" .= arg0]
    PolygonLine arg0 -> object [ "tag" .= ("PolygonLine" :: Text), "arg0" .= arg0]
    PolygonFill -> object [ "tag" .= ("PolygonFill" :: Text)]

instance FromJSON PolygonMode where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "PolygonPoint" -> PolygonPoint <$> obj .: "arg0"
      "PolygonLine" -> PolygonLine <$> obj .: "arg0"
      "PolygonFill" -> pure PolygonFill
  parseJSON _ = mzero

instance ToJSON ProvokingVertex where
  toJSON v = case v of
    FirstVertex -> object [ "tag" .= ("FirstVertex" :: Text)]
    LastVertex -> object [ "tag" .= ("LastVertex" :: Text)]

instance FromJSON ProvokingVertex where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "FirstVertex" -> pure FirstVertex
      "LastVertex" -> pure LastVertex
  parseJSON _ = mzero

instance ToJSON CullMode where
  toJSON v = case v of
    CullNone -> object [ "tag" .= ("CullNone" :: Text)]
    CullFront arg0 -> object [ "tag" .= ("CullFront" :: Text), "arg0" .= arg0]
    CullBack arg0 -> object [ "tag" .= ("CullBack" :: Text), "arg0" .= arg0]

instance FromJSON CullMode where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "CullNone" -> pure CullNone
      "CullFront" -> CullFront <$> obj .: "arg0"
      "CullBack" -> CullBack <$> obj .: "arg0"
  parseJSON _ = mzero

instance ToJSON ComparisonFunction where
  toJSON v = case v of
    Never -> object [ "tag" .= ("Never" :: Text)]
    Less -> object [ "tag" .= ("Less" :: Text)]
    Equal -> object [ "tag" .= ("Equal" :: Text)]
    Lequal -> object [ "tag" .= ("Lequal" :: Text)]
    Greater -> object [ "tag" .= ("Greater" :: Text)]
    Notequal -> object [ "tag" .= ("Notequal" :: Text)]
    Gequal -> object [ "tag" .= ("Gequal" :: Text)]
    Always -> object [ "tag" .= ("Always" :: Text)]

instance FromJSON ComparisonFunction where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "Never" -> pure Never
      "Less" -> pure Less
      "Equal" -> pure Equal
      "Lequal" -> pure Lequal
      "Greater" -> pure Greater
      "Notequal" -> pure Notequal
      "Gequal" -> pure Gequal
      "Always" -> pure Always
  parseJSON _ = mzero

instance ToJSON StencilOperation where
  toJSON v = case v of
    OpZero -> object [ "tag" .= ("OpZero" :: Text)]
    OpKeep -> object [ "tag" .= ("OpKeep" :: Text)]
    OpReplace -> object [ "tag" .= ("OpReplace" :: Text)]
    OpIncr -> object [ "tag" .= ("OpIncr" :: Text)]
    OpIncrWrap -> object [ "tag" .= ("OpIncrWrap" :: Text)]
    OpDecr -> object [ "tag" .= ("OpDecr" :: Text)]
    OpDecrWrap -> object [ "tag" .= ("OpDecrWrap" :: Text)]
    OpInvert -> object [ "tag" .= ("OpInvert" :: Text)]

instance FromJSON StencilOperation where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "OpZero" -> pure OpZero
      "OpKeep" -> pure OpKeep
      "OpReplace" -> pure OpReplace
      "OpIncr" -> pure OpIncr
      "OpIncrWrap" -> pure OpIncrWrap
      "OpDecr" -> pure OpDecr
      "OpDecrWrap" -> pure OpDecrWrap
      "OpInvert" -> pure OpInvert
  parseJSON _ = mzero

instance ToJSON BlendEquation where
  toJSON v = case v of
    FuncAdd -> object [ "tag" .= ("FuncAdd" :: Text)]
    FuncSubtract -> object [ "tag" .= ("FuncSubtract" :: Text)]
    FuncReverseSubtract -> object [ "tag" .= ("FuncReverseSubtract" :: Text)]
    Min -> object [ "tag" .= ("Min" :: Text)]
    Max -> object [ "tag" .= ("Max" :: Text)]

instance FromJSON BlendEquation where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "FuncAdd" -> pure FuncAdd
      "FuncSubtract" -> pure FuncSubtract
      "FuncReverseSubtract" -> pure FuncReverseSubtract
      "Min" -> pure Min
      "Max" -> pure Max
  parseJSON _ = mzero

instance ToJSON BlendingFactor where
  toJSON v = case v of
    Zero -> object [ "tag" .= ("Zero" :: Text)]
    One -> object [ "tag" .= ("One" :: Text)]
    SrcColor -> object [ "tag" .= ("SrcColor" :: Text)]
    OneMinusSrcColor -> object [ "tag" .= ("OneMinusSrcColor" :: Text)]
    DstColor -> object [ "tag" .= ("DstColor" :: Text)]
    OneMinusDstColor -> object [ "tag" .= ("OneMinusDstColor" :: Text)]
    SrcAlpha -> object [ "tag" .= ("SrcAlpha" :: Text)]
    OneMinusSrcAlpha -> object [ "tag" .= ("OneMinusSrcAlpha" :: Text)]
    DstAlpha -> object [ "tag" .= ("DstAlpha" :: Text)]
    OneMinusDstAlpha -> object [ "tag" .= ("OneMinusDstAlpha" :: Text)]
    ConstantColor -> object [ "tag" .= ("ConstantColor" :: Text)]
    OneMinusConstantColor -> object [ "tag" .= ("OneMinusConstantColor" :: Text)]
    ConstantAlpha -> object [ "tag" .= ("ConstantAlpha" :: Text)]
    OneMinusConstantAlpha -> object [ "tag" .= ("OneMinusConstantAlpha" :: Text)]
    SrcAlphaSaturate -> object [ "tag" .= ("SrcAlphaSaturate" :: Text)]

instance FromJSON BlendingFactor where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "Zero" -> pure Zero
      "One" -> pure One
      "SrcColor" -> pure SrcColor
      "OneMinusSrcColor" -> pure OneMinusSrcColor
      "DstColor" -> pure DstColor
      "OneMinusDstColor" -> pure OneMinusDstColor
      "SrcAlpha" -> pure SrcAlpha
      "OneMinusSrcAlpha" -> pure OneMinusSrcAlpha
      "DstAlpha" -> pure DstAlpha
      "OneMinusDstAlpha" -> pure OneMinusDstAlpha
      "ConstantColor" -> pure ConstantColor
      "OneMinusConstantColor" -> pure OneMinusConstantColor
      "ConstantAlpha" -> pure ConstantAlpha
      "OneMinusConstantAlpha" -> pure OneMinusConstantAlpha
      "SrcAlphaSaturate" -> pure SrcAlphaSaturate
  parseJSON _ = mzero

instance ToJSON LogicOperation where
  toJSON v = case v of
    Clear -> object [ "tag" .= ("Clear" :: Text)]
    And -> object [ "tag" .= ("And" :: Text)]
    AndReverse -> object [ "tag" .= ("AndReverse" :: Text)]
    Copy -> object [ "tag" .= ("Copy" :: Text)]
    AndInverted -> object [ "tag" .= ("AndInverted" :: Text)]
    Noop -> object [ "tag" .= ("Noop" :: Text)]
    Xor -> object [ "tag" .= ("Xor" :: Text)]
    Or -> object [ "tag" .= ("Or" :: Text)]
    Nor -> object [ "tag" .= ("Nor" :: Text)]
    Equiv -> object [ "tag" .= ("Equiv" :: Text)]
    Invert -> object [ "tag" .= ("Invert" :: Text)]
    OrReverse -> object [ "tag" .= ("OrReverse" :: Text)]
    CopyInverted -> object [ "tag" .= ("CopyInverted" :: Text)]
    OrInverted -> object [ "tag" .= ("OrInverted" :: Text)]
    Nand -> object [ "tag" .= ("Nand" :: Text)]
    Set -> object [ "tag" .= ("Set" :: Text)]

instance FromJSON LogicOperation where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "Clear" -> pure Clear
      "And" -> pure And
      "AndReverse" -> pure AndReverse
      "Copy" -> pure Copy
      "AndInverted" -> pure AndInverted
      "Noop" -> pure Noop
      "Xor" -> pure Xor
      "Or" -> pure Or
      "Nor" -> pure Nor
      "Equiv" -> pure Equiv
      "Invert" -> pure Invert
      "OrReverse" -> pure OrReverse
      "CopyInverted" -> pure CopyInverted
      "OrInverted" -> pure OrInverted
      "Nand" -> pure Nand
      "Set" -> pure Set
  parseJSON _ = mzero

instance ToJSON StencilOps where
  toJSON v = case v of
    StencilOps{..} -> object
      [ "tag" .= ("StencilOps" :: Text)
      , "frontStencilOp" .= frontStencilOp
      , "backStencilOp" .= backStencilOp
      ]

instance FromJSON StencilOps where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "StencilOps" -> do
        frontStencilOp <- obj .: "frontStencilOp"
        backStencilOp <- obj .: "backStencilOp"
        pure $ StencilOps
          { frontStencilOp = frontStencilOp
          , backStencilOp = backStencilOp
          } 
  parseJSON _ = mzero

instance ToJSON StencilTest where
  toJSON v = case v of
    StencilTest{..} -> object
      [ "tag" .= ("StencilTest" :: Text)
      , "stencilComparision" .= stencilComparision
      , "stencilReference" .= stencilReference
      , "stencilMask" .= stencilMask
      ]

instance FromJSON StencilTest where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "StencilTest" -> do
        stencilComparision <- obj .: "stencilComparision"
        stencilReference <- obj .: "stencilReference"
        stencilMask <- obj .: "stencilMask"
        pure $ StencilTest
          { stencilComparision = stencilComparision
          , stencilReference = stencilReference
          , stencilMask = stencilMask
          } 
  parseJSON _ = mzero

instance ToJSON StencilTests where
  toJSON v = case v of
    StencilTests arg0 arg1 -> object [ "tag" .= ("StencilTests" :: Text), "arg0" .= arg0, "arg1" .= arg1]

instance FromJSON StencilTests where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "StencilTests" -> StencilTests <$> obj .: "arg0" <*> obj .: "arg1"
  parseJSON _ = mzero

instance ToJSON FetchPrimitive where
  toJSON v = case v of
    Points -> object [ "tag" .= ("Points" :: Text)]
    Lines -> object [ "tag" .= ("Lines" :: Text)]
    Triangles -> object [ "tag" .= ("Triangles" :: Text)]
    LinesAdjacency -> object [ "tag" .= ("LinesAdjacency" :: Text)]
    TrianglesAdjacency -> object [ "tag" .= ("TrianglesAdjacency" :: Text)]

instance FromJSON FetchPrimitive where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "Points" -> pure Points
      "Lines" -> pure Lines
      "Triangles" -> pure Triangles
      "LinesAdjacency" -> pure LinesAdjacency
      "TrianglesAdjacency" -> pure TrianglesAdjacency
  parseJSON _ = mzero

instance ToJSON OutputPrimitive where
  toJSON v = case v of
    TrianglesOutput -> object [ "tag" .= ("TrianglesOutput" :: Text)]
    LinesOutput -> object [ "tag" .= ("LinesOutput" :: Text)]
    PointsOutput -> object [ "tag" .= ("PointsOutput" :: Text)]

instance FromJSON OutputPrimitive where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "TrianglesOutput" -> pure TrianglesOutput
      "LinesOutput" -> pure LinesOutput
      "PointsOutput" -> pure PointsOutput
  parseJSON _ = mzero

instance ToJSON ColorArity where
  toJSON v = case v of
    Red -> object [ "tag" .= ("Red" :: Text)]
    RG -> object [ "tag" .= ("RG" :: Text)]
    RGB -> object [ "tag" .= ("RGB" :: Text)]
    RGBA -> object [ "tag" .= ("RGBA" :: Text)]

instance FromJSON ColorArity where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "Red" -> pure Red
      "RG" -> pure RG
      "RGB" -> pure RGB
      "RGBA" -> pure RGBA
  parseJSON _ = mzero

instance ToJSON Blending where
  toJSON v = case v of
    NoBlending -> object [ "tag" .= ("NoBlending" :: Text)]
    BlendLogicOp arg0 -> object [ "tag" .= ("BlendLogicOp" :: Text), "arg0" .= arg0]
    Blend{..} -> object
      [ "tag" .= ("Blend" :: Text)
      , "colorEqSrc" .= colorEqSrc
      , "alphaEqSrc" .= alphaEqSrc
      , "colorFSrc" .= colorFSrc
      , "colorFDst" .= colorFDst
      , "alphaFSrc" .= alphaFSrc
      , "alphaFDst" .= alphaFDst
      , "color" .= color
      ]

instance FromJSON Blending where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "NoBlending" -> pure NoBlending
      "BlendLogicOp" -> BlendLogicOp <$> obj .: "arg0"
      "Blend" -> do
        colorEqSrc <- obj .: "colorEqSrc"
        alphaEqSrc <- obj .: "alphaEqSrc"
        colorFSrc <- obj .: "colorFSrc"
        colorFDst <- obj .: "colorFDst"
        alphaFSrc <- obj .: "alphaFSrc"
        alphaFDst <- obj .: "alphaFDst"
        color <- obj .: "color"
        pure $ Blend
          { colorEqSrc = colorEqSrc
          , alphaEqSrc = alphaEqSrc
          , colorFSrc = colorFSrc
          , colorFDst = colorFDst
          , alphaFSrc = alphaFSrc
          , alphaFDst = alphaFDst
          , color = color
          } 
  parseJSON _ = mzero

instance ToJSON RasterContext where
  toJSON v = case v of
    PointCtx arg0 arg1 arg2 -> object [ "tag" .= ("PointCtx" :: Text), "arg0" .= arg0, "arg1" .= arg1, "arg2" .= arg2]
    LineCtx arg0 arg1 -> object [ "tag" .= ("LineCtx" :: Text), "arg0" .= arg0, "arg1" .= arg1]
    TriangleCtx arg0 arg1 arg2 arg3 -> object [ "tag" .= ("TriangleCtx" :: Text), "arg0" .= arg0, "arg1" .= arg1, "arg2" .= arg2, "arg3" .= arg3]

instance FromJSON RasterContext where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "PointCtx" -> PointCtx <$> obj .: "arg0" <*> obj .: "arg1" <*> obj .: "arg2"
      "LineCtx" -> LineCtx <$> obj .: "arg0" <*> obj .: "arg1"
      "TriangleCtx" -> TriangleCtx <$> obj .: "arg0" <*> obj .: "arg1" <*> obj .: "arg2" <*> obj .: "arg3"
  parseJSON _ = mzero

instance ToJSON FragmentOperation where
  toJSON v = case v of
    DepthOp arg0 arg1 -> object [ "tag" .= ("DepthOp" :: Text), "arg0" .= arg0, "arg1" .= arg1]
    StencilOp arg0 arg1 arg2 -> object [ "tag" .= ("StencilOp" :: Text), "arg0" .= arg0, "arg1" .= arg1, "arg2" .= arg2]
    ColorOp arg0 arg1 -> object [ "tag" .= ("ColorOp" :: Text), "arg0" .= arg0, "arg1" .= arg1]

instance FromJSON FragmentOperation where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "DepthOp" -> DepthOp <$> obj .: "arg0" <*> obj .: "arg1"
      "StencilOp" -> StencilOp <$> obj .: "arg0" <*> obj .: "arg1" <*> obj .: "arg2"
      "ColorOp" -> ColorOp <$> obj .: "arg0" <*> obj .: "arg1"
  parseJSON _ = mzero

instance ToJSON AccumulationContext where
  toJSON v = case v of
    AccumulationContext{..} -> object
      [ "tag" .= ("AccumulationContext" :: Text)
      , "accViewportName" .= accViewportName
      , "accOperations" .= accOperations
      ]

instance FromJSON AccumulationContext where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "AccumulationContext" -> do
        accViewportName <- obj .: "accViewportName"
        accOperations <- obj .: "accOperations"
        pure $ AccumulationContext
          { accViewportName = accViewportName
          , accOperations = accOperations
          } 
  parseJSON _ = mzero

instance ToJSON TextureDataType where
  toJSON v = case v of
    FloatT arg0 -> object [ "tag" .= ("FloatT" :: Text), "arg0" .= arg0]
    IntT arg0 -> object [ "tag" .= ("IntT" :: Text), "arg0" .= arg0]
    WordT arg0 -> object [ "tag" .= ("WordT" :: Text), "arg0" .= arg0]
    ShadowT -> object [ "tag" .= ("ShadowT" :: Text)]

instance FromJSON TextureDataType where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "FloatT" -> FloatT <$> obj .: "arg0"
      "IntT" -> IntT <$> obj .: "arg0"
      "WordT" -> WordT <$> obj .: "arg0"
      "ShadowT" -> pure ShadowT
  parseJSON _ = mzero

instance ToJSON TextureType where
  toJSON v = case v of
    Texture1D arg0 arg1 -> object [ "tag" .= ("Texture1D" :: Text), "arg0" .= arg0, "arg1" .= arg1]
    Texture2D arg0 arg1 -> object [ "tag" .= ("Texture2D" :: Text), "arg0" .= arg0, "arg1" .= arg1]
    Texture3D arg0 -> object [ "tag" .= ("Texture3D" :: Text), "arg0" .= arg0]
    TextureCube arg0 -> object [ "tag" .= ("TextureCube" :: Text), "arg0" .= arg0]
    TextureRect arg0 -> object [ "tag" .= ("TextureRect" :: Text), "arg0" .= arg0]
    Texture2DMS arg0 arg1 arg2 arg3 -> object [ "tag" .= ("Texture2DMS" :: Text), "arg0" .= arg0, "arg1" .= arg1, "arg2" .= arg2, "arg3" .= arg3]
    TextureBuffer arg0 -> object [ "tag" .= ("TextureBuffer" :: Text), "arg0" .= arg0]

instance FromJSON TextureType where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "Texture1D" -> Texture1D <$> obj .: "arg0" <*> obj .: "arg1"
      "Texture2D" -> Texture2D <$> obj .: "arg0" <*> obj .: "arg1"
      "Texture3D" -> Texture3D <$> obj .: "arg0"
      "TextureCube" -> TextureCube <$> obj .: "arg0"
      "TextureRect" -> TextureRect <$> obj .: "arg0"
      "Texture2DMS" -> Texture2DMS <$> obj .: "arg0" <*> obj .: "arg1" <*> obj .: "arg2" <*> obj .: "arg3"
      "TextureBuffer" -> TextureBuffer <$> obj .: "arg0"
  parseJSON _ = mzero

instance ToJSON MipMap where
  toJSON v = case v of
    Mip arg0 arg1 -> object [ "tag" .= ("Mip" :: Text), "arg0" .= arg0, "arg1" .= arg1]
    NoMip -> object [ "tag" .= ("NoMip" :: Text)]
    AutoMip arg0 arg1 -> object [ "tag" .= ("AutoMip" :: Text), "arg0" .= arg0, "arg1" .= arg1]

instance FromJSON MipMap where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "Mip" -> Mip <$> obj .: "arg0" <*> obj .: "arg1"
      "NoMip" -> pure NoMip
      "AutoMip" -> AutoMip <$> obj .: "arg0" <*> obj .: "arg1"
  parseJSON _ = mzero

instance ToJSON Filter where
  toJSON v = case v of
    Nearest -> object [ "tag" .= ("Nearest" :: Text)]
    Linear -> object [ "tag" .= ("Linear" :: Text)]
    NearestMipmapNearest -> object [ "tag" .= ("NearestMipmapNearest" :: Text)]
    NearestMipmapLinear -> object [ "tag" .= ("NearestMipmapLinear" :: Text)]
    LinearMipmapNearest -> object [ "tag" .= ("LinearMipmapNearest" :: Text)]
    LinearMipmapLinear -> object [ "tag" .= ("LinearMipmapLinear" :: Text)]

instance FromJSON Filter where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "Nearest" -> pure Nearest
      "Linear" -> pure Linear
      "NearestMipmapNearest" -> pure NearestMipmapNearest
      "NearestMipmapLinear" -> pure NearestMipmapLinear
      "LinearMipmapNearest" -> pure LinearMipmapNearest
      "LinearMipmapLinear" -> pure LinearMipmapLinear
  parseJSON _ = mzero

instance ToJSON EdgeMode where
  toJSON v = case v of
    Repeat -> object [ "tag" .= ("Repeat" :: Text)]
    MirroredRepeat -> object [ "tag" .= ("MirroredRepeat" :: Text)]
    ClampToEdge -> object [ "tag" .= ("ClampToEdge" :: Text)]
    ClampToBorder -> object [ "tag" .= ("ClampToBorder" :: Text)]

instance FromJSON EdgeMode where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "Repeat" -> pure Repeat
      "MirroredRepeat" -> pure MirroredRepeat
      "ClampToEdge" -> pure ClampToEdge
      "ClampToBorder" -> pure ClampToBorder
  parseJSON _ = mzero

instance ToJSON ImageSemantic where
  toJSON v = case v of
    Depth -> object [ "tag" .= ("Depth" :: Text)]
    Stencil -> object [ "tag" .= ("Stencil" :: Text)]
    Color -> object [ "tag" .= ("Color" :: Text)]

instance FromJSON ImageSemantic where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "Depth" -> pure Depth
      "Stencil" -> pure Stencil
      "Color" -> pure Color
  parseJSON _ = mzero

instance ToJSON ImageRef where
  toJSON v = case v of
    TextureImage arg0 arg1 arg2 -> object [ "tag" .= ("TextureImage" :: Text), "arg0" .= arg0, "arg1" .= arg1, "arg2" .= arg2]
    Framebuffer arg0 -> object [ "tag" .= ("Framebuffer" :: Text), "arg0" .= arg0]

instance FromJSON ImageRef where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "TextureImage" -> TextureImage <$> obj .: "arg0" <*> obj .: "arg1" <*> obj .: "arg2"
      "Framebuffer" -> Framebuffer <$> obj .: "arg0"
  parseJSON _ = mzero

instance ToJSON ClearImage where
  toJSON v = case v of
    ClearImage{..} -> object
      [ "tag" .= ("ClearImage" :: Text)
      , "imageSemantic" .= imageSemantic
      , "clearValue" .= clearValue
      ]

instance FromJSON ClearImage where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "ClearImage" -> do
        imageSemantic <- obj .: "imageSemantic"
        clearValue <- obj .: "clearValue"
        pure $ ClearImage
          { imageSemantic = imageSemantic
          , clearValue = clearValue
          } 
  parseJSON _ = mzero

instance ToJSON Command where
  toJSON v = case v of
    SetRasterContext arg0 -> object [ "tag" .= ("SetRasterContext" :: Text), "arg0" .= arg0]
    SetAccumulationContext arg0 -> object [ "tag" .= ("SetAccumulationContext" :: Text), "arg0" .= arg0]
    SetRenderTarget arg0 -> object [ "tag" .= ("SetRenderTarget" :: Text), "arg0" .= arg0]
    SetProgram arg0 -> object [ "tag" .= ("SetProgram" :: Text), "arg0" .= arg0]
    SetSamplerUniform arg0 arg1 -> object [ "tag" .= ("SetSamplerUniform" :: Text), "arg0" .= arg0, "arg1" .= arg1]
    SetTexture arg0 arg1 -> object [ "tag" .= ("SetTexture" :: Text), "arg0" .= arg0, "arg1" .= arg1]
    SetSampler arg0 arg1 -> object [ "tag" .= ("SetSampler" :: Text), "arg0" .= arg0, "arg1" .= arg1]
    RenderSlot arg0 -> object [ "tag" .= ("RenderSlot" :: Text), "arg0" .= arg0]
    RenderStream arg0 -> object [ "tag" .= ("RenderStream" :: Text), "arg0" .= arg0]
    ClearRenderTarget arg0 -> object [ "tag" .= ("ClearRenderTarget" :: Text), "arg0" .= arg0]
    GenerateMipMap arg0 -> object [ "tag" .= ("GenerateMipMap" :: Text), "arg0" .= arg0]
    SaveImage arg0 arg1 -> object [ "tag" .= ("SaveImage" :: Text), "arg0" .= arg0, "arg1" .= arg1]
    LoadImage arg0 arg1 -> object [ "tag" .= ("LoadImage" :: Text), "arg0" .= arg0, "arg1" .= arg1]

instance FromJSON Command where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "SetRasterContext" -> SetRasterContext <$> obj .: "arg0"
      "SetAccumulationContext" -> SetAccumulationContext <$> obj .: "arg0"
      "SetRenderTarget" -> SetRenderTarget <$> obj .: "arg0"
      "SetProgram" -> SetProgram <$> obj .: "arg0"
      "SetSamplerUniform" -> SetSamplerUniform <$> obj .: "arg0" <*> obj .: "arg1"
      "SetTexture" -> SetTexture <$> obj .: "arg0" <*> obj .: "arg1"
      "SetSampler" -> SetSampler <$> obj .: "arg0" <*> obj .: "arg1"
      "RenderSlot" -> RenderSlot <$> obj .: "arg0"
      "RenderStream" -> RenderStream <$> obj .: "arg0"
      "ClearRenderTarget" -> ClearRenderTarget <$> obj .: "arg0"
      "GenerateMipMap" -> GenerateMipMap <$> obj .: "arg0"
      "SaveImage" -> SaveImage <$> obj .: "arg0" <*> obj .: "arg1"
      "LoadImage" -> LoadImage <$> obj .: "arg0" <*> obj .: "arg1"
  parseJSON _ = mzero

instance ToJSON SamplerDescriptor where
  toJSON v = case v of
    SamplerDescriptor{..} -> object
      [ "tag" .= ("SamplerDescriptor" :: Text)
      , "samplerWrapS" .= samplerWrapS
      , "samplerWrapT" .= samplerWrapT
      , "samplerWrapR" .= samplerWrapR
      , "samplerMinFilter" .= samplerMinFilter
      , "samplerMagFilter" .= samplerMagFilter
      , "samplerBorderColor" .= samplerBorderColor
      , "samplerMinLod" .= samplerMinLod
      , "samplerMaxLod" .= samplerMaxLod
      , "samplerLodBias" .= samplerLodBias
      , "samplerCompareFunc" .= samplerCompareFunc
      ]

instance FromJSON SamplerDescriptor where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "SamplerDescriptor" -> do
        samplerWrapS <- obj .: "samplerWrapS"
        samplerWrapT <- obj .: "samplerWrapT"
        samplerWrapR <- obj .: "samplerWrapR"
        samplerMinFilter <- obj .: "samplerMinFilter"
        samplerMagFilter <- obj .: "samplerMagFilter"
        samplerBorderColor <- obj .: "samplerBorderColor"
        samplerMinLod <- obj .: "samplerMinLod"
        samplerMaxLod <- obj .: "samplerMaxLod"
        samplerLodBias <- obj .: "samplerLodBias"
        samplerCompareFunc <- obj .: "samplerCompareFunc"
        pure $ SamplerDescriptor
          { samplerWrapS = samplerWrapS
          , samplerWrapT = samplerWrapT
          , samplerWrapR = samplerWrapR
          , samplerMinFilter = samplerMinFilter
          , samplerMagFilter = samplerMagFilter
          , samplerBorderColor = samplerBorderColor
          , samplerMinLod = samplerMinLod
          , samplerMaxLod = samplerMaxLod
          , samplerLodBias = samplerLodBias
          , samplerCompareFunc = samplerCompareFunc
          } 
  parseJSON _ = mzero

instance ToJSON TextureDescriptor where
  toJSON v = case v of
    TextureDescriptor{..} -> object
      [ "tag" .= ("TextureDescriptor" :: Text)
      , "textureType" .= textureType
      , "textureSize" .= textureSize
      , "textureSemantic" .= textureSemantic
      , "textureSampler" .= textureSampler
      , "textureBaseLevel" .= textureBaseLevel
      , "textureMaxLevel" .= textureMaxLevel
      ]

instance FromJSON TextureDescriptor where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "TextureDescriptor" -> do
        textureType <- obj .: "textureType"
        textureSize <- obj .: "textureSize"
        textureSemantic <- obj .: "textureSemantic"
        textureSampler <- obj .: "textureSampler"
        textureBaseLevel <- obj .: "textureBaseLevel"
        textureMaxLevel <- obj .: "textureMaxLevel"
        pure $ TextureDescriptor
          { textureType = textureType
          , textureSize = textureSize
          , textureSemantic = textureSemantic
          , textureSampler = textureSampler
          , textureBaseLevel = textureBaseLevel
          , textureMaxLevel = textureMaxLevel
          } 
  parseJSON _ = mzero

instance ToJSON Parameter where
  toJSON v = case v of
    Parameter{..} -> object
      [ "tag" .= ("Parameter" :: Text)
      , "name" .= name
      , "ty" .= ty
      ]

instance FromJSON Parameter where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "Parameter" -> do
        name <- obj .: "name"
        ty <- obj .: "ty"
        pure $ Parameter
          { name = name
          , ty = ty
          } 
  parseJSON _ = mzero

instance ToJSON Program where
  toJSON v = case v of
    Program{..} -> object
      [ "tag" .= ("Program" :: Text)
      , "programUniforms" .= programUniforms
      , "programStreams" .= programStreams
      , "programInTextures" .= programInTextures
      , "programOutput" .= programOutput
      , "vertexShader" .= vertexShader
      , "geometryShader" .= geometryShader
      , "fragmentShader" .= fragmentShader
      ]

instance FromJSON Program where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "Program" -> do
        programUniforms <- obj .: "programUniforms"
        programStreams <- obj .: "programStreams"
        programInTextures <- obj .: "programInTextures"
        programOutput <- obj .: "programOutput"
        vertexShader <- obj .: "vertexShader"
        geometryShader <- obj .: "geometryShader"
        fragmentShader <- obj .: "fragmentShader"
        pure $ Program
          { programUniforms = programUniforms
          , programStreams = programStreams
          , programInTextures = programInTextures
          , programOutput = programOutput
          , vertexShader = vertexShader
          , geometryShader = geometryShader
          , fragmentShader = fragmentShader
          } 
  parseJSON _ = mzero

instance ToJSON Slot where
  toJSON v = case v of
    Slot{..} -> object
      [ "tag" .= ("Slot" :: Text)
      , "slotName" .= slotName
      , "slotStreams" .= slotStreams
      , "slotUniforms" .= slotUniforms
      , "slotPrimitive" .= slotPrimitive
      , "slotPrograms" .= slotPrograms
      ]

instance FromJSON Slot where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "Slot" -> do
        slotName <- obj .: "slotName"
        slotStreams <- obj .: "slotStreams"
        slotUniforms <- obj .: "slotUniforms"
        slotPrimitive <- obj .: "slotPrimitive"
        slotPrograms <- obj .: "slotPrograms"
        pure $ Slot
          { slotName = slotName
          , slotStreams = slotStreams
          , slotUniforms = slotUniforms
          , slotPrimitive = slotPrimitive
          , slotPrograms = slotPrograms
          } 
  parseJSON _ = mzero

instance ToJSON StreamData where
  toJSON v = case v of
    StreamData{..} -> object
      [ "tag" .= ("StreamData" :: Text)
      , "streamData" .= streamData
      , "streamType" .= streamType
      , "streamPrimitive" .= streamPrimitive
      , "streamPrograms" .= streamPrograms
      ]

instance FromJSON StreamData where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "StreamData" -> do
        streamData <- obj .: "streamData"
        streamType <- obj .: "streamType"
        streamPrimitive <- obj .: "streamPrimitive"
        streamPrograms <- obj .: "streamPrograms"
        pure $ StreamData
          { streamData = streamData
          , streamType = streamType
          , streamPrimitive = streamPrimitive
          , streamPrograms = streamPrograms
          } 
  parseJSON _ = mzero

instance ToJSON TargetItem where
  toJSON v = case v of
    TargetItem{..} -> object
      [ "tag" .= ("TargetItem" :: Text)
      , "targetSemantic" .= targetSemantic
      , "targetRef" .= targetRef
      ]

instance FromJSON TargetItem where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "TargetItem" -> do
        targetSemantic <- obj .: "targetSemantic"
        targetRef <- obj .: "targetRef"
        pure $ TargetItem
          { targetSemantic = targetSemantic
          , targetRef = targetRef
          } 
  parseJSON _ = mzero

instance ToJSON RenderTarget where
  toJSON v = case v of
    RenderTarget{..} -> object
      [ "tag" .= ("RenderTarget" :: Text)
      , "renderTargets" .= renderTargets
      ]

instance FromJSON RenderTarget where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "RenderTarget" -> do
        renderTargets <- obj .: "renderTargets"
        pure $ RenderTarget
          { renderTargets = renderTargets
          } 
  parseJSON _ = mzero

instance ToJSON Backend where
  toJSON v = case v of
    WebGL1 -> object [ "tag" .= ("WebGL1" :: Text)]
    OpenGL33 -> object [ "tag" .= ("OpenGL33" :: Text)]

instance FromJSON Backend where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "WebGL1" -> pure WebGL1
      "OpenGL33" -> pure OpenGL33
  parseJSON _ = mzero

instance ToJSON Pipeline where
  toJSON v = case v of
    Pipeline{..} -> object
      [ "tag" .= ("Pipeline" :: Text)
      , "backend" .= backend
      , "textures" .= textures
      , "samplers" .= samplers
      , "targets" .= targets
      , "programs" .= programs
      , "slots" .= slots
      , "streams" .= streams
      , "commands" .= commands
      ]

instance FromJSON Pipeline where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "Pipeline" -> do
        backend <- obj .: "backend"
        textures <- obj .: "textures"
        samplers <- obj .: "samplers"
        targets <- obj .: "targets"
        programs <- obj .: "programs"
        slots <- obj .: "slots"
        streams <- obj .: "streams"
        commands <- obj .: "commands"
        pure $ Pipeline
          { backend = backend
          , textures = textures
          , samplers = samplers
          , targets = targets
          , programs = programs
          , slots = slots
          , streams = streams
          , commands = commands
          } 
  parseJSON _ = mzero

