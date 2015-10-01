{-# LANGUAGE OverloadedStrings #-}
module Definitions (modules) where

import Control.Monad.Writer
import Language

ir = do
  -- type aliases
  "StreamName" #= Int
  "ProgramName" #= Int
  "TextureName" #= Int
  "SamplerName" #= Int
  "UniformName" #= String
  "SlotName" #= Int
  "FrameBufferComponent" #= Int
  "TextureUnit" #= Int
  "RenderTargetName" #= Int
  "TextureUnitMapping" #= Map "UniformName" "TextureUnit"

  -- definitions
  data_ "ArrayValue" $ do
    const_ "VBoolArray"   [Array Bool]
    const_ "VIntArray"    [Array Int32]
    const_ "VWordArray"   [Array Word32]
    const_ "VFloatArray"  [Array Float]

  -- GPU type value reification, needed for shader codegen
  data_ "Value" $ do
    const_ "VBool"  [Bool]
    const_ "VV2B"   [v2b]
    const_ "VV3B"   [v3b]
    const_ "VV4B"   [v4b]
    const_ "VWord"  [Word32]
    const_ "VV2U"   [v2u]
    const_ "VV3U"   [v3u]
    const_ "VV4U"   [v4u]
    const_ "VInt"   [Int32]
    const_ "VV2I"   [v2i]
    const_ "VV3I"   [v3i]
    const_ "VV4I"   [v4i]
    const_ "VFloat" [Float]
    const_ "VV2F"   [v2f]
    const_ "VV3F"   [v3f]
    const_ "VV4F"   [v4f]
    const_ "VM22F"  [m22]
    const_ "VM23F"  [m23]
    const_ "VM24F"  [m24]
    const_ "VM32F"  [m32]
    const_ "VM33F"  [m33]
    const_ "VM34F"  [m34]
    const_ "VM42F"  [m42]
    const_ "VM43F"  [m43]
    const_ "VM44F"  [m44]

  data_ "InputType" $ do
    enum_ "Bool"
    enum_ "V2B"
    enum_ "V3B"
    enum_ "V4B"
    enum_ "Word"
    enum_ "V2U"
    enum_ "V3U"
    enum_ "V4U"
    enum_ "Int"
    enum_ "V2I"
    enum_ "V3I"
    enum_ "V4I"
    enum_ "Float"
    enum_ "V2F"
    enum_ "V3F"
    enum_ "V4F"
    enum_ "M22F"
    enum_ "M23F"
    enum_ "M24F"
    enum_ "M32F"
    enum_ "M33F"
    enum_ "M34F"
    enum_ "M42F"
    enum_ "M43F"
    enum_ "M44F"
    -- shadow textures
    enum_ "STexture1D"
    enum_ "STexture2D"
    enum_ "STextureCube"
    enum_ "STexture1DArray"
    enum_ "STexture2DArray"
    enum_ "STexture2DRect"
    -- float textures
    enum_ "FTexture1D"
    enum_ "FTexture2D"
    enum_ "FTexture3D"
    enum_ "FTextureCube"
    enum_ "FTexture1DArray"
    enum_ "FTexture2DArray"
    enum_ "FTexture2DMS"
    enum_ "FTexture2DMSArray"
    enum_ "FTextureBuffer"
    enum_ "FTexture2DRect"
    -- int textures
    enum_ "ITexture1D"
    enum_ "ITexture2D"
    enum_ "ITexture3D"
    enum_ "ITextureCube"
    enum_ "ITexture1DArray"
    enum_ "ITexture2DArray"
    enum_ "ITexture2DMS"
    enum_ "ITexture2DMSArray"
    enum_ "ITextureBuffer"
    enum_ "ITexture2DRect"
    -- uint textures
    enum_ "UTexture1D"
    enum_ "UTexture2D"
    enum_ "UTexture3D"
    enum_ "UTextureCube"
    enum_ "UTexture1DArray"
    enum_ "UTexture2DArray"
    enum_ "UTexture2DMS"
    enum_ "UTexture2DMSArray"
    enum_ "UTextureBuffer"
    enum_ "UTexture2DRect"
    deriving_ [Haskell] [Eq,Ord]

  data_ "PointSpriteCoordOrigin" $ do
    enum_ "LowerLeft"
    enum_ "UpperLeft"

  data_ "PointSize" $ do
    const_  "PointSize" [Float]
    enum_   "ProgramPointSize"

  data_ "PolygonOffset" $ do
    enum_   "NoOffset"
    const_  "Offset" [Float,Float]

  data_ "FrontFace" $ do
    enum_ "CCW"
    enum_ "CW"

  data_ "PolygonMode" $ do
    const_  "PolygonPoint" ["PointSize"]
    const_  "PolygonLine"  [Float]
    enum_   "PolygonFill"

  data_ "ProvokingVertex" $ do
    enum_ "FirstVertex"
    enum_ "LastVertex"

  data_ "CullMode" $ do
    enum_ "CullNone"
    const_  "CullFront" ["FrontFace"]
    const_  "CullBack"  ["FrontFace"]

  data_ "ComparisonFunction" $ do
    enum_ "Never"
    enum_ "Less"
    enum_ "Equal"
    enum_ "Lequal"
    enum_ "Greater"
    enum_ "Notequal"
    enum_ "Gequal"
    enum_ "Always"

  "DepthFunction" #= "ComparisonFunction"

  data_ "StencilOperation" $ do
    enum_ "OpZero"
    enum_ "OpKeep"
    enum_ "OpReplace"
    enum_ "OpIncr"
    enum_ "OpIncrWrap"
    enum_ "OpDecr"
    enum_ "OpDecrWrap"
    enum_ "OpInvert"

  data_ "BlendEquation" $ do
    enum_ "FuncAdd"
    enum_ "FuncSubtract"
    enum_ "FuncReverseSubtract"
    enum_ "Min"
    enum_ "Max"

  data_ "BlendingFactor" $ do
    enum_ "Zero"
    enum_ "One"
    enum_ "SrcColor"
    enum_ "OneMinusSrcColor"
    enum_ "DstColor"
    enum_ "OneMinusDstColor"
    enum_ "SrcAlpha"
    enum_ "OneMinusSrcAlpha"
    enum_ "DstAlpha"
    enum_ "OneMinusDstAlpha"
    enum_ "ConstantColor"
    enum_ "OneMinusConstantColor"
    enum_ "ConstantAlpha"
    enum_ "OneMinusConstantAlpha"
    enum_ "SrcAlphaSaturate"

  data_ "LogicOperation" $ do
    enum_ "Clear"
    enum_ "And"
    enum_ "AndReverse"
    enum_ "Copy"
    enum_ "AndInverted"
    enum_ "Noop"
    enum_ "Xor"
    enum_ "Or"
    enum_ "Nor"
    enum_ "Equiv"
    enum_ "Invert"
    enum_ "OrReverse"
    enum_ "CopyInverted"
    enum_ "OrInverted"
    enum_ "Nand"
    enum_ "Set"

  data_ "StencilOps" $ do
    constR_ "StencilOps"
      [ "frontStencilOp"  #:: "StencilOperation" -- Used for front faced triangles and other primitives.
      , "backStencilOp"   #:: "StencilOperation" -- Used for back faced triangles.
      ]

  data_ "StencilTest" $ do
    constR_ "StencilTest"
      [ "stencilComparision"  #:: "ComparisonFunction" -- The function used to compare the @stencilReference@ and the stencil buffers value with.
      , "stencilReference"    #:: Int32                -- The value to compare with the stencil buffer's value.
      , "stencilMask"         #:: Word32               -- A bit mask with ones in each position that should be compared and written to the stencil buffer.
      ]

  data_ "StencilTests" $ do
    const_ "StencilTests" ["StencilTest", "StencilTest"]

  -- primitive types
  data_ "FetchPrimitive" $ do
    enum_ "Points"
    enum_ "Lines"
    enum_ "Triangles"
    enum_ "LinesAdjacency"
    enum_ "TrianglesAdjacency"
    deriving_ [PureScript] [Show,Eq]

  data_ "OutputPrimitive" $ do
    enum_ "TrianglesOutput"
    enum_ "LinesOutput"
    enum_ "PointsOutput"

  data_ "ColorArity" $ do
    enum_ "Red"
    enum_ "RG"
    enum_ "RGB"
    enum_ "RGBA"
    deriving_ [PureScript] [Show]

  data_ "Blending" $ do
    enum_ "NoBlending"
    const_ "BlendLogicOp"  ["LogicOperation"]
    constR_ "Blend"
      [ "colorEqSrc"  #:: "BlendEquation"
      , "alphaEqSrc"  #:: "BlendEquation"
      , "colorFSrc"   #:: "BlendingFactor"
      , "colorFDst"   #:: "BlendingFactor"
      , "alphaFSrc"   #:: "BlendingFactor"
      , "alphaFDst"   #:: "BlendingFactor"
      , "color"       #:: v4f
      ]

  data_ "RasterContext" $ do
    const_ "PointCtx"      ["PointSize", Float, "PointSpriteCoordOrigin"]
    const_ "LineCtx"       [Float, "ProvokingVertex"]
    const_ "TriangleCtx"   ["CullMode", "PolygonMode", "PolygonOffset", "ProvokingVertex"]

  data_ "FragmentOperation" $ do
    const_ "DepthOp"       ["DepthFunction", Bool]
    const_ "StencilOp"     ["StencilTests", "StencilOps", "StencilOps"]
    const_ "ColorOp"       ["Blending", "Value"]

  data_ "AccumulationContext" $ do
    constR_ "AccumulationContext"
      [ "accViewportName" #:: Maybe String
      , "accOperations"   #:: List "FragmentOperation"
      ]

  data_ "TextureDataType" $ do
    const_  "FloatT"        ["ColorArity"]
    const_  "IntT"          ["ColorArity"]
    const_  "WordT"         ["ColorArity"]
    enum_   "ShadowT"
    deriving_ [PureScript] [Show]

  data_ "TextureType" $ do
    const_ "Texture1D"      ["TextureDataType", Int]
    const_ "Texture2D"      ["TextureDataType", Int]
    const_ "Texture3D"      ["TextureDataType"]
    const_ "TextureCube"    ["TextureDataType"]
    const_ "TextureRect"    ["TextureDataType"]
    const_ "Texture2DMS"    ["TextureDataType", Int, Int, Bool]
    const_ "TextureBuffer"  ["TextureDataType"]

  data_ "MipMap" $ do
    const_  "Mip"           [Int,Int] -- Base level, Max level
    enum_   "NoMip"
    const_  "AutoMip"       [Int,Int] -- Base level, Max level

  data_ "Filter" $ do
    enum_ "Nearest"
    enum_ "Linear"
    enum_ "NearestMipmapNearest"
    enum_ "NearestMipmapLinear"
    enum_ "LinearMipmapNearest"
    enum_ "LinearMipmapLinear"

  data_ "EdgeMode" $ do
    enum_ "Repeat"
    enum_ "MirroredRepeat"
    enum_ "ClampToEdge"
    enum_ "ClampToBorder"

  data_ "ImageSemantic" $ do
    enum_ "Depth"
    enum_ "Stencil"
    enum_ "Color"
    deriving_ [Haskell] [Eq]

  data_ "ImageRef" $ do
    const_ "TextureImage"  ["TextureName", Int, Maybe Int]  -- Texture name, mip index, array index
    const_ "Framebuffer"   ["ImageSemantic"]

  data_ "ClearImage" $ do
    constR_ "ClearImage"
      [ "imageSemantic" #:: "ImageSemantic"
      , "clearValue"    #:: "Value"
      ]

  data_ "Command" $ do
    const_ "SetRasterContext"          ["RasterContext"]
    const_ "SetAccumulationContext"    ["AccumulationContext"]
    const_ "SetRenderTarget"           ["RenderTargetName"]
    const_ "SetProgram"                ["ProgramName"] --TextureUnitMapping    -- adding texture unit map to set program command seems to be better solution than the current one
    const_ "SetSamplerUniform"         ["UniformName", "TextureUnit"]             -- hint: currently the texture unit mapping is encoded with this command
    const_ "SetTexture"                ["TextureUnit", "TextureName"]             -- binds texture to the specified texture unit
    const_ "SetSampler"                ["TextureUnit", Maybe "SamplerName"]     -- binds sampler to the specified texture unit
    const_ "RenderSlot"                ["SlotName"]
    const_ "RenderStream"              ["StreamName"]
    const_ "ClearRenderTarget"         [Array "ClearImage"]
    const_ "GenerateMipMap"            ["TextureUnit"]
    const_ "SaveImage"                 ["FrameBufferComponent", "ImageRef"]                            -- from framebuffer component to texture (image)
    const_ "LoadImage"                 ["ImageRef", "FrameBufferComponent"]                            -- from texture (image) to framebuffer component

  data_ "SamplerDescriptor" $ do
    constR_ "SamplerDescriptor"
      [ "samplerWrapS"          #:: "EdgeMode"
      , "samplerWrapT"          #:: Maybe "EdgeMode"
      , "samplerWrapR"          #:: Maybe "EdgeMode"
      , "samplerMinFilter"      #:: "Filter"
      , "samplerMagFilter"      #:: "Filter"
      , "samplerBorderColor"    #:: "Value"
      , "samplerMinLod"         #:: Maybe Float
      , "samplerMaxLod"         #:: Maybe Float
      , "samplerLodBias"        #:: Float
      , "samplerCompareFunc"    #:: Maybe "ComparisonFunction"
      ]

  data_ "TextureDescriptor" $ do    -- texture size, type, array, mipmap
    constR_ "TextureDescriptor"
      [ "textureType"       #:: "TextureType"
      , "textureSize"       #:: "Value"
      , "textureSemantic"   #:: "ImageSemantic"
      , "textureSampler"    #:: "SamplerDescriptor"
      , "textureBaseLevel"  #:: Int
      , "textureMaxLevel"   #:: Int
      ]

  data_ "Parameter" $ do 
    constR_ "Parameter"
      [ "name"  #:: String
      , "ty"    #:: "InputType"
      ]

  data_ "Program" $ do   -- AST, input
    constR_ "Program"
      [ "programUniforms"   #:: Map "UniformName" "InputType"   -- uniform input (value based uniforms only / no textures)
      , "programStreams"    #:: Map "UniformName" "Parameter"   -- vertex shader input attribute name -> (slot attribute name, attribute type)
      , "programInTextures" #:: Map "UniformName" "InputType"   -- all textures (uniform textures and render textures) referenced by the program
      , "programOutput"     #:: Array "Parameter"
      , "vertexShader"      #:: String
      , "geometryShader"    #:: Maybe String
      , "fragmentShader"    #:: String
      ]

  data_ "Slot" $ do      -- input, primitive type
    constR_ "Slot"
      [ "slotName"      #:: String
      , "slotStreams"   #:: Map String "InputType"
      , "slotUniforms"  #:: Map "UniformName" "InputType"
      , "slotPrimitive" #:: "FetchPrimitive"
      , "slotPrograms"  #:: Array "ProgramName"
      ]

  data_ "StreamData" $ do
    constR_ "StreamData"
      [ "streamData"      #:: Map String "ArrayValue"
      , "streamType"      #:: Map String "InputType"
      , "streamPrimitive" #:: "FetchPrimitive"
      , "streamPrograms"  #:: Array "ProgramName"
      ]

  data_ "TargetItem" $ do
    constR_ "TargetItem"
      [ "targetSemantic"  #:: "ImageSemantic"
      , "targetRef"       #:: Maybe "ImageRef"
      ]

  data_ "RenderTarget" $ do
    constR_ "RenderTarget"
      [ "renderTargets" #:: Array "TargetItem" -- render texture or default framebuffer (semantic, render texture for the program output)
      ]

  data_ "Backend" $ do
    enum_ "WebGL1"
    enum_ "OpenGL33"

  data_ "Pipeline" $ do
    constR_ "Pipeline"
      [ "backend"       #:: "Backend"
      , "textures"      #:: Array "TextureDescriptor"
      , "samplers"      #:: Array "SamplerDescriptor"
      , "targets"       #:: Array "RenderTarget"
      , "programs"      #:: Array "Program"
      , "slots"         #:: Array "Slot"
      , "streams"       #:: Array "StreamData"
      , "commands"      #:: Array "Command"
      ]
    deriving_ [Haskell] [Show]

mesh = do
  data_ "MeshAttribute" $ do
    const_ "A_Float"  [Array Float]
    const_ "A_V2F"    [Array v2f]
    const_ "A_V3F"    [Array v3f]
    const_ "A_V4F"    [Array v4f]
    const_ "A_M22F"   [Array m22]
    const_ "A_M33F"   [Array m33]
    const_ "A_M44F"   [Array m44]
    const_ "A_Int"    [Array Int32]
    const_ "A_Word"   [Array Word32]

  data_ "MeshPrimitive" $ do
    enum_  "P_Points"
    enum_  "P_TriangleStrip"
    enum_  "P_Triangles"
    const_ "P_TriangleStripI" [Array Int32]
    const_ "P_TrianglesI"     [Array Int32]

  data_ "Mesh" $ do
    constR_ "Mesh"
      [ "mAttributes" #:: Map String "MeshAttribute"
      , "mPrimitive"  #:: "MeshPrimitive"
      ]

typeInfo = do
  data_ "TypeInfo" $ do
    constR_ "TypeInfo"
      [ "startLine"   #:: Int
      , "startColumn" #:: Int
      , "endLine"     #:: Int
      , "endColumn"   #:: Int
      , "text"        #:: String
      ]

  data_ "MyEither" $ do
    const_ "MyLeft"   ["TypeInfo", Array "TypeInfo"]
    const_ "MyRight"  ["Pipeline", Array "TypeInfo"]

modules = do
  module_ "IR" ir
  module_ "Mesh" mesh
  module_ "TypeInfo" $ do
    import_ ["IR"]
    typeInfo
