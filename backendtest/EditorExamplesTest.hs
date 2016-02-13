{-# LANGUAGE LambdaCase #-}
module EditorExamplesTest (getRenderJob) where

import Control.Monad
import qualified Data.Vector as V
import qualified Data.Map as Map
import qualified Data.ByteString as BS
import qualified Data.ByteString.Base64 as B64
import Data.ByteString.Char8 (unpack)
import System.FilePath
import System.Directory

import Data.Aeson
import Data.Vect

import TestData as TD
import LambdaCube.Linear
import LambdaCube.IR
import LambdaCube.PipelineSchema
import LambdaCube.PipelineSchemaUtil
import LambdaCube.Mesh

import LambdaCube.Compiler as LambdaCube -- compiler

{-
  ../test-data/editor-examples

  let inputSchema = 
        { slots : fromArray [ Tuple "stream4" {primitive: Triangles, attributes: fromArray [Tuple "position4" TV4F, Tuple "vertexUV" TV2F]}
                            ]
        , uniforms : fromArray
          +[ Tuple "MVP" M44F
          +, Tuple "Time" Float
          +, Tuple "Diffuse" FTexture2D
          ]
        }
-}

inputSchema = makeSchema $ do
  defObjectArray "stream4" Triangles $ do
    "position4" @: Attribute_V4F
    "vertexUV"  @: Attribute_V2F
  defUniforms $ do
    "Time"    @: Float
    "MVP"     @: M44F
    "Diffuse" @: FTexture2D

frame t m = Frame
  { renderCount   = 10
  , frameUniforms = Map.fromList [("Time",VFloat t), ("MVP",VM44F m)]
  , frameTextures = Map.fromList [("Diffuse",0)]
  }

scene wh = Scene
  { TD.objectArrays     = Map.fromList [("stream4", V.fromList [0])]
  , renderTargetWidth   = wh
  , renderTargetHeight  = wh
  , frames              = V.fromList [frame t (mvp t) | t <- [0..10]]
  }
  where
    mvp t =
      let camPos = Vec3 3.0 1.3 0.3
          camTarget = Vec3 0.0 0.0 0.0
          camUp = Vec3 0.0 1.0 0.0
          near = 0.1
          far = 100.0
          fovDeg = 30.0

          angle = pi / 24.0 * t

          cm = fromProjective $ lookat camPos camTarget camUp
          mm = fromProjective $ orthogonal $ toOrthoUnsafe $ rotMatrixY angle
          pm = perspective near far (fovDeg / 180 * pi) (fromIntegral wh / fromIntegral wh)
      in mat4ToM44F $ mm .*. cm .*. pm

getRenderJob = do
  let path = "../testdata/editor-examples"
  tests <- filter ((".lc" ==) . takeExtension) <$> getDirectoryContents path
  print tests
  ppls <- forM tests $ \name -> do
    putStrLn $ "compile: " ++ name
    LambdaCube.compileMain [path] OpenGL33 (dropExtension name) >>= \case
      Left err  -> fail $ "compile error:\n" ++ err
      Right ppl -> return $ PipelineInfo
        { pipelineName = path </> name
        , pipeline = ppl
        }

  img <- unpack . B64.encode <$> BS.readFile "logo256x256.png"

  return $ RenderJob
    { meshes      = V.fromList [cubeMesh]
    , TD.textures = V.fromList [img]
    , schema      = inputSchema
    , scenes      = V.fromList [scene 64]
    , pipelines   = V.fromList ppls
    }

g_vertex_buffer_data =
    [ V4   1.0    1.0  (-1.0) 1.0
    , V4   1.0  (-1.0) (-1.0) 1.0
    , V4 (-1.0) (-1.0) (-1.0) 1.0

    , V4   1.0    1.0  (-1.0) 1.0
    , V4 (-1.0) (-1.0) (-1.0) 1.0
    , V4 (-1.0)   1.0  (-1.0) 1.0

    , V4   1.0    1.0  (-1.0) 1.0
    , V4   1.0    1.0    1.0  1.0
    , V4   1.0  (-1.0)   1.0  1.0

    , V4   1.0    1.0  (-1.0) 1.0
    , V4   1.0  (-1.0)   1.0  1.0
    , V4   1.0  (-1.0) (-1.0) 1.0

    , V4   1.0    1.0    1.0  1.0
    , V4 (-1.0) (-1.0)   1.0  1.0
    , V4   1.0  (-1.0)   1.0  1.0

    , V4   1.0    1.0    1.0  1.0
    , V4 (-1.0)   1.0    1.0  1.0
    , V4 (-1.0) (-1.0)   1.0  1.0

    , V4 (-1.0)   1.0    1.0  1.0
    , V4 (-1.0) (-1.0) (-1.0) 1.0
    , V4 (-1.0) (-1.0)   1.0  1.0

    , V4 (-1.0)   1.0    1.0  1.0
    , V4 (-1.0)   1.0  (-1.0) 1.0
    , V4 (-1.0) (-1.0) (-1.0) 1.0

    , V4   1.0    1.0  (-1.0) 1.0
    , V4 (-1.0)   1.0  (-1.0) 1.0
    , V4 (-1.0)   1.0    1.0  1.0

    , V4   1.0    1.0  (-1.0) 1.0
    , V4 (-1.0)   1.0    1.0  1.0
    , V4   1.0    1.0    1.0  1.0

    , V4   1.0    (-1.0)  (-1.0) 1.0
    , V4   1.0    (-1.0)    1.0  1.0
    , V4 (-1.0)   (-1.0)    1.0  1.0

    , V4   1.0    (-1.0)  (-1.0) 1.0
    , V4 (-1.0)   (-1.0)    1.0  1.0
    , V4 (-1.0)   (-1.0)  (-1.0) 1.0
    ]

--  Two UV coordinatesfor each vertex. They were created with Blender.
g_uv_buffer_data =
    [ V2 0.0 1.0
    , V2 0.0 0.0
    , V2 1.0 0.0
    , V2 0.0 1.0
    , V2 1.0 0.0
    , V2 1.0 1.0
    , V2 0.0 1.0
    , V2 1.0 1.0
    , V2 1.0 0.0
    , V2 0.0 1.0
    , V2 1.0 0.0
    , V2 0.0 0.0
    , V2 1.0 1.0
    , V2 0.0 0.0
    , V2 1.0 0.0
    , V2 1.0 1.0
    , V2 0.0 1.0
    , V2 0.0 0.0
    , V2 0.0 1.0
    , V2 1.0 0.0
    , V2 0.0 0.0
    , V2 0.0 1.0
    , V2 1.0 1.0
    , V2 1.0 0.0
    , V2 0.0 1.0
    , V2 1.0 1.0
    , V2 1.0 0.0
    , V2 0.0 1.0
    , V2 1.0 0.0
    , V2 0.0 0.0
    , V2 0.0 1.0
    , V2 0.0 0.0
    , V2 1.0 0.0
    , V2 0.0 1.0
    , V2 1.0 0.0
    , V2 1.0 1.0
    ]

cubeMesh = Mesh
  { mAttributes = Map.fromList
        [ ("position4", A_V4F $ V.fromList g_vertex_buffer_data)
        , ("vertexUV",  A_V2F $ V.fromList g_uv_buffer_data)
        ]
  , mPrimitive = P_Triangles
  }

vec4ToV4F (Vec4 x y z w) = V4 x y z w
mat4ToM44F (Mat4 a b c d) = V4 (vec4ToV4F a) (vec4ToV4F b) (vec4ToV4F c) (vec4ToV4F d)

-- | Camera transformation matrix.
lookat :: Vec3   -- ^ Camera position.
       -> Vec3   -- ^ Target position.
       -> Vec3   -- ^ Upward direction.
       -> Proj4
lookat pos target up = translateBefore4 (neg pos) (orthogonal $ toOrthoUnsafe r)
  where
    w = normalize $ pos &- target
    u = normalize $ up &^ w
    v = w &^ u
    r = transpose $ Mat3 u v w

-- | Perspective transformation matrix in row major order.
perspective :: Float  -- ^ Near plane clipping distance (always positive).
            -> Float  -- ^ Far plane clipping distance (always positive).
            -> Float  -- ^ Field of view of the y axis, in radians.
            -> Float  -- ^ Aspect ratio, i.e. screen's width\/height.
            -> Mat4
perspective n f fovy aspect = transpose $
    Mat4 (Vec4 (2*n/(r-l))       0       (-(r+l)/(r-l))        0)
         (Vec4     0        (2*n/(t-b))  ((t+b)/(t-b))         0)
         (Vec4     0             0       (-(f+n)/(f-n))  (-2*f*n/(f-n)))
         (Vec4     0             0            (-1)             0)
  where
    t = n*tan(fovy/2)
    b = -t
    r = aspect*t
    l = -r
