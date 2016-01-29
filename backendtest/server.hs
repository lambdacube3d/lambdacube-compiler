{-# LANGUAGE OverloadedStrings, LambdaCase, RecordWildCards #-}
import Control.Monad
import Control.Concurrent
import Control.Exception (finally)
import Data.Aeson
import Foreign
import Codec.Picture as Juicy
import qualified Data.ByteString as BS
import qualified Data.ByteString.Base64 as B64
import Data.ByteString.Char8 (unpack)
import qualified Data.Vector as V
import qualified Data.Vector.Storable as SV
import qualified Network.WebSockets as WS
import qualified Data.Map as Map
import Text.Printf
import System.Directory

import TestData
import LambdaCube.Linear
import LambdaCube.IR
import LambdaCube.PipelineSchema
import LambdaCube.PipelineSchemaUtil
import LambdaCube.Mesh

main :: IO ()
main = do
  putStrLn "listening"
  WS.runServer "192.168.0.12" 9160 application

application pending = do
  conn <- WS.acceptRequest pending
  WS.forkPingThread conn 30
  let disconnect = return ()
  flip finally disconnect $ do
    -- receive client info
    decodeStrict <$> WS.receiveData conn >>= \case
      Nothing -> putStrLn "invalid client info"
      Just ci@ClientInfo{..} -> print ci
    -- send pipeline
    renderJob@RenderJob{..} <- testRenderJob
    WS.sendTextData conn . encode $ renderJob
    -- TODO: get render result: pipeline x scene x frame
    forM_ [1..length pipelines] $ \pIdx ->
      forM_ (zip [1..] $ V.toList scenes) $ \(sIdx,Scene{..}) ->
        forM_ [1..length frames] $ \fIdx -> do
          decodeStrict <$> WS.receiveData conn >>= \case
            Nothing -> putStrLn "invalid RenderJobResult"
            Just (RenderJobError e) -> putStrLn $ "render error: " ++ e -- TODO: test failed
            Just (RenderJobResult FrameResult{..}) -> do
              let name = "out/output_ppl" ++ show pIdx ++ "_scn" ++ show sIdx ++ "_" ++ show fIdx ++ ".png"
              compareOrSaveImage name =<< toImage frImageWidth frImageHeight . either error id . B64.decode =<< WS.receiveData conn
              putStrLn $ name ++ "\t" ++ unwords (map showTime . V.toList $ frRenderTimes)
    putStrLn "render job done"
    forever $ threadDelay 1000000

compareOrSaveImage name img@(Image w h pixels) = do
  doesFileExist name >>= \case
    False -> do
      putStrLn $ "save image: " ++ name
      savePngImage name (ImageRGBA8 img)
    True -> do
      Right (ImageRGBA8 (Image origW origH origPixels)) <- readImage name
      let diffPixels a b = SV.sum $ SV.zipWith (\x y -> (fromIntegral x - fromIntegral y)^2) a b :: Float
          diff = diffPixels pixels origPixels
          threshold = 0
      case (w /= origW || h /= origH || diff > threshold) of
        True -> do
          putStrLn $ "images differ!!! " ++ show diff
        False -> putStrLn $ "image match " ++ show diff

toImage :: Int -> Int -> BS.ByteString -> IO (Image PixelRGBA8)
toImage w h buf = do
    fp <- mallocForeignPtrBytes (4*w*h)
    withForeignPtr fp $ \dst -> BS.useAsCStringLen buf $ \(src,i) -> copyBytes dst (castPtr src) i
    return $ Image w h $ SV.unsafeFromForeignPtr fp 0 (w*h)

showTime delta
    | t > 1e-1  = printf "%.3fs" t
    | t > 1e-3  = printf "%.1fms" (t/1e-3)
    | otherwise = printf "%.0fus" (t/1e-6)
  where
    t = realToFrac delta :: Double

{-
  data sets:
    hello
    editor
-}
{-
  features to test:
    blending
    depth test
    culling
    texturing
      uniform texture
      render texture
    multi draw calls into the same framebuffer
-}
-- TODO
{-
  how to pair pipelines with predefined data
  basically: storage - pipelines
    render job:
      gpu data
        scene <--> storage
          frame
-}
{-
  initial test cases:
    - hello - done
    - editor exercises
      TODO
        create storage
        collect pipelines
    - create render job list
-}
testRenderJob = do
  let triangleA = Mesh
        { mAttributes   = Map.fromList
            [ ("position",  A_V2F $ V.fromList [V2 1 1, V2 1 (-1), V2 (-1) (-1)])
            , ("uv",        A_V2F $ V.fromList [V2 1 1, V2 0 1, V2 0 0])
            ]
        , mPrimitive    = P_Triangles
        }

      triangleB = Mesh
        { mAttributes   = Map.fromList
            [ ("position",  A_V2F $ V.fromList [V2 1 1, V2 (-1) (-1), V2 (-1) 1])
            , ("uv",        A_V2F $ V.fromList [V2 1 1, V2 0 0, V2 1 0])
            ]
        , mPrimitive    = P_Triangles
        }
      inputSchema = makeSchema $ do
          defObjectArray "objects" Triangles $ do
            "position"  @: Attribute_V2F
            "uv"        @: Attribute_V2F
          defUniforms $ do
            "time"           @: Float
            "diffuseTexture" @: FTexture2D
      frame t = Frame
                  { renderCount   = 10
                  , frameUniforms = Map.fromList [("time",VFloat t)]
                  , frameTextures = Map.fromList [("diffuseTexture",0)]
                  }

      scene wh = Scene
        { objectArrays        = Map.fromList [("objects", V.fromList [0,1])]
        , renderTargetWidth   = wh
        , renderTargetHeight  = wh
        , frames              = V.fromList [frame t | t <- [0,0.3..6]]
        }

  img <- unpack . B64.encode <$> BS.readFile "logo.png"
  Just ppl <- decodeStrict <$> BS.readFile "hello.json"

  return $ RenderJob
    { meshes      = V.fromList [triangleA,triangleB]
    , textures    = V.fromList [img]
    , schema      = inputSchema
    , scenes      = V.fromList [scene (2^s) | s <- [1..9]]
    , pipelines   = V.fromList [ppl]
    }
