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
import System.FilePath
import System.Directory
import System.Process

import TestData
import LambdaCube.Linear
import LambdaCube.IR
import LambdaCube.PipelineSchema
import LambdaCube.PipelineSchemaUtil
import LambdaCube.Mesh

import qualified EditorExamplesTest

main :: IO ()
main = do
  putStrLn "listening"
  WS.runServer "192.168.0.12" 9160 application

application pending = do
  conn <- WS.acceptRequest pending
  WS.forkPingThread conn 30
  let disconnect = return ()
      one = 1 :: Int
  flip finally disconnect $ do
    -- receive client info
    decodeStrict <$> WS.receiveData conn >>= \case
      Nothing -> fail "invalid client info"
      Just ci@ClientInfo{..} -> print ci
    -- send pipeline
    (testName,renderJob@RenderJob{..}) <- EditorExamplesTest.getRenderJob -- TODO
    WS.sendTextData conn . encode $ renderJob
    -- get render result: pipeline x scene x frame
    res <- forM pipelines $ \PipelineInfo{..} -> do
      forM (zip [one..] $ V.toList scenes) $ \(sIdx,Scene{..}) ->
        forM [one..length frames] $ \fIdx -> do
          let name = "backend-test-data/" ++ testName ++ "/result/" ++ takeBaseName pipelineName ++ "_scn" ++ printf "%02d" sIdx ++ "_" ++ printf "%02d" fIdx ++ ".png"
          decodeStrict <$> WS.receiveData conn >>= \case
            Nothing -> fail $ name ++ " - invalid RenderJobResult"
            Just (RenderJobError e) -> fail $ name ++ " - render error:\n" ++ e -- TODO: test failed
            Just (RenderJobResult FrameResult{..}) -> do
              createDirectoryIfMissing True (takeDirectory name)
              compareOrSaveImage name =<< toImage frImageWidth frImageHeight . either error id . B64.decode =<< WS.receiveData conn
              --putStrLn $ name ++ "\t" ++ unwords (map showTime . V.toList $ frRenderTimes)
    let differ = or $ concat $ fmap concat res
    putStrLn $ "render job: " ++ if differ then "FAIL" else "OK"
    forever $ threadDelay 1000000

compareOrSaveImage name img@(Image w h pixels) = do
  doesFileExist name >>= \case
    False -> do
      putStrLn $ "new image: " ++ name
      savePngImage name (ImageRGBA8 img)
      return False
    True -> do
      Right (ImageRGBA8 (Image origW origH origPixels)) <- readImage name
      let diffPixels a b = SV.sum $ SV.zipWith (\x y -> (fromIntegral x - fromIntegral y)^2) a b :: Float
          diff = diffPixels pixels origPixels
          threshold = 0
          differ = w /= origW || h /= origH || diff > threshold
      case differ of
        True -> do
          putStrLn $ name ++ " - differ!!! " ++ show diff
          let mismatchImage = dropExtension name ++ "_mismatch.png"
              diffImage = dropExtension name ++ "_diff.png"
          putStrLn $ "save difference: " ++ diffImage
          savePngImage mismatchImage (ImageRGBA8 img)
          (exitCode,out,err) <- readProcessWithExitCode "compare" ["-compose","src",name,mismatchImage,diffImage] ""
          --let res = read . head . words $ out :: Float
          print (out,err)
        False -> putStrLn $ name ++ " OK"
      return differ

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
