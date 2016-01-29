-- generated file, do not modify!
-- 2016-01-28T13:15:31.27456Z

{-# LANGUAGE OverloadedStrings, RecordWildCards #-}
module TestData where

import Data.Int
import Data.Word
import Data.Map
import Data.Vector (Vector(..))
import LambdaCube.Linear

import Data.Text
import Data.Aeson hiding (Value,Bool)
import Data.Aeson.Types hiding (Value,Bool)
import Control.Monad

import LambdaCube.IR
import LambdaCube.Mesh
import LambdaCube.PipelineSchema

data ClientInfo
  = ClientInfo
  { clientName :: String
  , clientBackend :: Backend
  }

  deriving (Show, Eq, Ord)

data Frame
  = Frame
  { renderCount :: Int
  , frameUniforms :: Map String Value
  , frameTextures :: Map String Int
  }

  deriving (Show, Eq, Ord)

data Scene
  = Scene
  { objectArrays :: Map String (Vector Int)
  , renderTargetWidth :: Int
  , renderTargetHeight :: Int
  , frames :: Vector Frame
  }

  deriving (Show, Eq, Ord)

data RenderJob
  = RenderJob
  { meshes :: Vector Mesh
  , textures :: Vector String
  , schema :: PipelineSchema
  , scenes :: Vector Scene
  , pipelines :: Vector Pipeline
  }

  deriving (Show, Eq, Ord)

data FrameResult
  = FrameResult
  { frRenderTimes :: Vector Float
  , frImageWidth :: Int
  , frImageHeight :: Int
  }

  deriving (Show, Eq, Ord)

data RenderJobResult
  = RenderJobResult FrameResult
  | RenderJobError String
  deriving (Show, Eq, Ord)


instance ToJSON ClientInfo where
  toJSON v = case v of
    ClientInfo{..} -> object
      [ "tag" .= ("ClientInfo" :: Text)
      , "clientName" .= clientName
      , "clientBackend" .= clientBackend
      ]

instance FromJSON ClientInfo where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "ClientInfo" -> do
        clientName <- obj .: "clientName"
        clientBackend <- obj .: "clientBackend"
        pure $ ClientInfo
          { clientName = clientName
          , clientBackend = clientBackend
          } 
  parseJSON _ = mzero

instance ToJSON Frame where
  toJSON v = case v of
    Frame{..} -> object
      [ "tag" .= ("Frame" :: Text)
      , "renderCount" .= renderCount
      , "frameUniforms" .= frameUniforms
      , "frameTextures" .= frameTextures
      ]

instance FromJSON Frame where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "Frame" -> do
        renderCount <- obj .: "renderCount"
        frameUniforms <- obj .: "frameUniforms"
        frameTextures <- obj .: "frameTextures"
        pure $ Frame
          { renderCount = renderCount
          , frameUniforms = frameUniforms
          , frameTextures = frameTextures
          } 
  parseJSON _ = mzero

instance ToJSON Scene where
  toJSON v = case v of
    Scene{..} -> object
      [ "tag" .= ("Scene" :: Text)
      , "objectArrays" .= objectArrays
      , "renderTargetWidth" .= renderTargetWidth
      , "renderTargetHeight" .= renderTargetHeight
      , "frames" .= frames
      ]

instance FromJSON Scene where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "Scene" -> do
        objectArrays <- obj .: "objectArrays"
        renderTargetWidth <- obj .: "renderTargetWidth"
        renderTargetHeight <- obj .: "renderTargetHeight"
        frames <- obj .: "frames"
        pure $ Scene
          { objectArrays = objectArrays
          , renderTargetWidth = renderTargetWidth
          , renderTargetHeight = renderTargetHeight
          , frames = frames
          } 
  parseJSON _ = mzero

instance ToJSON RenderJob where
  toJSON v = case v of
    RenderJob{..} -> object
      [ "tag" .= ("RenderJob" :: Text)
      , "meshes" .= meshes
      , "textures" .= textures
      , "schema" .= schema
      , "scenes" .= scenes
      , "pipelines" .= pipelines
      ]

instance FromJSON RenderJob where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "RenderJob" -> do
        meshes <- obj .: "meshes"
        textures <- obj .: "textures"
        schema <- obj .: "schema"
        scenes <- obj .: "scenes"
        pipelines <- obj .: "pipelines"
        pure $ RenderJob
          { meshes = meshes
          , textures = textures
          , schema = schema
          , scenes = scenes
          , pipelines = pipelines
          } 
  parseJSON _ = mzero

instance ToJSON FrameResult where
  toJSON v = case v of
    FrameResult{..} -> object
      [ "tag" .= ("FrameResult" :: Text)
      , "frRenderTimes" .= frRenderTimes
      , "frImageWidth" .= frImageWidth
      , "frImageHeight" .= frImageHeight
      ]

instance FromJSON FrameResult where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "FrameResult" -> do
        frRenderTimes <- obj .: "frRenderTimes"
        frImageWidth <- obj .: "frImageWidth"
        frImageHeight <- obj .: "frImageHeight"
        pure $ FrameResult
          { frRenderTimes = frRenderTimes
          , frImageWidth = frImageWidth
          , frImageHeight = frImageHeight
          } 
  parseJSON _ = mzero

instance ToJSON RenderJobResult where
  toJSON v = case v of
    RenderJobResult arg0 -> object [ "tag" .= ("RenderJobResult" :: Text), "arg0" .= arg0]
    RenderJobError arg0 -> object [ "tag" .= ("RenderJobError" :: Text), "arg0" .= arg0]

instance FromJSON RenderJobResult where
  parseJSON (Object obj) = do
    tag <- obj .: "tag"
    case tag :: Text of
      "RenderJobResult" -> RenderJobResult <$> obj .: "arg0"
      "RenderJobError" -> RenderJobError <$> obj .: "arg0"
  parseJSON _ = mzero

