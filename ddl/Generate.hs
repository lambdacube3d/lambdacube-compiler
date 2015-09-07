{-# LANGUAGE OverloadedStrings, FlexibleInstances #-}
import qualified Data.Text.Lazy as LText
import           Text.EDE
import           Text.EDE.Filters

import           Data.HashMap.Strict          (HashMap)
import qualified Data.HashMap.Strict          as Map
import           Data.Text                    (Text)

import Data.Time.Clock

import Definitions
import Language

instance Unquote [Field]
instance Unquote [Char]
instance Quote [Char]
instance Unquote DataDef
instance Unquote Type

mylib :: HashMap Text Term
mylib = Map.fromList
    -- boolean
    [ "hasFieldNames" @: hasFieldNames
    , "parens"        @: parens
    , "constType"     @: constType
    , "hsType"        @: hsType
    , "psType"        @: psType
    ]


main :: IO ()
main = do
  irHs <- eitherParseFile "templates/data.hs.ede"
  irEncodeHs <- eitherParseFile "templates/encode.hs.ede"
  irDecodeHs <- eitherParseFile "templates/decode.hs.ede"
  irPs <- eitherParseFile "templates/data.purs.ede"
  irEncodePs <- eitherParseFile "templates/encode.purs.ede"
  irDecodePs <- eitherParseFile "templates/decode.purs.ede"
  let generate name def = do
        dt <- getCurrentTime
        let env = fromPairs
              [ "dataAndType" .= def
              , "definitions" .= [a | a@DataDef{} <- def ]
              , "moduleName"  .= name
              , "dateTime"    .= dt
              ]
        -- Haskell
        either error (\x -> writeFile ("out/" ++ name ++ ".hs") $ LText.unpack x) $ irHs >>= (\t -> eitherRenderWith mylib t env)
        either error (\x -> writeFile ("out/" ++ name ++ "Encode.hs") $ LText.unpack x) $ irEncodeHs >>= (\t -> eitherRenderWith mylib t env)
        either error (\x -> writeFile ("out/" ++ name ++ "Decode.hs") $ LText.unpack x) $ irDecodeHs >>= (\t -> eitherRenderWith mylib t env)
        -- Purescript
        either error (\x -> writeFile ("out/" ++ name ++ ".purs") $ LText.unpack x) $ irPs >>= (\t -> eitherRenderWith mylib t env)
        either error (\x -> writeFile ("out/" ++ name ++ "Encode.purs") $ LText.unpack x) $ irEncodePs >>= (\t -> eitherRenderWith mylib t env)
        either error (\x -> writeFile ("out/" ++ name ++ "Decode.purs") $ LText.unpack x) $ irDecodePs >>= (\t -> eitherRenderWith mylib t env)
  generate "IR" ir
