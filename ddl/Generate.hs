{-# LANGUAGE OverloadedStrings, FlexibleInstances #-}
import qualified Data.Text.Lazy as LText
import           Text.EDE
import           Text.EDE.Filters

import           Data.HashMap.Strict          (HashMap)
import qualified Data.HashMap.Strict          as HashMap
import           Data.Text                    (Text)
import qualified Data.Map as Map

import Data.Time.Clock

import Definitions
import Language

instance Unquote [Field]
instance Unquote [Char]
instance Quote [Char]
instance Unquote DataDef
instance Unquote Type

main :: IO ()
main = do
  irHs <- eitherParseFile "templates/data.hs.ede"
  irPs <- eitherParseFile "templates/data.purs.ede"
  let generate name def = do
        dt <- getCurrentTime
        let env = fromPairs
              [ "dataAndType" .= def
              , "definitions" .= [a | a@DataDef{} <- def ]
              , "moduleName"  .= name
              , "dateTime"    .= dt
              ]
            aliasMap = Map.fromList [(n,t) | TypeAlias n t <- def]
            mylib :: HashMap Text Term
            mylib = HashMap.fromList
                -- boolean
                [ "hasFieldNames" @: hasFieldNames
                , "parens"        @: parens
                , "constType"     @: constType
                , "hsType"        @: hsType aliasMap
                , "psType"        @: psType aliasMap
                ]

        -- Haskell
        either error (\x -> writeFile ("out/" ++ name ++ ".hs") $ LText.unpack x) $ irHs >>= (\t -> eitherRenderWith mylib t env)
        -- Purescript
        either error (\x -> writeFile ("out/" ++ name ++ ".purs") $ LText.unpack x) $ irPs >>= (\t -> eitherRenderWith mylib t env)
  generate "IR" ir
  generate "Mesh" mesh
  generate "TypeInfo" typeInfo
