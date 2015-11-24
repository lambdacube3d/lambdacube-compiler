{-# LANGUAGE OverloadedStrings, FlexibleInstances #-}
import qualified Data.Text.Lazy as LText
import           Text.EDE
import           Text.EDE.Filters

import           Data.HashMap.Strict          (HashMap)
import qualified Data.HashMap.Strict          as HashMap
import           Data.Text                    (Text)
import qualified Data.Map as Map

import Data.Time.Clock
import Control.Monad.Writer

import Definitions
import Language

instance Unquote [Field]
instance Unquote [Char]
instance Quote [Char]
instance Unquote DataDef
instance Unquote Type

main :: IO ()
main = do
  dataSwift <- eitherParseFile "templates/data.swift.ede"
  dataJava <- eitherParseFile "templates/data.java.ede"
  dataHpp <- eitherParseFile "templates/data.hpp.ede"
  dataHpp2 <- eitherParseFile "templates/data.hpp2.ede"
  dataCpp <- eitherParseFile "templates/data.cpp.ede"
  dataCs <- eitherParseFile "templates/data.cs.ede"
  dataHs <- eitherParseFile "templates/data.hs.ede"
  dataPs <- eitherParseFile "templates/data.purs.ede"
  let generate (ModuleDef name imports def) = do
        dt <- getCurrentTime
        let env = fromPairs
              [ "dataAndType" .= def
              , "definitions" .= [a | a@DataDef{} <- def ]
              , "moduleName"  .= name
              , "dateTime"    .= dt
              , "imports"     .= imports
              ]
            aliasMap = Map.fromList [(n,t) | TypeAlias n t <- def]
            mylib :: HashMap Text Term
            mylib = HashMap.fromList
                [ "hasFieldNames"   @: hasFieldNames
                , "parens"          @: parens
                , "constType"       @: constType
                , "hsType"          @: hsType aliasMap
                , "psType"          @: psType aliasMap
                , "cppType"         @: cppType aliasMap
                , "csType"          @: csType aliasMap
                , "javaType"        @: javaType aliasMap
                , "swiftType"       @: swiftType aliasMap
                ]

        -- Haskell
        either error (\x -> writeFile ("out/" ++ name ++ ".hs") $ LText.unpack x) $ dataHs >>= (\t -> eitherRenderWith mylib t env)
        -- Purescript
        either error (\x -> writeFile ("out/" ++ name ++ ".purs") $ LText.unpack x) $ dataPs >>= (\t -> eitherRenderWith mylib t env)
        -- C++
        either error (\x -> writeFile ("out/" ++ name ++ "2.hpp") $ LText.unpack x) $ dataHpp2 >>= (\t -> eitherRenderWith mylib t env)
        either error (\x -> writeFile ("out/" ++ name ++ ".hpp") $ LText.unpack x) $ dataHpp >>= (\t -> eitherRenderWith mylib t env)
        either error (\x -> writeFile ("out/" ++ name ++ ".cpp") $ LText.unpack x) $ dataCpp >>= (\t -> eitherRenderWith mylib t env)
        {-
        -- Java
        either error (\x -> writeFile ("out/" ++ name ++ ".java") $ LText.unpack x) $ dataJava >>= (\t -> eitherRenderWith mylib t env)
        -- C#
        either error (\x -> writeFile ("out/" ++ name ++ ".cs") $ LText.unpack x) $ dataCs >>= (\t -> eitherRenderWith mylib t env)
        -}
        -- Swift
        either error (\x -> writeFile ("out/" ++ name ++ ".swift") $ LText.unpack x) $ dataSwift >>= (\t -> eitherRenderWith mylib t env)
  mapM_ generate $ execWriter modules
