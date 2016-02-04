{-# LANGUAGE RecordWildCards #-}
import Options.Applicative
import Data.Aeson
import qualified Data.ByteString.Lazy as B
import System.FilePath

import LambdaCube.Compiler

data Config
  = Config
  { srcName :: String
  , backend :: Backend
  , includePaths :: [FilePath]
  }

sample :: Parser Config
sample = Config
  <$> argument str (metavar "SOURCE_FILE")
  <*> flag OpenGL33 WebGL1 (long "webgl" <> help "generate WebGL 1.0 pipeline" )
  <*> pure ["."]

main :: IO ()
main = compile =<< execParser opts
  where
    opts = info (helper <*> sample)
      ( fullDesc
     <> progDesc "compiles LambdaCube graphics pipeline source to JSON IR"
     <> header "LambdaCube 3D compiler" )

compile :: Config -> IO ()
compile Config{..} = do
  let dropExt n | takeExtension n == ".lc"  = dropExtension n
      dropExt n = n
      baseName = dropExt srcName
  pplRes <- compileMain includePaths backend baseName
  case pplRes of
    Left err -> putStrLn err
    Right ppl -> B.writeFile (baseName <> ".json") $ encode ppl
