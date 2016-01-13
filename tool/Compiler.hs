-- {-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
import Options.Applicative
import Data.Aeson
import qualified Data.ByteString.Lazy as B
import LambdaCube.Compiler.Driver
import System.FilePath
import Paths_lambdacube_compiler (getDataDir)

data Config
  = Config
  { srcName :: String
  , backend :: Backend
  , sourceDir :: FilePath
  }

sample :: Parser Config
sample = Config
  <$> argument str (metavar "SOURCE_FILE")
  <*> flag OpenGL33 WebGL1 (long "webgl" <> help "generate WebGL 1.0 pipeline" )
  <*> pure "/lc"

main :: IO ()
main = do
  cabalDataDir <- getDataDir
  cfg <- execParser opts
  compile (cfg {sourceDir = cabalDataDir </> "lc"})
  where
    opts = info (helper <*> sample)
      ( fullDesc
     <> progDesc "compiles LambdaCube graphics pipeline source to JSON IR"
     <> header "LambdaCube 3D compiler" )

compile :: Config -> IO ()
compile Config{..} = do
  pplRes <- compileMain [".", sourceDir] backend srcName
  case pplRes of
    Left err -> putStrLn err
    Right ppl -> do
      B.writeFile (srcName <> ".json") $ encode ppl
