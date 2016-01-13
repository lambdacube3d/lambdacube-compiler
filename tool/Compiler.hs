{-# LANGUAGE RecordWildCards #-}
import Options.Applicative
import Data.Aeson
import qualified Data.ByteString.Lazy as B
import LambdaCube.Compiler.Driver

data Config
  = Config
  { srcName :: String
  , backend :: Backend
  }

sample :: Parser Config
sample = Config
  <$> argument str (metavar "SOURCE_FILE")
  <*> flag OpenGL33 WebGL1 (long "webgl" <> help "generate WebGL 1.0 pipeline" )

main :: IO ()
main = execParser opts >>= compile
  where
    opts = info (helper <*> sample)
      ( fullDesc
     <> progDesc "compiles LambdaCube graphics pipeline source to JSON IR"
     <> header "LambdaCube 3D compiler" )

compile :: Config -> IO ()
compile Config{..} = do
  pplRes <- compileMain ["."] backend srcName
  case pplRes of
    Left err -> putStrLn err
    Right ppl -> do
      B.writeFile (srcName <> ".json") $ encode ppl
