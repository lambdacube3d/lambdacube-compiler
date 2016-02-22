{-# LANGUAGE RecordWildCards #-}
import Options.Applicative
import Data.Aeson
import qualified Data.ByteString.Lazy as B
import System.FilePath
import Data.Version
import Paths_lambdacube_compiler (version)

import LambdaCube.Compiler

data Config
  = Config
  { srcName :: String
  , backend :: Backend
  , includePaths :: [FilePath]
  , pretty :: Bool
  , output :: Maybe String
  }

sample :: Parser Config
sample = Config
  <$> argument str (metavar "SOURCE_FILE")
  <*> flag OpenGL33 WebGL1 (long "webgl" <> help "generate WebGL 1.0 pipeline" )
  <*> pure ["."]
  <*> switch (long "pretty" <> help "pretty prints pipeline")
  <*> optional (strOption (long "output" <> short 'o' <> metavar "FILENAME" <> help "output file name"))

main :: IO ()
main = compile =<< execParser opts
  where
    opts = info (helper <*> sample)
      ( fullDesc
     <> progDesc "compiles LambdaCube graphics pipeline source to JSON IR"
     <> header ("LambdaCube 3D compiler " ++ showVersion version))

compile :: Config -> IO ()
compile cfg@Config{..} = do
  let ext = takeExtension srcName
      baseName | ext == ".lc" = dropExtension srcName
               | otherwise = srcName
      withOutName n = maybe n id output
  case ext of
    ".json" | pretty -> prettyPrint cfg
    _ -> do
      pplRes <- compileMain includePaths backend srcName
      case pplRes of
        Left err -> fail err
        Right ppl -> case pretty of
          False -> B.writeFile (withOutName $ baseName <> ".json") $ encode ppl
          True -> writeFile (withOutName $ baseName <> ".ppl") $ prettyShowUnlines ppl

prettyPrint :: Config -> IO ()
prettyPrint Config{..} = do
  let baseName = dropExtension srcName
      withOutName n = maybe n id output
  json <- B.readFile srcName
  case eitherDecode json :: Either String Pipeline of
    Left err -> putStrLn err
    Right ppl -> writeFile (withOutName $ baseName <> ".ppl") $ prettyShowUnlines ppl

