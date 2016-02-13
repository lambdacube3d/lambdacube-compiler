{-# LANGUAGE RecordWildCards #-}
import Options.Applicative
import Data.Aeson
import qualified Data.ByteString.Lazy as B
import System.FilePath
import qualified Text.Show.Pretty as PP
import Data.Version
import Paths_lambdacube_compiler (version)

import LambdaCube.Compiler

data Config
  = Config
  { srcName :: String
  , backend :: Backend
  , includePaths :: [FilePath]
  , pretty :: Bool
  }

sample :: Parser Config
sample = Config
  <$> argument str (metavar "SOURCE_FILE")
  <*> flag OpenGL33 WebGL1 (long "webgl" <> help "generate WebGL 1.0 pipeline" )
  <*> pure ["."]
  <*> switch (long "pretty" <> help "pretty prints pipeline")

main :: IO ()
main = compile =<< execParser opts
  where
    opts = info (helper <*> sample)
      ( fullDesc
     <> progDesc "compiles LambdaCube graphics pipeline source to JSON IR"
     <> header ("LambdaCube 3D compiler " ++ showVersion version))

compile :: Config -> IO ()
compile Config{..} = do
  let ext = takeExtension srcName
      baseName | ext == ".lc" = dropExtension srcName
               | otherwise = srcName
  case ext of
    ".json" | pretty -> prettyPrint srcName
    _ -> do
      pplRes <- compileMain includePaths backend baseName
      case pplRes of
        Left err -> putStrLn err
        Right ppl -> case pretty of
          False -> B.writeFile (baseName <> ".json") $ encode ppl
          True -> writeFile (baseName <> ".ppl") $ ppUnlines $ PP.ppShow ppl

prettyPrint :: String -> IO ()
prettyPrint srcName = do
  let baseName = dropExtension srcName
  json <- B.readFile srcName
  case eitherDecode json :: Either String Pipeline of
    Left err -> putStrLn err
    Right ppl -> writeFile (baseName <> ".ppl") $ ppUnlines $ PP.ppShow ppl

ppUnlines :: String -> String
ppUnlines = goPP 0
  where goPP _ [] = []
        goPP n ('"':xs) | isMultilineString xs = "\"\"\"\n" ++ indent ++ go xs where
          indent = replicate n ' '
          go ('\\':'n':xs) = "\n" ++ indent ++ go xs
          go ('\\':c:xs) = '\\':c:go xs
          go ('"':xs) = "\n" ++ indent ++ "\"\"\"" ++ goPP n xs
          go (x:xs) = x : go xs
        goPP n (x:xs) = x : goPP (if x == '\n' then 0 else n+1) xs

        isMultilineString ('\\':'n':xs) = True
        isMultilineString ('\\':c:xs) = isMultilineString xs
        isMultilineString ('"':xs) = False
        isMultilineString (x:xs) = isMultilineString xs
        isMultilineString [] = False
