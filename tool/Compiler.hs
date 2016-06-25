import Control.Monad
import Options.Applicative
import Data.Aeson
import qualified Data.ByteString.Lazy as B
import System.FilePath
import Data.Version
import Paths_lambdacube_compiler (version)

import LambdaCube.Compiler

addInfo i p = info (helper <*> p) i

main :: IO ()
main = join $ execParser $ addInfo i $ versionOption <*> subparser (
    command "compile" (addInfo (progDesc "compiles LambdaCube3D source to JSON IR") compile')
 <> command "parse" (addInfo (progDesc "parses LambdaCube3D source") $ parse
          <$> argument str (metavar "SOURCE_FILE")
          <*> flag OpenGL33 WebGL1 (long "webgl" <> help "generate WebGL 1.0 pipeline" )
          <*> pure ["."]
          <*> optional (strOption (long "output" <> short 'o' <> metavar "FILENAME" <> help "output file name"))
    )
 <> command "pretty" (addInfo (progDesc "pretty prints JSON IR") $ prettyPrint
      <$> argument str (metavar "SOURCE_FILE")
      <*> optional (strOption (long "output" <> short 'o' <> metavar "FILENAME" <> help "output file name"))
    )) <|> compile'
  where
    compile' = (compile
          <$> argument str (metavar "SOURCE_FILE")
          <*> flag OpenGL33 WebGL1 (long "webgl" <> help "generate WebGL 1.0 pipeline" )
          <*> pure ["."]
          <*> optional (strOption (long "output" <> short 'o' <> metavar "FILENAME" <> help "output file name"))
        )

    i = fullDesc
     <> progDesc "executes command (default to compile if no command is given)"
     <> header versionStr

versionStr :: String
versionStr = "LambdaCube 3D compiler " ++ showVersion version

versionOption :: Parser (a -> a)
versionOption = abortOption (InfoMsg versionStr) $ mconcat
    [ long "version"
    , short 'v'
    , help "Print version."
    ]

prettyPrint srcName output = do
      let baseName = dropExtension srcName
          withOutName n = maybe n id output
      json <- B.readFile srcName
      case eitherDecode json :: Either String Pipeline of
        Left err -> putStrLn err
        Right ppl -> writeFile (withOutName $ baseName <> ".ppl") $ prettyShowUnlines ppl

parse srcName backend includePaths output = do
    pplRes <- parseModule includePaths srcName
    case pplRes of
        Left err -> fail $ show err
        Right ppl -> maybe (putStrLn ppl) (`writeFile` ppl) output

compile srcName backend includePaths output = do
  let ext = takeExtension srcName
      baseName | ext == ".lc" = dropExtension srcName
               | otherwise = srcName
      withOutName n = maybe n id output
  do
      pplRes <- compileMain includePaths backend srcName
      case pplRes of
        Left err -> fail $ show err
        Right ppl -> B.writeFile (withOutName $ baseName <> ".json") $ encode ppl
--          True -> writeFile (withOutName $ baseName <> ".ppl") $ prettyShowUnlines ppl

