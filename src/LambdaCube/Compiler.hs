{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}  -- instance MonadMask m => MonadMask (ExceptT e m)
module LambdaCube.Compiler
    ( Backend(..)
    , Pipeline
    , module Exported

    , MMT, runMMT, mapMMT
    , MM, runMM
    , Err
    , catchMM, catchErr
    , ioFetch
    , getDef, compileMain, preCompile
    , removeFromCache

    , compilePipeline
    , ppShow
    , prettyShowUnlines
    ) where

import Data.Char
import Data.List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Except
import Control.Monad.Identity
import Control.DeepSeq
import Control.Monad.Catch
import Control.Exception hiding (catch, bracket, finally, mask)
import Control.Arrow hiding ((<+>))
import System.Directory
import System.FilePath
--import Debug.Trace
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Text.Show.Pretty as PP

import LambdaCube.IR as IR
import LambdaCube.Compiler.Pretty hiding ((</>))
import LambdaCube.Compiler.Parser (Module(..), Export(..), ImportItems (..), runDefParser, parseLC)
import LambdaCube.Compiler.Lexer as Exported (Range(..))
import LambdaCube.Compiler.Infer (PolyEnv(..), showError, joinPolyEnvs, filterPolyEnv, inference_, extractDesugarInfo)
import LambdaCube.Compiler.Infer as Exported (Infos, listAllInfos, listTypeInfos, listTraceInfos, Exp, outputType, boolType, trueExp)
import LambdaCube.Compiler.CoreToIR

-- inlcude path for: Builtins, Internals and Prelude
import Paths_lambdacube_compiler (getDataDir)

type EName = String
type MName = String

type Modules = Map FilePath (Either Doc (PolyEnv, String))
type ModuleFetcher m = Maybe FilePath -> MName -> m (FilePath, String)

-- todo: use RWS
newtype MMT m a = MMT { runMMT :: ExceptT String (ReaderT (ModuleFetcher (MMT m)) (StateT Modules (WriterT Infos m))) a }
    deriving (Functor, Applicative, Monad, MonadReader (ModuleFetcher (MMT m)), MonadState Modules, MonadError String, MonadIO, MonadThrow, MonadCatch, MonadMask, MonadWriter Infos)
type MM = MMT IO

instance MonadMask m => MonadMask (ExceptT e m) where
    mask f = ExceptT $ mask $ \u -> runExceptT $ f (mapExceptT u)
    uninterruptibleMask = error "not implemented: uninterruptibleMask for ExcpetT"

mapMMT f (MMT m) = MMT $ f m

type Err a = (Either String a, Infos)

runMM :: Monad m => ModuleFetcher (MMT m) -> MMT m a -> m (Err a) 
runMM fetcher
    = runWriterT
    . flip evalStateT mempty
    . flip runReaderT fetcher
    . runExceptT
    . runMMT

catchErr :: (MonadCatch m, NFData a, MonadIO m) => (String -> m a) -> m a -> m a
catchErr er m = (force <$> m >>= liftIO . evaluate) `catch` getErr `catch` getPMatchFail
  where
    getErr (e :: ErrorCall) = catchErr er $ er $ show e
    getPMatchFail (e :: PatternMatchFail) = catchErr er $ er $ show e

catchMM :: Monad m => MMT m a -> (String -> Infos -> MMT m a) -> MMT m a
catchMM m e = mapMMT (lift . mapReaderT (mapStateT $ lift . runWriterT >=> f) . runExceptT) m >>= either (uncurry e) return
  where
    f ((Right x, m), is) = tell is >> return (Right x, m)
    f ((Left e, m), is) = return (Left (e, is), m)

-- TODO: remove dependent modules from cache too
removeFromCache :: Monad m => FilePath -> MMT m ()
removeFromCache f = modify $ Map.delete f

readFileStrict :: FilePath -> IO String
readFileStrict = fmap T.unpack . TIO.readFile

readFile' :: FilePath -> IO (Maybe String)
readFile' fname = do
    b <- doesFileExist fname
    if b then Just <$> readFileStrict fname else return Nothing

ioFetch :: MonadIO m => [FilePath] -> ModuleFetcher (MMT m)
ioFetch paths imp n = do
  preludePath <- (</> "lc") <$> liftIO getDataDir
  let
    f [] = throwError $ show $ "can't find module" <+> hsep (map text fnames)
    f (x:xs) = liftIO (readFile' x) >>= \case
        Nothing -> f xs
        Just src -> do
          --liftIO $ putStrLn $ "loading " ++ x
          return (x, src)
    fnames = map normalise . concatMap lcModuleFile $ nub $ preludePath : paths
    lcModuleFile path = (++ ".lc") <$> g imp
      where
        g Nothing = [path </> n]
        g (Just fn) = [path </> hn, fst (splitMPath fn) </> hn]

        hn = h [] n
        h acc [] = reverse acc
        h acc ('.':cs) = reverse acc </> h [] cs
        h acc (c: cs) = h (c: acc) cs
  f fnames

splitMPath fn = (joinPath as, intercalate "." $ bs ++ [y])
  where
    (as, bs) = span (\x -> null x || x == "." || x == "/" || isLower (head x)) xs
    (xs, y) = map takeDirectory . splitPath *** id $ splitFileName $ dropExtension fn


loadModule :: MonadMask m => Maybe FilePath -> MName -> MMT m (FilePath, PolyEnv)
loadModule imp mname = do
    fetch <- ask
    (fname, src) <- fetch imp mname
    c <- gets $ Map.lookup fname
    case c of
        Just (Right (m, _)) -> return (fname, m)
        Just (Left e) -> throwError $ show $ "cycles in module imports:" <+> pShow mname <+> e
        _ -> do
            e <- either (throwError . show) return $ parseLC fname src
            modify $ Map.insert fname $ Left $ pShow $ map fst $ moduleImports e
            let
                loadModuleImports (m, is) = do
                    filterPolyEnv (filterImports is) . snd <$> loadModule (Just fname) (snd m)
            do
                ms <- mapM loadModuleImports $ moduleImports e
                x' <- {-trace ("loading " ++ fname) $-} do
                    env@(PolyEnv ge _) <- joinPolyEnvs False ms
                    defs <- MMT $ mapExceptT (return . runIdentity) $ runDefParser (extractDesugarInfo ge) $ definitions e
                    srcs <- gets $ Map.mapMaybe (either (const Nothing) (Just . snd))
                    x <- MMT $ mapExceptT (lift . lift . mapWriterT (return . first (left $ showError (Map.insert fname src srcs)) . runIdentity)) $ inference_ env (extensions e) defs
                    case moduleExports e of
                            Nothing -> return x
                            Just es -> joinPolyEnvs False $ flip map es $ \exp -> case exp of
                                ExportId (snd -> d) -> case  Map.lookup d $ getPolyEnv x of
                                    Just def -> PolyEnv (Map.singleton d def) mempty
                                    Nothing  -> error $ d ++ " is not defined"
                                ExportModule (snd -> m) | m == snd (splitMPath mname) -> x
                                ExportModule m -> case [ ms
                                                       | ((m', is), ms) <- zip (moduleImports e) ms, m' == m] of
                                    [PolyEnv x infos] -> PolyEnv x mempty   -- TODO
                                    []  -> error "empty export list"
                                    _   -> error "export list: internal error"
                modify $ Map.insert fname $ Right (x', src)
                return (fname, x')
              `catchMM` (\e is -> modify (Map.delete fname) >> tell is >> throwError e)

filterImports (ImportAllBut ns) = not . (`elem` map snd ns)
filterImports (ImportJust ns) = (`elem` map snd ns)

-- used in runTests
getDef :: MonadMask m => MName -> EName -> Maybe Exp -> MMT m (FilePath, Either String (Exp, Exp), Infos)
getDef m d ty = do
    (fname, pe) <- loadModule Nothing m
    return
      ( fname
      , case Map.lookup d $ getPolyEnv pe of
        Just (e, thy, si)
            | Just False <- (== thy) <$> ty -> Left $ "type of " ++ d ++ " should be " ++ show ty ++ " instead of " ++ ppShow thy     -- TODO: better type comparison
            | otherwise -> Right (e, thy)
        Nothing -> Left $ d ++ " is not found"
      , infos pe
      )

parseAndToCoreMain m = either throwError return . (\(_, e, i) -> flip (,) i <$> e) =<< getDef m "main" (Just outputType)

-- | most commonly used interface for end users
compileMain :: [FilePath] -> IR.Backend -> MName -> IO (Either String IR.Pipeline)
compileMain path backend fname
    = fmap ((id +++ fst) . fst) $ runMM (ioFetch path) $ first (compilePipeline backend) <$> parseAndToCoreMain fname

-- | Removes the escaping characters from the error message
removeEscapes = first (removeEscs +++ id)

-- used by the compiler-service of the online editor
preCompile :: (MonadMask m, MonadIO m) => [FilePath] -> [FilePath] -> Backend -> String -> IO (String -> m (Err (IR.Pipeline, Infos)))
preCompile paths paths' backend mod = do
  res <- runMM (ioFetch paths) $ loadModule Nothing mod
  case res of
    (Left err, i) -> error $ "Prelude could not compiled: " ++ err
    (Right (_, prelude), _) -> return compile
      where
        compile src = fmap removeEscapes . runMM fetch $ do
            modify $ Map.insert ("." </> "Prelude.lc") $ Right (prelude, "<<TODO>>")
            first (compilePipeline backend) <$> parseAndToCoreMain "Main"
          where
            fetch imp = \case
                "Prelude" -> return ("./Prelude.lc", undefined)
                "Main" -> return ("./Main.lc", src)
                n -> ioFetch paths' imp n

prettyShowUnlines :: Show a => a -> String
prettyShowUnlines = goPP 0 . PP.ppShow
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
