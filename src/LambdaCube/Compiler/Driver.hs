{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module LambdaCube.Compiler.Driver
    ( Backend(..)
    , Pipeline
    , Infos, listInfos
    , showRange
    , ErrorMsg(..)
    , Exp, toExp, tyOf, outputType, boolType, trueExp

    , MMT, runMMT, mapMMT
    , MM, runMM
    , Err
    , catchMM, catchErr
    , ioFetch
    , getDef, compileMain, preCompile
    ) where

import Data.List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
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
import Debug.Trace
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

import IR
import LambdaCube.Compiler.Pretty hiding ((</>))
import LambdaCube.Compiler.Infer (Infos, listInfos, ErrorMsg(..), showRange, PolyEnv(..), Export(..), ModuleR(..), ErrorT, throwErrorTCM, parseLC, joinPolyEnvs, filterPolyEnv, inference_, removeEscs, ImportItems (..))
import LambdaCube.Compiler.CoreToIR

type EName = String
type MName = String

type Modules = Map FilePath (Either Doc PolyEnv)
type ModuleFetcher m = MName -> m (FilePath, String)

newtype MMT m a = MMT { runMMT :: ReaderT (ModuleFetcher (MMT m)) (ErrorT (StateT Modules (WriterT Infos m))) a }
    deriving (Functor, Applicative, Monad, MonadReader (ModuleFetcher (MMT m)), MonadState Modules, MonadError ErrorMsg, MonadIO, MonadThrow, MonadCatch, MonadMask)
type MM = MMT IO

instance MonadMask m => MonadMask (ExceptT e m) where
    mask f = ExceptT $ mask $ \u -> runExceptT $ f (mapExceptT u)
    uninterruptibleMask = error "not implemented: uninterruptibleMask for ExcpetT"

mapMMT f (MMT m) = MMT $ f m

type Err a = (Either ErrorMsg a, Infos)

runMM :: Monad m => ModuleFetcher (MMT m) -> MMT m a -> m (Err a) 
runMM fetcher
    = runWriterT
    . flip evalStateT mempty
    . runExceptT
    . flip runReaderT fetcher
    . runMMT

catchErr :: (MonadCatch m, NFData a) => (String -> m a) -> m a -> m a
catchErr er m = (m >>= evaluate) `catch` getErr `catch` getPMatchFail
  where
    evaluate x = (return $!! x) >>= return
    getErr (e :: ErrorCall) = catchErr er $ er $ show e
    getPMatchFail (e :: PatternMatchFail) = catchErr er $ er $ show e

catchMM :: Monad m => MMT m a -> (ErrorMsg -> MMT m a) -> MMT m a
catchMM m e = mapMMT (mapReaderT $ lift . runExceptT) m >>= either e return

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
ioFetch paths n = f fnames
  where
    f [] = throwErrorTCM $ "can't find module" <+> hsep (map text fnames)
    f (x:xs) = liftIO (readFile' x) >>= \case
        Nothing -> f xs
        Just src -> return (x, src)
    fnames = map (normalise . lcModuleFile) $ nub paths
    lcModuleFile path = path </> (n ++ ".lc")

loadModule :: MonadMask m => MName -> MMT m (FilePath, PolyEnv)
loadModule mname = do
    fetch <- ask
    (fname, src) <- fetch mname
    c <- gets $ Map.lookup fname
    case c of
        Just (Right m) -> return (fname, m)
        Just (Left e) -> throwErrorTCM $ "cycles in module imports:" <+> pShow mname <+> e
        _ -> do
            e <- MMT $ lift $ mapExceptT (lift . lift) $ parseLC fname src
            modify $ Map.insert fname $ Left $ pShow $ map fst $ moduleImports e
            let
                loadModuleImports (m, is) = do
                    filterPolyEnv (filterImports is) . snd <$> loadModule m
            do
                ms <- mapM loadModuleImports $ moduleImports e
                x' <- trace ("loading " ++ fname) $ do
                    env <- joinPolyEnvs False ms
                    x <- MMT $ lift $ mapExceptT (lift . mapWriterT (return . runIdentity)) $ inference_ env e
                    case moduleExports e of
                            Nothing -> return x
                            Just es -> joinPolyEnvs False $ flip map es $ \exp -> case exp of
                                ExportId d -> case  Map.lookup d $ getPolyEnv x of
                                    Just def -> PolyEnv (Map.singleton d def) mempty
                                    Nothing  -> error $ d ++ " is not defined"
                                ExportModule m | m == takeFileName mname -> x
                                ExportModule m -> case [ ms
                                                       | ((m', is), ms) <- zip (moduleImports e) ms, m' == m] of
                                    [x] -> x
                                    []  -> error "empty export list"
                                    _   -> error "export list: internal error"
                modify $ Map.insert fname $ Right x'
                return (fname, x')
--              `finally` modify (Map.delete fname)
              `catchMM` (\e -> modify (Map.delete fname) >> throwError e)

filterImports (ImportAllBut ns) = not . (`elem` ns)
filterImports (ImportJust ns) = (`elem` ns)

-- used in runTests
getDef :: MonadMask m => MName -> EName -> Maybe Exp -> MMT m (FilePath, Either String Exp, Infos)
getDef m d ty = do
    (fname, pe) <- loadModule m
    return
      ( fname
      , case Map.lookup d $ getPolyEnv pe of
        Just (th, thy, si)
            | Just False <- (== toExp thy) <$> ty -> Left $ "type of " ++ d ++ " should be " ++ show ty ++ " instead of " ++ show (toExp thy)     -- TODO: better type comparison
            | otherwise -> Right $ toExp th
        Nothing -> Left $ d ++ " is not found"
      , infos pe
      )

parseAndToCoreMain m = either (throwErrorTCM . text) return . (\(_, e, i) -> flip (,) i <$> e) =<< getDef m "main" (Just outputType)

-- | most commonly used interface for end users
compileMain :: [FilePath] -> IR.Backend -> MName -> IO (Either String IR.Pipeline)
compileMain path backend fname
    = fmap ((show +++ fst) . fst) $ runMM (ioFetch path) $ (compilePipeline backend *** id) <$> parseAndToCoreMain fname

-- | Removes the escaping characters from the error message
removeEscapes = ((\(ErrorMsg e) -> ErrorMsg (removeEscs e)) +++ id) *** id

-- used by the compiler-service of the online editor
preCompile :: (MonadMask m, MonadIO m) => [FilePath] -> [FilePath] -> Backend -> String -> IO (String -> m (Err (IR.Pipeline, Infos)))
preCompile paths paths' backend mod = do
  res <- runMM (ioFetch paths) $ loadModule mod
  case res of
    (Left err, i) -> error $ "Prelude could not compiled: " ++ show err    
    (Right (_, prelude), _) -> return compile
      where
        compile src = fmap removeEscapes . runMM fetch $ do
            modify $ Map.insert ("." </> "Prelude.lc") $ Right prelude
            (compilePipeline backend *** id) <$> parseAndToCoreMain "Main"
          where
            fetch = \case
                "Prelude" -> return ("./Prelude.lc", undefined)
                "Main" -> return ("./Main.lc", src)
                n -> ioFetch paths' n

