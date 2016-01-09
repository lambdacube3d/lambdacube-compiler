{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module LambdaCube.Compiler.Driver
    ( module LambdaCube.Compiler.Driver
    , Backend(..)
    , Pipeline
    , Infos
    , showRange
    , ErrorMsg(..)
    , Exp, toExp, tyOf, outputType, boolType, trueExp
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

import IR
import LambdaCube.Compiler.Pretty hiding ((</>))
import LambdaCube.Compiler.Infer (Info, Infos, ErrorMsg(..), showRange, PolyEnv(..), Export(..), ModuleR(..), ErrorT, throwErrorTCM, parseLC, joinPolyEnvs, inference_)
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

catchMM_ :: Monad m => MMT m a -> MMT m (Either ErrorMsg a)
catchMM_ = mapMMT $ mapReaderT $ \m -> lift $ runExceptT m

catchMM :: Monad m => MMT m a -> MMT m (Either String a)
catchMM = mapMMT $ mapReaderT $ \m -> lift $ either (Left . show) Right <$> runExceptT m

catchMM' :: Monad m => MMT m a -> (ErrorMsg -> MMT m a) -> MMT m a
catchMM' m e = catchMM_ m >>= either e return

-- TODO: remove dependent modules from cache too
removeFromCache :: Monad m => FilePath -> MMT m ()
removeFromCache f = modify $ Map.delete f

readFile' :: FilePath -> IO (Maybe String)
readFile' fname = do
    b <- doesFileExist fname
    if b then Just <$> readFile fname else return Nothing

ioFetch :: [FilePath] -> ModuleFetcher MM
ioFetch paths n = f fnames
  where
    f [] = throwErrorTCM $ "can't find module" <+> hsep (map text fnames)
    f (x:xs) = liftIO (readFile' x) >>= \case
        Nothing -> f xs
        Just src -> return (x, src)
    fnames = map lcModuleFile paths
    lcModuleFile path = path </> (n ++ ".lc")

loadModule :: MonadMask m => MName -> MMT m PolyEnv
loadModule mname = do
    fetch <- ask
    (fname, src) <- fetch mname
    c <- gets $ Map.lookup fname
    case c of
        Just (Right m) -> return m
        Just (Left e) -> throwErrorTCM $ "cycles in module imports:" <+> pShow mname <+> e
        _ -> do
            e <- MMT $ lift $ mapExceptT (lift . lift) $ parseLC fname src
            modify $ Map.insert fname $ Left $ pShow $ moduleImports e
            do
                ms <- mapM loadModule $ moduleImports e
                x' <- trace ("loading " ++ fname) $ do
                    env <- joinPolyEnvs False ms
                    x <- MMT $ lift $ mapExceptT (lift . mapWriterT (return . runIdentity)) $ inference_ env e
                    case moduleExports e of
                            Nothing -> return x
                            Just es -> joinPolyEnvs False $ flip map es $ \exp -> case exp of
                                ExportModule m | m == mname -> x
                                ExportModule m -> case [ms | (m', ms) <- zip (moduleImports e) ms, m' == m] of
                                    [x] -> x
                modify $ Map.insert fname $ Right x'
                return x'
--              `finally` modify (Map.delete fname)
              `catchMM'` (\e -> modify (Map.delete fname) >> throwError e)
{- not used?
--getDef_ :: MName -> EName -> MM Exp
getDef_ m d = do
    pe <- loadModule m
    MMT $ return (getPolyEnv pe Map.! d)

getType = getType_ "Prelude"
getType_ m n = either (putStrLn . show) (putStrLn . ppShow . toExp . snd) . fst =<< runMM (ioFetch ["./tests/accept"]) (getDef_ (ExpN m) (ExpN n))

getDef'' m n = either (putStrLn . show) (either putStrLn (putStrLn . ppShow . fst)) . fst =<< runMM (ioFetch ["./tests/accept"]) (getDef (ExpN m) (ExpN n) Nothing)
-}
-- used in runTests
getDef :: MonadMask m => MName -> EName -> Maybe Exp -> MMT m (Either String Exp, Infos)
getDef m d ty = do
    pe <- loadModule m
    return
      ( case Map.lookup d $ getPolyEnv pe of
        Just (th, thy)
            | Just False <- (== toExp thy) <$> ty -> Left $ "type of " ++ d ++ " should be " ++ show ty ++ " instead of " ++ show (toExp thy)     -- TODO: better type comparison
            | otherwise -> Right $ toExp th
        Nothing -> Left $ d ++ " is not found"
      , infos pe
      )

parseAndToCoreMain m = either (throwErrorTCM . text) return . (\(e, i) -> flip (,) i <$> e) =<< getDef m "main" (Just outputType)

compileMain_ :: MonadMask m => PolyEnv -> ModuleFetcher (MMT m) -> IR.Backend -> FilePath -> MName -> m (Err (IR.Pipeline, Infos))
compileMain_ prelude fetch backend path fname = runMM fetch $ do
    modify $ Map.insert (path </> "Prelude.lc") $ Right prelude
    (compilePipeline True backend *** id) <$> parseAndToCoreMain fname

-- | most commonly used interface for end users
compileMain :: [FilePath] -> IR.Backend -> MName -> IO (Either String IR.Pipeline)
compileMain path backend fname = fmap ((show +++ fst) . fst) $ runMM (ioFetch path) $ (compilePipeline True backend *** id) <$> parseAndToCoreMain fname

compileMain' :: MonadMask m => PolyEnv -> IR.Backend -> String -> m (Err (IR.Pipeline, Infos))
compileMain' prelude backend src = compileMain_ prelude fetch backend "." "Main"
  where
    fetch = \case
        "Prelude" -> return ("./Prelude.lc", undefined)
        "Main" -> return ("./Main.lc", src)
        n -> throwErrorTCM $ "can't find module" <+> pShow n

-- used by the compiler-service of the online editor
preCompile :: MonadMask m => [FilePath] -> Backend -> String -> IO (String -> m (Err (IR.Pipeline, Infos)))
preCompile paths backend mod = do
  res <- runMM (ioFetch paths) $ loadModule mod
  case res of
    (Right prelude, _) -> return $ compileMain' prelude backend
    (Left err, i) -> error $ "Prelude could not compiled: " ++ show err    

