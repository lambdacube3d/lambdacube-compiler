{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
module Driver
    ( module Driver
    , pattern ExpN
    , IR.Backend(..)
    , showErr
    , dummyPos
    ) where

import Data.List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Foldable (Foldable, toList)
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Identity
import Control.Arrow hiding ((<+>))
import System.Directory
import System.FilePath
import Debug.Trace

import Pretty hiding ((</>))
import Type
import qualified IR as IR
import qualified CoreToIR as IR
import Parser
import Typecheck hiding (Exp(..))

type Modules = Map FilePath PolyEnv
type ModuleFetcher m = MName -> m (FilePath, String)

newtype MMT m a = MMT { runMMT :: ReaderT (ModuleFetcher (MMT m)) (ErrorT (StateT Modules (VarMT m))) a }
    deriving (Functor, Applicative, Monad, MonadReader (ModuleFetcher (MMT m)), MonadState Modules, MonadError ErrorMsg, MonadIO)
type MM = MMT IO

mapMMT f (MMT m) = MMT $ f m

type Err = Either ErrorMsg

runMM :: Monad m => ModuleFetcher (MMT m) -> MMT m a -> m (Err a) 
runMM fetcher
    = flip evalStateT 0
    . flip evalStateT mempty
    . runExceptT
    . flip runReaderT fetcher
    . runMMT

catchMM :: Monad m => MMT m a -> MMT m (Either String a)
catchMM = mapMMT $ mapReaderT $ \m -> lift $ either (Left . show) Right <$> runExceptT m

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
    lcModuleFile path = path </> (showN n ++ ".lc")

loadModule :: Monad m => MName -> MMT m PolyEnv
loadModule mname = do
    fetch <- ask
    (fname, src) <- fetch mname
    c <- gets $ Map.lookup fname
    case c of
        Just m -> return m
        _ -> do
            e <- MMT $ lift $ mapExceptT (lift . lift) $ parseLC fname src
            ms <- mapM loadModule $ moduleImports e
            mapError (InFile src) $ trace ("loading " ++ fname) $ do
                env <- joinPolyEnvs ms
                x <- MMT $ lift $ mapExceptT (lift . mapStateT liftIdentity) $ inference_ env e
                modify $ Map.insert fname x
                return x

getDef_ :: MName -> EName -> MM Exp
getDef_ m d = do
    pe <- loadModule m
    MMT $ fmap (\(m, (_, x)) -> typingToTy m x) $ lift $ lift $ lift $ mapStateT liftIdentity $ runWriterT' $ either undefined id (getPolyEnv pe Map.! d) $ ""

getType = getType_ "Prelude"
getType_ m n = either (putStrLn . show) (putStrLn . ppShow) =<< runMM (ioFetch ["./tests/accept"]) (getDef_ (ExpN m) (ExpN n))

getDef :: Monad m => MName -> EName -> MMT m (Either String (Exp, Infos))
getDef m d = do
    pe <- loadModule m
    case Map.lookup d $ getTEnv $ thunkEnv pe of
        Just (ISubst th) -> return $ Right (reduce th, infos pe)
        Nothing -> return $ Left "not found"
        _ -> throwErrorTCM "not found?"

parseAndToCoreMain m = either (throwErrorTCM . text) return =<< getDef m (ExpN "main")

compileMain_ :: Monad m => PolyEnv -> ModuleFetcher (MMT m) -> IR.Backend -> FilePath -> MName -> m (Err (IR.Pipeline, Infos))
compileMain_ prelude fetch backend path fname = runMM fetch $ do
    modify $ Map.insert (path </> "Prelude.lc") prelude
    (IR.compilePipeline backend *** id) <$> parseAndToCoreMain fname

compileMain :: Monad m => ModuleFetcher (MMT m) -> IR.Backend -> FilePath -> MName -> m (Err (IR.Pipeline, Infos))
compileMain fetch backend path fname = runMM fetch $ (IR.compilePipeline backend *** id) <$> parseAndToCoreMain fname

compileMain' :: Monad m => PolyEnv -> IR.Backend -> String -> m (Err (IR.Pipeline, Infos))
compileMain' prelude backend src = compileMain_ prelude fetch backend "." (ExpN "Main")
  where
    fetch = \case
        ExpN "Prelude" -> return ("./Prelude.lc", undefined)
        ExpN "Main" -> return ("./Main.lc", src)
        n -> throwErrorTCM $ "can't find module" <+> pShow n



