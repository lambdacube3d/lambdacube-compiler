{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Driver
    ( module Driver
    , pattern ExpN
    , IR.Backend(..)
    , showErr
    , dummyPos
    , freshTypeVars
    ) where

import Data.List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Foldable (Foldable, toList)
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

import Pretty hiding ((</>))
import Type
import qualified IR as IR
import qualified CoreToIR as IR
import Parser
import Typecheck hiding (Exp(..))

type Modules = Map FilePath (Either Doc PolyEnv)
type ModuleFetcher m = MName -> m (FilePath, String)

newtype MMT m a = MMT { runMMT :: ReaderT (ModuleFetcher (MMT m)) (ErrorT (StateT Modules (WriterT Infos (VarMT m)))) a }
    deriving (Functor, Applicative, Monad, MonadReader (ModuleFetcher (MMT m)), MonadState Modules, MonadError ErrorMsg, MonadIO, MonadThrow, MonadCatch, MonadMask)
type MM = MMT IO

instance MonadMask m => MonadMask (ExceptT e m) where
    mask f = ExceptT $ mask $ \u -> runExceptT $ f (mapExceptT u)
    uninterruptibleMask = error "not implemented: uninterruptibleMask for ExcpetT"

mapMMT f (MMT m) = MMT $ f m

type Err a = (Either ErrorMsg a, Infos)

runMM :: Monad m => FreshVars -> ModuleFetcher (MMT m) -> MMT m a -> m (Err a) 
runMM vs fetcher
    = flip evalStateT vs
    . runWriterT
    . flip evalStateT mempty
    . runExceptT
    . flip runReaderT fetcher
    . runMMT

catchErr :: (MonadCatch m, NFData a) => (String -> m a) -> m a -> m a
catchErr er m = (m >>= evaluate) `catch` getErr `catch` getPMatchFail
  where
    evaluate x = (return $!! x) >>= return
    catchErr m = m
    getErr (e :: ErrorCall) = catchErr $ er $ show e
    getPMatchFail (e :: PatternMatchFail) = catchErr $ er $ show e

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
    lcModuleFile path = path </> (showN n ++ ".lc")

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
                x' <- mapError (InFile src) $ trace ("loading " ++ fname) $ do
                    env <- joinPolyEnvs ms
                    x <- MMT $ lift $ mapExceptT (lift . mapWriterT (mapStateT $ return . runIdentity)) $ inference_ env e
                    case moduleExports e of
                            Nothing -> return x
                            Just es -> joinPolyEnvs $ flip map es $ \exp -> case exp of
                                ExportModule m | m == mname -> x
                                ExportModule m -> case [ms | (m', ms) <- zip (moduleImports e) ms, m' == m] of
                                    [x] -> x
                modify $ Map.insert fname $ Right x'
                return x'
--              `finally` modify (Map.delete fname)
              `catchMM'` (\e -> modify (Map.delete fname) >> throwError e)

--getDef_ :: MName -> EName -> MM Exp
getDef_ m d = do
    pe <- loadModule m
    MMT $ return (getPolyEnv pe Map.! d)

getType = getType_ "Prelude"
getType_ m n = either (putStrLn . show) (putStrLn . ppShow . eitherItem tyOf id) . fst =<< runMM freshTypeVars (ioFetch ["./tests/accept"]) (getDef_ (ExpN m) (ExpN n))

getDef'' m n = either (putStrLn . show) (either putStrLn (putStrLn . ppShow . fst)) . fst =<< runMM freshTypeVars (ioFetch ["./tests/accept"]) (getDef (ExpN m) (ExpN n) Nothing)

getDef :: MonadMask m => MName -> EName -> Maybe Exp -> MMT m (Either String (Exp, Infos))
getDef m d ty = do
    pe <- loadModule m
    case Map.lookup d $ getPolyEnv pe of
        Just (ISubst th) -> case (ty, tyOf th) of
            (Just ty, ty') | ty' /= ty -> return $ Left "type of main should be 'Output'"       -- TODO: better type comparison
            _ -> return $ Right (reduce th, infos pe)
        Nothing -> return $ Left "not found"
        _ -> throwErrorTCM "not found?"

outputType :: Exp
outputType = TCon Star "Output"

parseAndToCoreMain m = either (throwErrorTCM . text) return =<< getDef m (ExpN "main") (Just outputType)

compileMain_ :: MonadMask m => FreshVars -> PolyEnv -> ModuleFetcher (MMT m) -> IR.Backend -> FilePath -> MName -> m (Err (IR.Pipeline, Infos))
compileMain_ vs prelude fetch backend path fname = runMM vs fetch $ do
    modify $ Map.insert (path </> "Prelude.lc") $ Right prelude
    (IR.compilePipeline backend *** id) <$> parseAndToCoreMain fname

compileMain :: MonadMask m => ModuleFetcher (MMT m) -> IR.Backend -> FilePath{-TODO:remove-} -> MName -> m (Err (IR.Pipeline, Infos))
compileMain fetch backend _ fname = runMM freshTypeVars fetch $ (IR.compilePipeline backend *** id) <$> parseAndToCoreMain fname

compileMain' :: MonadMask m => FreshVars -> PolyEnv -> IR.Backend -> String -> m (Err (IR.Pipeline, Infos))
compileMain' vs prelude backend src = compileMain_ vs prelude fetch backend "." (ExpN "Main")
  where
    fetch = \case
        ExpN "Prelude" -> return ("./Prelude.lc", undefined)
        ExpN "Main" -> return ("./Main.lc", src)
        n -> throwErrorTCM $ "can't find module" <+> pShow n



