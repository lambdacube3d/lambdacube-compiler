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
import Control.Monad.Writer
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

type Modules = Map FilePath (Maybe PolyEnv)
type ModuleFetcher m = MName -> m (FilePath, String)

newtype MMT m a = MMT { runMMT :: ReaderT (ModuleFetcher (MMT m)) (ErrorT (StateT Modules (WriterT Infos (VarMT m)))) a }
    deriving (Functor, Applicative, Monad, MonadReader (ModuleFetcher (MMT m)), MonadState Modules, MonadError ErrorMsg, MonadIO)
type MM = MMT IO

mapMMT f (MMT m) = MMT $ f m

type Err a = (Either ErrorMsg a, Infos)

freshTypeVars :: FreshVars
freshTypeVars = map ('t':) $ map show [0..]

runMM :: Monad m => FreshVars -> ModuleFetcher (MMT m) -> MMT m a -> m (Err a) 
runMM vs fetcher
    = flip evalStateT vs
    . runWriterT
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
        Just (Just m) -> return m
        Just _ -> throwErrorTCM $ "cycles in module imports:" <+> pShow mname
        _ -> do
            modify $ Map.insert fname Nothing
            e <- MMT $ lift $ mapExceptT (lift . lift) $ parseLC fname src
            ms <- mapM loadModule $ moduleImports e
            mapError (InFile src) $ trace ("loading " ++ fname) $ do
                env <- joinPolyEnvs ms
                x <- MMT $ lift $ mapExceptT (lift . mapWriterT (mapStateT liftIdentity)) $ inference_ env e
                modify $ Map.insert fname $ Just x
                return x

--getDef_ :: MName -> EName -> MM Exp
getDef_ m d = do
    pe <- loadModule m
    MMT $ return (getPolyEnv pe Map.! d)

getType = getType_ "Prelude"
getType_ m n = either (putStrLn . show) (putStrLn . ppShow) . fst =<< runMM freshTypeVars (ioFetch ["./tests/accept"]) (getDef_ (ExpN m) (ExpN n))

getDef'' m n = either (putStrLn . show) (either putStrLn (putStrLn . ppShow . fst)) . fst =<< runMM freshTypeVars (ioFetch ["./tests/accept"]) (getDef (ExpN m) (ExpN n) Nothing)

getDef :: Monad m => MName -> EName -> Maybe Exp -> MMT m (Either String (Exp, Infos))
getDef m d ty = do
    pe <- loadModule m
    case Map.lookup d $ getTEnv $ thunkEnv pe of
        Just (ISubst th) -> case (ty, tyOf th) of
            (Just ty, ty') | ty' /= ty -> return $ Left "type of main should be 'Output'"       -- TODO: better type comparison
            _ -> return $ Right (reduce th, infos pe)
        Nothing -> return $ Left "not found"
        _ -> throwErrorTCM "not found?"

outputType :: Exp
outputType = TCon Star "Output"

parseAndToCoreMain m = either (throwErrorTCM . text) return =<< getDef m (ExpN "main") (Just outputType)

compileMain_ :: Monad m => FreshVars -> PolyEnv -> ModuleFetcher (MMT m) -> IR.Backend -> FilePath -> MName -> m (Err (IR.Pipeline, Infos))
compileMain_ vs prelude fetch backend path fname = runMM vs fetch $ do
    modify $ Map.insert (path </> "Prelude.lc") $ Just prelude
    (IR.compilePipeline backend *** id) <$> parseAndToCoreMain fname

compileMain :: Monad m => ModuleFetcher (MMT m) -> IR.Backend -> FilePath{-TODO:remove-} -> MName -> m (Err (IR.Pipeline, Infos))
compileMain fetch backend _ fname = runMM freshTypeVars fetch $ (IR.compilePipeline backend *** id) <$> parseAndToCoreMain fname

compileMain' :: Monad m => FreshVars -> PolyEnv -> IR.Backend -> String -> m (Err (IR.Pipeline, Infos))
compileMain' vs prelude backend src = compileMain_ vs prelude fetch backend "." (ExpN "Main")
  where
    fetch = \case
        ExpN "Prelude" -> return ("./Prelude.lc", undefined)
        ExpN "Main" -> return ("./Main.lc", src)
        n -> throwErrorTCM $ "can't find module" <+> pShow n



