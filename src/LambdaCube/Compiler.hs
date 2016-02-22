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
    , ioFetch, decideFilePath
    , getDef, compileMain, preCompile
    , removeFromCache

    , compilePipeline
    , ppShow
    , prettyShowUnlines
    ) where

import Data.List
import Data.Maybe
import Data.Function
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Control.Monad.State.Strict
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
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Text.Show.Pretty as PP

import LambdaCube.IR as IR
import LambdaCube.Compiler.Pretty hiding ((</>))
import LambdaCube.Compiler.Parser (Module(..), Export(..), ImportItems (..), runDefParser, parseLC)
import LambdaCube.Compiler.Lexer (DesugarInfo)
import LambdaCube.Compiler.Lexer as Exported (Range(..))
import LambdaCube.Compiler.Infer (showError, inference, GlobalEnv, initEnv)
import LambdaCube.Compiler.Infer as Exported (Infos, listAllInfos, listTypeInfos, listTraceInfos, Exp, outputType, boolType, trueExp, unfixlabel)
import LambdaCube.Compiler.CoreToIR

-- inlcude path for: Builtins, Internals and Prelude
import Paths_lambdacube_compiler (getDataDir)

--------------------------------------------------------------------------------

readFileStrict :: FilePath -> IO String
readFileStrict = fmap T.unpack . TIO.readFile

readFile' :: FilePath -> IO (Maybe (IO String))
readFile' fname = do
    b <- doesFileExist fname
    return $ if b then Just $ readFileStrict fname else Nothing

instance MonadMask m => MonadMask (ExceptT e m) where
    mask f = ExceptT $ mask $ \u -> runExceptT $ f (mapExceptT u)
    uninterruptibleMask = error "not implemented: uninterruptibleMask for ExcpetT"

prettyShowUnlines :: Show a => a -> String
prettyShowUnlines = goPP 0 . PP.ppShow
  where
    goPP _ [] = []
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

--------------------------------------------------------------------------------

type MName = String
type SName = String
type SourceCode = String

-- file name or module name?
decideFilePath n
    | takeExtension n == ".lc" = Left n
    | otherwise = Right n

dropExtension' e f
    | takeExtension f == e = dropExtension f
    | otherwise = error $ "dropExtension: expcted extension: " ++ e ++ " ; filename: " ++ f

fileNameToModuleName n
    = intercalate "." $ remDot $ (\(a, b) -> map takeDirectory (splitPath a) ++ [b]) $ splitFileName $ dropExtension' ".lc" $ normalise n
  where
    remDot (".": xs) = xs
    remDot xs = xs

moduleNameToFileName n = hn n ++ ".lc"
  where
    hn = h []
    h acc [] = reverse acc
    h acc ('.':cs) = reverse acc </> hn cs
    h acc (c: cs) = h (c: acc) cs

type ModuleFetcher m = Maybe FilePath -> Either FilePath MName -> m (FilePath, MName, m SourceCode)

ioFetch :: MonadIO m => [FilePath] -> ModuleFetcher (MMT m x)
ioFetch paths' imp n = do
    preludePath <- (</> "lc") <$> liftIO getDataDir
    let paths = paths' ++ [preludePath]
        find ((x, mn): xs) = liftIO (readFile' x) >>= maybe (find xs) (\src -> return (x, mn, liftIO src))
        find [] = throwError $ show $ "can't find " <+> either (("lc file" <+>) . text) (("module" <+>) . text) n
                                  <+> "in path" <+> hsep (map text paths)
        lcModuleFile path = case n of
            Left n  -> (path </> n, fileNameToModuleName n)
            Right n -> (path </> moduleNameToFileName n, n)
    find $ nubBy ((==) `on` fst) $ map (first normalise . lcModuleFile) paths

--------------------------------------------------------------------------------

-- todo: use RWS
newtype MMT m x a = MMT { runMMT :: ExceptT String (ReaderT (ModuleFetcher (MMT m x)) (StateT (Modules x) (WriterT Infos m))) a }
    deriving (Functor, Applicative, Monad, MonadReader (ModuleFetcher (MMT m x)), MonadState (Modules x), MonadError String, MonadIO, MonadThrow, MonadCatch, MonadMask, MonadWriter Infos)
type MM = MMT IO Infos

mapMMT f (MMT m) = MMT $ f m

type Err a = (Either String a, Infos)

runMM :: Monad m => ModuleFetcher (MMT m x) -> MMT m x a -> m (Err a) 
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

catchMM :: Monad m => MMT m x a -> (String -> Infos -> MMT m x a) -> MMT m x a
catchMM m e = mapMMT (lift . mapReaderT (mapStateT $ lift . runWriterT >=> f) . runExceptT) m >>= either (uncurry e) return
  where
    f ((Right x, m), is) = tell is >> return (Right x, m)
    f ((Left e, m), is) = return (Left (e, is), m)

-- TODO: remove dependent modules from cache too?
removeFromCache :: Monad m => FilePath -> MMT m x ()
removeFromCache f = modify $ Map.delete f

type Module' x = (SourceCode, DesugarInfo, GlobalEnv, x)

type Modules x = Map FilePath (Either (SourceCode, Module) (Module' x))

loadModule :: MonadMask m => (Infos -> x) -> Maybe FilePath -> Either FilePath MName -> MMT m x (FilePath, Module' x)
loadModule ex imp mname_ = do
    (fname, mname, srcm) <- ask >>= \fetch -> fetch imp mname_
    c <- gets $ Map.lookup fname
    case c of
        Just (Right m) -> return (fname, m)
        Just (Left (_, e)) -> throwError $ show $ "cycles in module imports:" <+> pShow mname <+> pShow (fst <$> moduleImports e)
        _ -> do
            src <- srcm
            e <- either (throwError . show) return $ parseLC fname src
            modify $ Map.insert fname $ Left (src, e)
            let
                loadModuleImports (m, is) = do
                    (_, (_, ds, ge, _)) <- loadModule ex (Just fname) (Right $ snd m)
                    return (ds{-todo: filter-}, Map.filterWithKey (\k _ -> filterImports is k) ge)

                filterImports (ImportAllBut ns) = not . (`elem` map snd ns)
                filterImports (ImportJust ns) = (`elem` map snd ns)
            do
                ms <- mapM loadModuleImports $ moduleImports e
                let (ds, ge) = mconcat ms
                (defs, dsinfo) <- MMT $ mapExceptT (return . runIdentity) $ runDefParser ds $ definitions e
                srcs <- gets $ fmap $ either fst (\(src, _, _, _) -> src)
                let
                    -- todo: better story for info handling
                    ff (Left e, is) = Left (showError srcs e) <$ tell is
                    ff (Right ge, is) = return $ Right (mconcat ge, is)
                (newge, is) <- MMT $ mapExceptT (lift . lift . mapWriterT (return . runIdentity) . (ff <=< runWriterT . flip runReaderT (extensions e, initEnv <> ge))) $ inference defs
                (ds', ge') <- fmap mconcat $ forM (fromMaybe [ExportModule (mempty, mname)] $ moduleExports e) $ \exp -> case exp of
                    ExportId (snd -> d) -> case Map.lookup d newge of
                        Just def -> return (mempty{-TODO-}, Map.singleton d def)
                        Nothing  -> error $ d ++ " is not defined"
                    ExportModule (snd -> m) | m == mname -> return (dsinfo, newge)
                    ExportModule m -> case [ x | ((m', _), x) <- zip (moduleImports e) ms, m' == m] of
                        [x] -> return x
                        []  -> throwError $ "empty export list: " ++ show (fname, m, map fst $ moduleImports e, mname)
                        _   -> error "export list: internal error"
                let m = (src, ds', ge', ex is)
                modify $ Map.insert fname $ Right m
                return (fname, m)
              `catchMM` (\e is -> modify (Map.delete fname) >> tell is >> throwError e)

-- used in runTests
getDef :: MonadMask m => FilePath -> SName -> Maybe Exp -> MMT m Infos (FilePath, Either String (Exp, Exp), Infos)
getDef m d ty = do
    (fname, (_, _, ge, infos)) <- loadModule id Nothing $ Left m
    return
      ( fname
      , case Map.lookup d ge of
        Just (e, thy, si)
            | Just False <- (== thy) <$> ty -> Left $ "type of " ++ d ++ " should be " ++ show ty ++ " instead of " ++ ppShow thy     -- TODO: better type comparison
            | otherwise -> Right (e, thy)
        Nothing -> Left $ d ++ " is not found"
      , infos
      )

parseAndToCoreMain m = either throwError return . (\(_, e, i) -> flip (,) i <$> e) =<< getDef m "main" (Just outputType)

-- | most commonly used interface for end users
compileMain :: [FilePath] -> IR.Backend -> MName -> IO (Either String IR.Pipeline)
compileMain path backend fname
    = fmap (right fst . fst) $ runMM (ioFetch path) $ first (compilePipeline backend) <$> parseAndToCoreMain fname

-- used by the compiler-service of the online editor
preCompile :: (MonadMask m, MonadIO m) => [FilePath] -> [FilePath] -> Backend -> FilePath -> IO (String -> m (Err (IR.Pipeline, Infos)))
preCompile paths paths' backend mod = do
  res <- runMM (ioFetch paths) $ loadModule id Nothing $ Left mod
  case res of
    (Left err, i) -> error $ "Prelude could not compiled: " ++ err
    (Right (_, prelude), _) -> return compile
      where
        compile src = fmap (first (left removeEscs)) . runMM fetch $ do
            modify $ Map.insert ("." </> "Prelude.lc") $ Right prelude
            first (compilePipeline backend) <$> parseAndToCoreMain "Main"
          where
            fetch imp = \case
                Left "Prelude" -> return ("./Prelude.lc", "Prelude", undefined)
                Left "Main"    -> return ("./Main.lc", "Main", return src)
                n -> ioFetch paths' imp n

