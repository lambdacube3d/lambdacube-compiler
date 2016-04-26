{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}  -- instance MonadMask m => MonadMask (ExceptT e m)
module LambdaCube.Compiler
    ( Backend(..)
    , Pipeline
    , module Exported

    , MMT, runMMT, mapMMT
    , MM, runMM
    , catchErr
    , ioFetch, decideFilePath
    , getDef, compileMain, parseModule, preCompile
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
import qualified Data.IntMap.Strict as IM
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Except
import Control.DeepSeq
import Control.Monad.Catch
import Control.Exception hiding (catch, bracket, finally, mask)
import Control.Arrow hiding ((<+>))
import System.Directory
import System.FilePath
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Text.Show.Pretty as PP
--import Debug.Trace

import LambdaCube.IR as IR
import LambdaCube.Compiler.Pretty hiding ((</>))
import LambdaCube.Compiler.Parser (Module(..), Export(..), ImportItems (..), runDefParser, FileInfo(..), parseLC, Stmt, DesugarInfo)
import LambdaCube.Compiler.Lexer as Exported (Range(..), SPos(..), SIName(..), pattern SIName, sName)
import LambdaCube.Compiler.Infer (inference, GlobalEnv, initEnv)
import LambdaCube.Compiler.Infer as Exported (Infos, Info(..), listAllInfos, listTypeInfos, listTraceInfos, errorRange, Exp, outputType, boolType, trueExp, unfixlabel)
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

type ModuleFetcher m = Maybe FilePath -> Either FilePath MName -> m (Either String (FilePath, MName, m SourceCode))

ioFetch :: MonadIO m => [FilePath] -> ModuleFetcher (MMT m x)
ioFetch paths' imp n = do
    preludePath <- (</> "lc") <$> liftIO getDataDir
    let paths = paths' ++ [preludePath]
        find ((x, mn): xs) = liftIO (readFile' x) >>= maybe (find xs) (\src -> return $ Right (x, mn, liftIO src))
        find [] = return $ Left $ show $ "can't find " <+> either (("lc file" <+>) . text) (("module" <+>) . text) n
                                  <+> "in path" <+> hsep (map text (paths' ++ ["<<installed-prelude-path>>"]{-todo-}))
    find $ nubBy ((==) `on` fst) $ map (first normalise . lcModuleFile) paths
  where
    lcModuleFile path = case n of
        Left n  -> (path </> n, fileNameToModuleName n)
        Right n -> (path </> moduleNameToFileName n, n)

--------------------------------------------------------------------------------

newtype MMT m x a = MMT { runMMT :: ReaderT (ModuleFetcher (MMT m x)) (StateT (Modules x) m) a }
    deriving (Functor, Applicative, Monad, MonadReader (ModuleFetcher (MMT m x)), MonadState (Modules x), MonadIO, MonadThrow, MonadCatch, MonadMask)

type MM = MMT IO Infos

mapMMT f (MMT m) = MMT $ f m

runMM :: Monad m => ModuleFetcher (MMT m x) -> MMT m x a -> m a
runMM fetcher
    = flip evalStateT (Modules mempty mempty 1)
    . flip runReaderT fetcher
    . runMMT

catchErr :: (MonadCatch m, NFData a, MonadIO m) => (String -> m a) -> m a -> m a
catchErr er m = (force <$> m >>= liftIO . evaluate) `catch` getErr `catch` getPMatchFail
  where
    getErr (e :: ErrorCall) = catchErr er $ er $ show e
    getPMatchFail (e :: PatternMatchFail) = catchErr er $ er $ show e

-- TODO: remove dependent modules from cache too?
removeFromCache :: Monad m => FilePath -> MMT m x ()
removeFromCache f = modify $ \m@(Modules nm im ni) -> case Map.lookup f nm of
    Nothing -> m
    Just i -> Modules (Map.delete f nm) (IM.delete i im) ni

type Module' x = (SourceCode, Either String{-error msg-} (Module, x, Either String{-error msg-} (DesugarInfo, GlobalEnv)))

data Modules x = Modules
    { moduleIds :: !(Map FilePath Int)
    , modules   :: !(IM.IntMap (FilePath, Module' x))
    , nextMId   :: !Int
    }

(<&>) = flip (<$>)

loadModule :: MonadMask m => ((Infos, [Stmt]) -> x) -> Maybe FilePath -> Either FilePath MName -> MMT m x (Either String (FilePath, Module' x))
loadModule ex imp mname_ = do
  r <- ask >>= \fetch -> fetch imp mname_
  case r of
   Left err -> return $ Left err
   Right (fname, mname, srcm) -> do
    c <- gets $ Map.lookup fname . moduleIds
    case c of
      Just fid -> gets $ Right . (IM.! fid) . modules
      _ -> do
        src <- srcm
        fid <- gets nextMId
        modify $ \(Modules nm im ni) -> Modules (Map.insert fname fid nm) im $ ni+1
        res <- case parseLC $ FileInfo fid fname src of
          Left e -> return $ Left $ show e
          Right e -> do
            modify $ \(Modules nm im ni) -> Modules nm (IM.insert fid (fname, (src, Right (e, ex mempty, Left $ show $ "cycles in module imports:" <+> pShow mname <+> pShow (fst <$> moduleImports e)))) im) ni
            ms <- forM (moduleImports e) $ \(m, is) -> loadModule ex (Just fname) (Right $ sName m) <&> \r -> case r of
                      Left err -> Left $ sName m ++ " couldn't be found"
                      Right (fb, (src, dsge)) ->
                         either (Left . const (sName m ++ " couldn't be parsed"))
                                (\(pm, x, e) -> either
                                    (Left . const (sName m ++ " couldn't be typechecked"))
                                    (\(ds, ge) -> Right (ds{-todo: filter-}, Map.filterWithKey (\k _ -> filterImports is k) ge))
                                    e)
                                dsge

            let (res, err) = case sequence ms of
                  Left err -> (ex mempty, Left err)
                  Right ms@(mconcat -> (ds, ge)) -> case runExcept $ runDefParser ds $ definitions e of
                    Left err -> (ex mempty, Left $ show err)
                    Right (defs, warnings, dsinfo) -> (,) (ex (map ParseWarning warnings ++ is, defs)) $ case res of
                      Left err -> Left (show err)
                      Right (mconcat -> newge) ->
                        right mconcat $ forM (fromMaybe [ExportModule $ SIName mempty mname] $ moduleExports e) $ \case
                            ExportId (sName -> d) -> case Map.lookup d newge of
                                Just def -> Right (mempty{-TODO-}, Map.singleton d def)
                                Nothing  -> Left $ d ++ " is not defined"
                            ExportModule (sName -> m) | m == mname -> Right (dsinfo, newge)
                            ExportModule m -> case [ x | ((m', _), x) <- zip (moduleImports e) ms, m' == m] of
                                [x] -> Right x
                                []  -> Left $ "empty export list: " ++ show (fname, m, map fst $ moduleImports e, mname)
                                _   -> error "export list: internal error"
                     where
                        (res, is) = runWriter . flip runReaderT (extensions e, initEnv <> ge) . runExceptT $ inference defs

            return $ Right (e, res, err)
        modify $ \(Modules nm im ni) -> Modules nm (IM.insert fid (fname, (src, res)) im) ni
        return $ Right (fname, (src, res))
  where
    filterImports (ImportAllBut ns) = not . (`elem` map sName ns)
    filterImports (ImportJust ns) = (`elem` map sName ns)

-- used in runTests
getDef :: MonadMask m => FilePath -> SName -> Maybe Exp -> MMT m Infos (Infos, Either String (FilePath, Either String (Exp, Exp)))
getDef = getDef_ fst

getDef_ ex m d ty = loadModule ex Nothing (Left m) <&> \case
    Left err -> (mempty, Left err)
    Right (fname, (src, Left err)) -> (mempty, Left err)
    Right (fname, (src, Right (pm, infos, Left err))) -> (,) infos $ Left err
    Right (fname, (src, Right (pm, infos, Right (_, ge)))) -> (,) infos $ Right
        ( fname
        , case Map.lookup d ge of
          Just (e, thy, si)
            | Just False <- (== thy) <$> ty          -- TODO: better type comparison
                -> Left $ "type of " ++ d ++ " should be " ++ show ty ++ " instead of " ++ ppShow thy
            | otherwise -> Right (e, thy)
          Nothing -> Left $ d ++ " is not found"
        )

compilePipeline' ex backend m
    = second (either Left (fmap (compilePipeline backend) . snd)) <$> getDef_ ex m "main" (Just outputType)

-- | most commonly used interface for end users
compileMain :: [FilePath] -> IR.Backend -> MName -> IO (Either String IR.Pipeline)
compileMain path backend fname
    = fmap snd $ runMM (ioFetch path) $ compilePipeline' (const ()) backend fname

parseModule :: [FilePath] -> MName -> IO (Either String String)
parseModule path fname = runMM (ioFetch path) $ loadModule snd Nothing (Left fname) <&> \case
    Left err -> Left err
    Right (fname, (src, Left err)) -> Left err
    Right (fname, (src, Right (pm, infos, _))) -> Right $ pPrintStmts infos

-- used by the compiler-service of the online editor
preCompile :: (MonadMask m, MonadIO m) => [FilePath] -> [FilePath] -> Backend -> FilePath -> IO (String -> m (Either String IR.Pipeline, (Infos, String)))
preCompile paths paths' backend mod = do
  res <- runMM (ioFetch paths) $ loadModule ex Nothing $ Left mod
  case res of
    Left err -> error $ "Prelude could not compiled: " ++ err
    Right (src, prelude) -> return compile
      where
        compile src = fmap (first (left removeEscs)) . runMM fetch $ do
            let pname = "." </> "Prelude.lc"
            modify $ \(Modules nm im ni) -> Modules (Map.insert pname ni nm) (IM.insert ni (pname, prelude) im) (ni+1)
            (snd &&& fst) <$> compilePipeline' ex backend "Main"
          where
            fetch imp = \case
                Left "Prelude" -> return $ Right ("./Prelude.lc", "Prelude", undefined)
                Left "Main"    -> return $ Right ("./Main.lc", "Main", return src)
                n -> ioFetch paths' imp n
  where
    ex = second pPrintStmts

pPrintStmts = unlines . map ((++"\n") . removeEscs . ppShow)

