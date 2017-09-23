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
    , ioFetch, decideFilePath
    , loadModule, getDef, compileMain, parseModule, preCompile
    , removeFromCache

    , compilePipeline
    , ppShow
    , plainShow
    , prettyShowUnlines
    ) where
import qualified Data.ByteString.Char8 as BS

import Data.Binary
import Data.Time.Clock
import Text.Printf
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
import Control.Monad.Catch
import Control.Arrow hiding ((<+>))
import System.FilePath
import System.Directory
import System.IO.Unsafe
--import Debug.Trace

import LambdaCube.IR as IR
import LambdaCube.Compiler.Pretty hiding ((</>))
import LambdaCube.Compiler.DesugaredSource (Module_(..), Export(..), ImportItems (..), Stmt)
import LambdaCube.Compiler.Parser (runDefParser, parseLC, DesugarInfo, Module)
import LambdaCube.Compiler.InferMonad (GlobalEnv, initEnv, closeGlobalEnv)
import LambdaCube.Compiler.Infer (inference)
import LambdaCube.Compiler.CoreToIR

import LambdaCube.Compiler.Utils
import LambdaCube.Compiler.DesugaredSource as Exported (FileInfo(..), Range(..), SPos(..), pattern SPos, SIName(..), pattern SIName, sName, SI(..))
import LambdaCube.Compiler.Core as Exported (mkDoc, Exp, ExpType(..), pattern ET, outputType, boolType, trueExp, hnf, closeExp)
import LambdaCube.Compiler.InferMonad as Exported (errorRange, listAllInfos, listAllInfos', listTypeInfos, listErrors, listWarnings, listTraceInfos, Infos, Info(..))
--import LambdaCube.Compiler.Infer as Exported ()

-- inlcude path for: Builtins, Internals and Prelude
import Paths_lambdacube_compiler (getDataDir)

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

type ModuleFetcher m = Maybe FilePath -> Either FilePath MName -> m (Either Doc (FilePath, MName, m SourceCode))

ioFetch :: MonadIO m => [FilePath] -> ModuleFetcher (MMT m x)
ioFetch paths' imp n = do
    preludePath <- (</> "lc") <$> liftIO getDataDir
    let paths = map (id &&& id) paths' ++ [(preludePath, {-"<<installed-prelude-path>>"-}preludePath)]
        find ((x, (x', mn)): xs) = liftIO (readFileIfExists x) >>= maybe (find xs) (\src -> return $ Right (x', mn, liftIO src))
        find [] = return $ Left $ "can't find" <+> either (("lc file" <+>) . text) (("module" <+>) . text) n
                                  <+> "in path" <+> hsep (text . snd <$> paths)
    find $ nubBy ((==) `on` fst) $ map (first normalise . lcModuleFile) paths
  where
    lcModuleFile (path, path') = case n of
        Left n  -> (path </> n, (path' </> n, fileNameToModuleName n))
        Right n -> (path </> moduleNameToFileName n, (path' </> moduleNameToFileName n, n))

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

-- TODO: remove dependent modules from cache too?
removeFromCache :: Monad m => FilePath -> MMT m x ()
removeFromCache f = modify $ \m@(Modules nm im ni) -> case Map.lookup f nm of
    Nothing -> m
    Just i -> Modules (Map.delete f nm) (IM.delete i im) ni

type Module' x = (SourceCode, Either Doc{-error msg-} (Module, x, Either Doc{-error msg-} (DesugarInfo, GlobalEnv)))

data Modules x = Modules
    { moduleIds :: !(Map FilePath Int)
    , modules   :: !(IM.IntMap (FileInfo, Module' x))
    , nextMId   :: !Int
    }

loadModule :: MonadMask m => ((Infos, [Stmt]) -> x) -> Maybe FilePath -> Either FilePath MName -> MMT m x (Either Doc (FileInfo, Module' x))
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
        let fi = FileInfo fid fname mname
        res <- case parseLC fi of
          Left e -> return $ Left $ text $ show e
          Right e -> do
            modify $ \(Modules nm im ni) -> Modules nm (IM.insert fid (fi, (src, Right (e, ex mempty, Left $ "cycles in module imports:" <+> pShow mname <+> pShow (fst <$> moduleImports e)))) im) ni
            ms <- forM (moduleImports e) $ \(m, is) -> loadModule ex (Just fname) (Right $ sName m) <&> \r -> case r of
                      Left err -> Left $ pShow m <+> "is not found"
                      Right (fb, (src, dsge)) ->
                         either (Left . const (pShow m <+> "couldn't be parsed"))
                                (\(pm, x, e) -> either
                                    (Left . const (pShow m <+> "couldn't be typechecked"))
                                    (\(ds, ge) -> Right (ds{-todo: filter-}, Map.filterWithKey (\k _ -> filterImports is k) ge))
                                    e)
                                dsge
            ---------------
            let (res, err, g_env, defs) = case sequence ms of
                  Left err -> (ex mempty, Left $ pShow err, mempty, mempty)
                  Right ms@(mconcat -> (ds, ge)) -> case runExcept $ runDefParser ds $ definitions e of
                    Left err -> (ex mempty, Left $ pShow err, mempty, mempty)
                    Right (defs, warnings, dsinfo) -> ((ex (map ParseWarning warnings ++ is, defs)), res_1, g_env_1, defs) -- defs g_env_1
                     where
                        defs_cached = unsafePerformIO $ do
                          let filename = printf "%s.def_bin" $ takeFileName fname :: String
                          doesFileExist filename >>= \case
                            True  -> do
                              BS.putStrLn $ BS.pack $ printf "load %s" filename
                              decodeFile filename
                            False -> do
                              BS.putStrLn $ BS.pack $ printf "save %s" filename
                              encodeFile filename defs
                              pure defs
                        (res, is) = runWriter . flip runReaderT (extensions e, initEnv <> ge) . runExceptT $ inference defs --_cached

                        (g_env_1, res_1) = case res of
                              Left err -> (mempty, Left $ pShow err)
                              Right (mconcat -> newge) -> --do
                                --writeFile (printf "%s.exp" fname) $ show newge
                                (newge, right mconcat $ forM (fromMaybe [ExportModule $ SIName mempty mname] $ moduleExports e) $ \case
                                    ExportId (sName -> d) -> case Map.lookup d newge of
                                        Just def -> Right (mempty{-TODO-}, Map.singleton d def)
                                        Nothing  -> Left $ text d <+> "is not defined"
                                    ExportModule (sName -> m) | m == mname -> Right (dsinfo, newge)
                                    ExportModule m -> case [ x | ((m', _), x) <- zip (moduleImports e) ms, m' == m] of
                                        [x] -> Right x
                                        []  -> Left $ "empty export list in module" <+> text fname -- m, map fst $ moduleImports e, mname)
                                        _   -> error "export list: internal error")
            ---------------
            let writeResult = do
                  let filename = printf "%s.exp" $ takeFileName fname :: String
                      filename_closed = printf "%s.exp.closed" $ takeFileName fname :: String
                      filename_closed_tr = printf "%s.exp.closed.tr" $ takeFileName fname :: String
                      filename_keys = printf "%s.exp.keys" $ takeFileName fname :: String
                  --putStrLn $ printf "write result! %d %s" ({-Map.size-}length g_env) filename
                  writeFile filename_keys $ unlines $ map show $ Map.keys g_env
                  let (g_env_ok, g_env_closed, g_env_closed_tr) = unzip3
                        [ ( printf "%s :: %s\n%s = %s\n\n" k ty_s k v_s :: String
                          , printf "%s :: %s\n%s = %s\n\n" k c_ty_s k c_v_s :: String
                          , printf "%s :: %s\n%s = %s\n\n" k tr_c_ty_s k tr_c_v_s :: String
                          )
                        | (k,(v, v_ty, v_si)) <- Map.toList g_env
                        , let ty_s = show $ mkDoc (False,False) $ v_ty
                        , let v_s = show $ mkDoc (False,True) $ v
                        , let c_v_ty = closeExp v_ty
                        , let c_v = closeExp v
                        , let c_ty_s = show $ mkDoc (False,False) c_v_ty
                        , let c_v_s = show $ mkDoc (False,True) $ c_v
                        , let tr_c_ty_s = show $ mkDoc (False,False) $ tr_exp c_v_ty
                        , let tr_c_v_s = show $ mkDoc (False,True) $ tr_exp c_v
                        ]
                      tr_exp :: Exp -> Exp
                      tr_exp = decode . encode
                  {-
                  writeFile filename (concat $ g_env_ok :: String)
                  writeFile filename_closed (concat $ g_env_closed :: String)
                  writeFile filename_closed_tr (concat $ g_env_closed_tr :: String)
                  -}
                  BS.putStrLn $ BS.pack $ printf "write %s" (printf "%s.env_bin - START" $ takeFileName fname :: String)
                  encodeFile (printf "%s.env_bin" $ takeFileName fname :: String) $ closeGlobalEnv g_env
                  BS.putStrLn $ BS.pack $ printf "write %s" (printf "%s.env_bin - DONE" $ takeFileName fname :: String)
                  
                  -- TODO: guarded pShow save to file for g_env exps and closed g_env exps

                writeParsedDefs = do
                  BS.putStrLn $ BS.pack $ printf "defs count: %d" (length defs)
                  let filename = printf "%s.defs" $ takeFileName fname :: String
                  writeFile filename $ unlines $ map ((++ "\n"). show . pShow) defs
                  encodeFile (printf "%s.def_bin" $ takeFileName fname :: String) defs
                  {-
                    Experiment:
                      Stmt/SExp - can be serialized
                      Exp - explodes ; must be the inference algorithm
                  -}
                debugAction = do
                  printTimeDiff (fname ++ " Defs") writeParsedDefs
                  printTimeDiff (fname ++ " Exp") writeResult
                  --when (fname == "./SampleMaterial.lc") $
                  --  fail "stop"
            return $ unsafePerformIO (debugAction >> pure (Right (e, res, err)))
            --return (Right (e, res, err))
        modify $ \(Modules nm im ni) -> Modules nm (IM.insert fid (fi, (src, res)) im) ni
        return $ Right (fi, (src, res))
  where
    filterImports (ImportAllBut ns) = not . (`elem` map sName ns)
    filterImports (ImportJust ns) = (`elem` map sName ns)


-- used in runTests
getDef :: MonadMask m => FilePath -> SName -> Maybe Exp -> MMT m (Infos, [Stmt]) ((Infos, [Stmt]), Either Doc (FileInfo, Either Doc ExpType))
getDef = getDef_ id

getDef_ ex m d ty = loadModule ex Nothing (Left m) <&> \case
    Left err -> (mempty, Left err)
    Right (fname, (src, Left err)) -> (mempty, Left err)
    Right (fname, (src, Right (pm, infos, Left err))) -> (,) infos $ Left err
    Right (fname, (src, Right (pm, infos, Right (_, ge)))) -> (,) infos $ Right
        ( fname
        , case Map.lookup d ge of
          Just (e, thy, si)
            | Just False <- (== thy) <$> ty          -- TODO: better type comparison
                -> Left $ "type of" <+> text d <+> "should be" <+> pShow ty <+> "instead of" <+> pShow thy
            | otherwise -> Right (ET e thy)
          Nothing -> Left $ text d <+> "is not found"
        )

compilePipeline' ex backend m
    = second (either Left (fmap (compilePipeline backend) . snd)) <$> getDef_ ex m "main" (Just outputType)

-- | most commonly used interface for end users
compileMain :: [FilePath] -> IR.Backend -> MName -> IO (Either Doc IR.Pipeline)
compileMain path backend fname
    = fmap snd $ runMM (ioFetch path) $ compilePipeline' (const ()) backend fname

parseModule :: [FilePath] -> MName -> IO (Either Doc String)
parseModule path fname = runMM (ioFetch path) $ loadModule snd Nothing (Left fname) <&> \case
    Left err -> Left err
    Right (fname, (src, Left err)) -> Left err
    Right (fname, (src, Right (pm, infos, _))) -> Right $ pPrintStmts infos

-- used by the compiler-service of the online editor
preCompile :: (MonadMask m, MonadIO m) => [FilePath] -> [FilePath] -> Backend -> FilePath -> IO (String -> m (Either Doc IR.Pipeline, (Infos, String)))
preCompile paths paths' backend mod = do
  res <- runMM (ioFetch paths) $ loadModule ex Nothing $ Left mod
  case res of
    Left err -> error $ "Prelude could not compiled:" ++ show err
    Right (fi, prelude) -> return compile
      where
        compile src = runMM fetch $ do
            let pname = "." </> "Prelude.lc"
            modify $ \(Modules nm im ni) -> Modules (Map.insert pname ni nm) (IM.insert ni (FileInfo ni pname "Prelude" , prelude) im) (ni+1)
            (snd &&& fst) <$> compilePipeline' ex backend "Main"
          where
            fetch imp = \case
                Left "Prelude" -> return $ Right ("./Prelude.lc", "Prelude", undefined)
                Left "Main"    -> return $ Right ("./Main.lc", "Main", return src)
                n -> ioFetch paths' imp n
  where
    ex = second pPrintStmts

pPrintStmts = unlines . map ((++"\n") . plainShow)

