{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Data.Monoid
import Data.Char
import Data.List
--import Data.Either
import qualified Data.Map.Strict as Map
import Data.Time.Clock
import Data.Algorithm.Patience
import Control.Applicative
import Control.Arrow hiding ((<+>))
import Control.Concurrent
import Control.Concurrent.Async
import Control.Monad
import Control.Monad.Reader
--import Control.Monad.Except
import Control.Monad.Catch
import Control.Exception hiding (catch, bracket, finally, mask)
--import Control.Exception hiding (catch)
import Control.Monad.Trans.Control
import Control.DeepSeq
import System.Exit
import System.Directory
import System.FilePath
import System.IO
import Options.Applicative

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Text.Printf

import qualified LambdaCube.IR as IR
import LambdaCube.Compiler
import LambdaCube.Compiler.Pretty hiding ((</>))

------------------------------------------ utils

(<&>) = flip (<$>)

readFileStrict :: FilePath -> IO String
readFileStrict = fmap T.unpack . TIO.readFile

getDirectoryContentsRecursive path = do
  l <- map (path </>) . filter (`notElem` [".",".."]) <$> getDirectoryContents path
  (++)
    <$> filterM doesFileExist l
    <*> (fmap mconcat . traverse getDirectoryContentsRecursive =<< filterM doesDirectoryExist l)

takeExtensions' :: FilePath -> [String]
takeExtensions' = snd . splitExtensions'

splitExtensions' fn = case splitExtension fn of
    (a, "") -> (a, [])
    (fn', ext) -> second (ext:) $ splitExtensions' fn'

getYNChar = do
    c <- getChar
    case c of
        _ | c `elem` ("yY" :: String) -> putChar '\n' >> return True
          | c `elem` ("nN" :: String) -> putChar '\n' >> return False
          | otherwise -> getYNChar

showTime delta
    | t > 1e-1  = printf "%.3fs" t
    | t > 1e-3  = printf "%.1fms" (t/1e-3)
    | otherwise = printf "%.0fus" (t/1e-6)
  where
    t = realToFrac delta :: Double

timeOut :: forall m a . MonadBaseControl IO m => NominalDiffTime -> a -> m a -> m (NominalDiffTime, a)
timeOut dt d m =
  control $ \runInIO ->
    race' (runInIO $ timeDiff m)
          (runInIO $ timeDiff $ liftIO (threadDelay $ round $ dt * 1000000) >> return d)
  where
    liftIO :: IO b -> m b
    liftIO m = liftBaseWith (const m)
    race' a b = either id id <$> race a b
    timeDiff m = (\s x e -> (diffUTCTime e s, x))
      <$> liftIO getCurrentTime
      <*> m
      <*> liftIO getCurrentTime

catchErr :: (MonadCatch m, NFData a, MonadIO m) => (String -> m a) -> m a -> m a
catchErr er m = (force <$> m >>= liftIO . evaluate) `catch` getErr `catch` getPMatchFail
  where
    getErr (e :: ErrorCall) = catchErr er $ er $ show e
    getPMatchFail (e :: PatternMatchFail) = catchErr er $ er $ show e

------------------------------------------

testDataPath = "./testdata"

data Config
  = Config
  { cfgVerbose      :: Bool
  , cfgReject       :: Bool
  , cfgTimeout      :: NominalDiffTime
  , cfgIgnore       :: [String]
  , cfgOverallTime  :: Bool
  } deriving Show

arguments :: Parser (Config, [String])
arguments =
  (,) <$> (Config <$> switch (short 'v' <> long "verbose" <> help "Verbose output during test runs")
                  <*> switch (short 'r' <> long "reject" <> help "Reject test cases with missing, new or different .out files")
                  <*> option (realToFrac <$> (auto :: ReadM Double)) (value 60 <> short 't' <> long "timeout" <> help "Timeout for tests in seconds")
                  <*> many (option (eitherReader Right) (short 'i' <> long "ignore" <> help "Ignore test"))
                  <*> switch (long "overall-time" <> help "Writes overall time to overall-time.txt")
          )
      <*> many (strArgument idm)

data Res = Passed | Accepted | NewRes | TimedOut | Rejected | Failed | ErrorCatched
    deriving (Eq, Ord, Show)

showRes = \case
    ErrorCatched    -> "crashed test"
    Failed          -> "failed test"
    Rejected        -> "rejected result"
    TimedOut        -> "timed out test"
    NewRes          -> "new result"
    Accepted        -> "accepted result"
    Passed          -> "passed test"

instance NFData Res where
    rnf a = a `seq` ()

erroneous = (>= TimedOut)

isWip    = (".wip" `elem`) . takeExtensions'
isReject = (".reject" `elem`) . takeExtensions'

-- for the repl
parse srcName = do
    pplRes <- parseModule ["testdata"] (srcName ++ ".lc")
    case pplRes of
        Left err -> fail $ show err
        Right ppl -> putStrLn ppl

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  hSetBuffering stdin NoBuffering
  (cfg@Config{..}, samplesToTest) <- execParser $
           info (helper <*> arguments)
                (fullDesc <> header "LambdaCube 3D compiler test suite")

  testData <- filter ((".lc" ==) . takeExtension) <$> getDirectoryContentsRecursive testDataPath
  -- select test set: all test or user selected
  let (ignoredTests, testSet) 
        = partition (\d -> any (`isInfixOf` d) cfgIgnore) 
        . map head . group . sort 
        $ [d | d <- testData, s <- if null samplesToTest then [""] else samplesToTest, s `isInfixOf` d]

  unless (null ignoredTests) $ do
    putStrLn $ "------------------------------------ Ignoring " ++ show (length ignoredTests) ++ " tests"
    forM_ ignoredTests putStrLn

  when (null testSet) $ do
    putStrLn $ "test files not found: " ++ show samplesToTest
    exitFailure

  putStrLn $ "------------------------------------ Running " ++ show (length testSet) ++ " tests"

  resultDiffs
    <- runMM (ioFetch [".", testDataPath])
    $ forM (zip [1..] testSet) $ doTest cfg

  let sh :: (FilePath -> Res -> Bool) -> String -> [String]
      sh p b = [ (if any (\(ty, s) -> erroneous ty && not (isWip s)) ss then "!" else "")
                 ++ show noOfResult ++ " "
                 ++ pad 10 (b ++ plural ++ ": ") ++ "\n"
                 ++ unlines (map snd ss)
               | not $ null ss ]
          where
            ss = [(ty, s) | ((_, ty), s) <- zip resultDiffs testSet, p s ty]
            noOfResult = length ss
            plural = ['s' | noOfResult > 1]

  putStrLn "------------------------------------ Summary"
  putStrLn $ unlines $ reverse $
      concat [ sh (\s ty -> ty == x && p s) (w ++ showRes x)
             | (w, p) <- [("", not . isWip), ("wip ", isWip)]
             , x <- [ErrorCatched, Failed, Rejected, TimedOut, NewRes, Accepted]
             ]
      ++ sh (\s ty -> ty == Passed && isWip s) "wip passed test"

  let overallTime = sum $ map fst resultDiffs
  putStrLn $ "Overall time: " ++ showTime overallTime
  when cfgOverallTime $ writeFile "overall-time.txt" $ show (realToFrac overallTime :: Double)

  when (or [erroneous r | ((_, r), f) <- zip resultDiffs testSet, not $ isWip f]) exitFailure
  putStrLn "All OK"
  when (or [erroneous r | ((_, r), f) <- zip resultDiffs testSet, isWip f]) $
        putStrLn "Only work in progress test cases are failing."

splitMPath fn = (joinPath $ reverse as, foldr1 (</>) $ reverse bs ++ [y], intercalate "." $ reverse bs ++ [y])
  where
    (bs, as) = span (\x -> not (null x) && isUpper (head x)) $ reverse xs
    (xs, y) = map takeDirectory . splitPath *** id $ splitFileName $ dropExtension fn

doTest Config{..} (i, fn) = do
    liftIO $ putStr $ pa ++ " " ++ mn ++ " " ++ concat exts ++ " "
    (runtime, res) <- mapMMT (timeOut cfgTimeout $ Left ("!Timed Out", TimedOut))
                    $ catchErr (\e -> return $ Left (tab "!Crashed" e, ErrorCatched))
                    $ liftIO . evaluate =<< (force . f <$> getMain)
    liftIO $ putStr $ "(" ++ showTime runtime ++ ")" ++ "    "
    (msg, result) <- case res of
        Left x -> return x
        Right (op, x) -> liftIO $ compareResult (pad 15 op) (dropExtension fn ++ ".out") x
    liftIO $ putStrLn msg
    return (runtime, result)
  where
    (splitMPath -> (pa, mn', mn), reverse -> exts) = splitExtensions' $ dropExtension fn

    getMain = do
        res <- local (const $ ioFetch [pa]) $ loadModule id Nothing (Left $ mn' ++ concat exts ++ ".lc") <&> \case
            Left err -> (mempty, Left (Nothing, err))
            Right (fname, (src, Left err)) -> (mempty, Left (Just fname, err))
            Right (fname, (src, Right (pm, infos, Left err))) -> (,) infos $ Left (Just fname, err)
            Right (fname, (src, Right (pm, infos, Right (_, ge)))) -> (,) infos $ Right
                ( fname
                , ge
                , case Map.lookup "main" ge of
                  Just (e, thy, si) -> Right (ET e thy)
                  Nothing -> Left $ text "main" <+> "is not found"
                )
        case res of
          (_, Right (fi, _, Right{})) -> removeFromCache $ filePath fi
          _ -> return ()
        return res

    --getDef :: MonadMask m => FilePath -> SName -> Maybe Exp -> MMT m (Infos, [Stmt]) ((Infos, [Stmt]), Either Doc (FilePath, Either Doc ExpType))
    clearPipelineInfo p = p {IR.info = ""}
    f ((i, desug), e) | not $ isReject fn = case e of
        Left (_, show -> e)      -> Left (unlines $ tab "!Failed" e: map show (listTraceInfos i), Failed)
        Right (fname, ge, Left (pShow -> e))
                                 -> Right ("typechecked module", simpleShow $ vcat $ e: showGE fname ge)
        Right (fname, ge, Right (ET e te))
            | te == outputType   -> Right ("compiled pipeline", prettyShowUnlines $ clearPipelineInfo $ compilePipeline OpenGL33 IR.V4F (ET e te))
            | e == trueExp       -> Right ("reducted main", de)
            | te == boolType     -> Left (tab "!Failed" $ "main should be True but it is \n" ++ simpleShow res, Failed)
            | otherwise          -> Right ("reduced main :: " ++ simpleShow (mkDoc (True, False) te), de)
          where
            de = simpleShow $ vcat $ (DAnn "main" $ pShow te) : (DLet "=" "main" res): showGE fname ge
            res = mkDoc (True, False) e
      | otherwise = case e of
        Left (fn, pShow -> e)    -> Right ("error message", simpleShow $ vcat $ e: listAllInfos fn i)
        Right _                  -> Left (tab "!Failed" "failed to catch error", Failed)
      where
        showGE fname ge =  "------------ desugared source code": intersperse "" (map pShow desug)
                        ++ "------------ core code": intersperse ""
                            [      DAnn (text n) (DResetFreshNames $ pShow t)
                              <$$> DLet "=" (text n) (DResetFreshNames $ mkDoc (False, True) e)
                            | (n, (e, t, RangeSI r)) <- Map.toList ge, rangeFile r == fname]
                        ++ listAllInfos' (Just fname) i

    tab msg
        | isWip fn && cfgReject = const msg
        | otherwise = ((msg ++ "\n") ++) . unlines . map ("  " ++) . lines

    compareResult msg ef e = doesFileExist ef >>= \b -> case b of
        False
            | cfgReject -> return ("!Missing .out file", Rejected)
            | otherwise -> writeFile ef e >> return ("New .out file", NewRes)
        True -> do
            e' <- lines <$> readFileStrict ef
            let d = diff e' $ lines e
            case d of
              _ | all (\case Both{} -> True; _ -> False) d -> return ("OK", Passed)
              rs -> do
                    mapM_ putStrLn $ printOldNew msg d
                    putStrLn $ ef ++ " has changed."
                    if cfgReject then return ("!Different .out file", Rejected) else do
                        putStr $ "Accept new " ++ msg ++ " (y/n)? "
                        c <- getYNChar
                        if c
                            then writeFile ef e >> return ("Accepted .out file", Accepted)
                            else return ("!Rejected .out file", Rejected)

printOldNew :: String -> [Item String] -> [String]
printOldNew msg d = (msg ++ " has changed.") : ff [] 0 d
  where
    ff acc n (x@(Both a b): ds) = [a' | n < 5] ++ ff (a':acc) (n+1) ds where a' = "  " ++ a
    ff acc n (Old a: ds)  = g acc n ++ (show (onred "< ") ++ a): ff [] 0 ds
    ff acc n (New b: ds)  = g acc n ++ (show (ongreen "> ") ++ b): ff [] 0 ds
    ff _ _ [] = []
    g acc n | n < 5 = []
    g acc n | n > 10 = "___________": reverse (take 5 acc)
    g acc n = reverse (take (n-5) acc)

pad n s = s ++ replicate (n - length s) ' '

limit :: String -> Int -> String -> String
limit msg n s = take n s ++ if null (drop n s) then "" else msg

