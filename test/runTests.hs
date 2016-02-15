{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
module Main where

import Data.List
import Data.Either
import Data.Time.Clock
import Control.Applicative
import Control.Concurrent
import Control.Concurrent.Async
import Control.Monad
import Control.Monad.Reader
import Control.Exception hiding (catch)
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

import LambdaCube.Compiler

------------------------------------------ utils

readFileStrict :: FilePath -> IO String
readFileStrict = fmap T.unpack . TIO.readFile

getDirectoryContentsRecursive path = do
  l <- map (path </>) . filter (`notElem` [".",".."]) <$> getDirectoryContents path
  -- ignore sub directories that name include .ignore
  (++)
    <$> (filter ((".lc" ==) . takeExtension) <$> filterM doesFileExist l)
    <*> (fmap concat . mapM getDirectoryContentsRecursive . filter ((".ignore" `notElem`) . takeExtensions') =<< filterM doesDirectoryExist l)

takeExtensions' :: FilePath -> [String]
takeExtensions' fn = case splitExtension fn of
    (_, "") -> []
    (fn', ext) -> ext: takeExtensions' fn'

getYNChar = do
    c <- getChar
    case c of
        _ | c `elem` ("yY\n" :: String) -> putChar '\n' >> return True
          | c `elem` ("nN\n" :: String) -> putChar '\n' >> return False
          | otherwise -> getYNChar

showTime delta
    | t > 1e-1  = printf "%.3fs" t
    | t > 1e-3  = printf "%.1fms" (t/1e-3)
    | otherwise = printf "%.0fus" (t/1e-6)
  where
    t = realToFrac delta :: Double

timeOut :: MonadBaseControl IO m => NominalDiffTime -> a -> m a -> m (NominalDiffTime, a)
timeOut dt d m =
  control $ \runInIO ->
    race' (runInIO $ timeDiff m)
          (runInIO $ timeDiff $ liftIO (threadDelay $ round $ dt * 1000000) >> return d)
  where
    liftIO = liftBaseWith . const
    race' a b = either id id <$> race a b
    timeDiff m = (\s x e -> (diffUTCTime e s, x))
      <$> liftIO getCurrentTime
      <*> m
      <*> liftIO getCurrentTime

------------------------------------------

testDataPath = "./testdata"

data Config
  = Config
  { cfgVerbose :: Bool
  , cfgReject  :: Bool
  , cfgTimeout :: NominalDiffTime
  , cfgIgnore  :: [String]
  } deriving Show

arguments :: Parser (Config, [String])
arguments =
  (,) <$> (Config <$> switch (short 'v' <> long "verbose" <> help "Verbose output during test runs")
                  <*> switch (short 'r' <> long "reject" <> help "Reject test cases with missing, new or different .out files")
                  <*> option (realToFrac <$> (auto :: ReadM Double)) (value 60 <> short 't' <> long "timeout" <> help "Timeout for tests in seconds")
                  <*> many (option (eitherReader Right) (short 'i' <> long "ignore" <> help "Ignore test"))
          )
      <*> many (strArgument idm)

data Res = Passed | Accepted | New | TimedOut | Rejected | Failed | ErrorCatched
    deriving (Eq, Ord, Show)

showRes = \case
    ErrorCatched    -> "crashed test"
    Failed          -> "failed test"
    Rejected        -> "rejected result"
    TimedOut        -> "timed out test"
    New             -> "new result"
    Accepted        -> "accepted result"
    Passed          -> "passed test"

instance NFData Res where
    rnf a = a `seq` ()

erroneous = (>= TimedOut)

isWip    = (".wip" `elem`) . takeExtensions'
isReject = (".reject" `elem`) . takeExtensions'

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  hSetBuffering stdin NoBuffering
  (cfg@Config{..}, samplesToTest) <- execParser $
           info (helper <*> arguments)
                (fullDesc <> header "LambdaCube 3D compiler test suite")

  testData <- getDirectoryContentsRecursive testDataPath
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

  (Right resultDiffs, _)
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
             , x <- [ErrorCatched, Failed, Rejected, TimedOut, New, Accepted]
             ]
      ++ sh (\s ty -> ty == Passed && isWip s) "wip passed test"

  putStrLn $ "Overall time: " ++ showTime (sum $ map fst resultDiffs)

  when (or [erroneous r | ((_, r), f) <- zip resultDiffs testSet, not $ isWip f]) exitFailure
  putStrLn "All OK"
  when (or [erroneous r | ((_, r), f) <- zip resultDiffs testSet, isWip f]) $
        putStrLn "Only work in progress test cases are failing."

doTest Config{..} (i, fn) = do
    liftIO $ putStr $ fn ++ " "
    (runtime, res) <- mapMMT (timeOut cfgTimeout $ Left ("!Timed Out", TimedOut))
                    $ catchErr (\e -> return $ Left (tab "!Crashed" e, ErrorCatched))
                    $ liftIO . evaluate =<< (force <$> action)
    liftIO $ putStr $ "(" ++ showTime runtime ++ ")" ++ "    "
    (msg, result) <- case res of
        Left x -> return x
        Right (op, x) -> liftIO $ compareResult (pad 15 op) (dropExtension fn ++ ".out") x
    liftIO $ putStrLn msg
    return (runtime, result)
  where
    n = dropExtension fn

    getMain n = do
        r@(fname, x, _) <- getDef n "main" Nothing
        when (isRight x) $ removeFromCache fname
        return r

    action = f <$> (Right <$> getMain n) `catchMM` (\e is -> return $ Left (e, is))

    f | not $ isReject fn = \case
        Left (e, i)              -> Left (unlines $ tab "!Failed" e: listTraceInfos i, Failed)
        Right (fname, Left e, i) -> Right ("typechecked module" , unlines $ e: listAllInfos i)
        Right (fname, Right (e, te), force -> i)
            | te == outputType   -> Right ("compiled pipeline", prettyShowUnlines $ compilePipeline OpenGL33 (e, te))
            | e == trueExp       -> Right ("reducted main", ppShow e)
            | te == boolType     -> Left (tab "!Failed" $ "main should be True but it is \n" ++ ppShow e, Failed)
            | otherwise          -> Right ("reduced main " ++ ppShow te, ppShow e)
      | otherwise = \case
        Left (e, i)              -> Right ("error message", unlines $ e: listAllInfos i)
        Right _                  -> Left (tab "!Failed" "failed to catch error", Failed)

    tab msg
        | isWip fn && cfgReject = const msg
        | otherwise = ((msg ++ "\n") ++) . unlines . map ("  " ++) . lines

    compareResult msg ef e = doesFileExist ef >>= \b -> case b of
        False
            | cfgReject -> return ("!Missing .out file", Rejected)
            | otherwise -> writeFile ef e >> return ("New .out file", New)
        True -> do
            e' <- readFileStrict ef
            case map fst $ filter snd $ zip [0..] $ zipWith (/=) e e' ++ replicate (abs $  length e - length e') True of
              [] -> return ("OK", Passed)
              rs | cfgReject-> return ("!Different .out file", Rejected)
                 | otherwise -> do
                    printOldNew msg (showRanges ef rs e') (showRanges ef rs e)
                    putStrLn $ ef ++ " has changed."
                    putStr $ "Accept new " ++ msg ++ " (y/n)? "
                    c <- length e' `seq` getYNChar
                    if c
                        then writeFile ef e >> return ("Accepted .out file", Accepted)
                        else return ("!Rejected .out file", Rejected)

printOldNew msg old new = do
    putStrLn $ msg ++ " has changed."
    putStrLn "------------------------------------------- Old"
    putStrLn old
    putStrLn "------------------------------------------- New"
    putStrLn new
    putStrLn "-------------------------------------------"

pad n s = s ++ replicate (n - length s) ' '

limit :: String -> Int -> String -> String
limit msg n s = take n s ++ if null (drop n s) then "" else msg

showRanges :: String -> [Int] -> String -> String
showRanges fname is e = (if head rs == 0 then "" else "...\n")
    ++ limit ("\n... (see " ++ fname ++ " for more differences)") 140000 (intercalate "\n...\n" $ f (zipWith (-) rs (0:rs)) e)
  where
    f :: [Int] -> String -> [String]
    f (i:is) e = g is $ drop i e
    f [] "" = []
    f [] _ = ["\n..."]
    g (i:is) e = take i e: f is (drop i e)
    rs = (head is - x) : concat [[a + x, b - x] | (a, b) <- zip is (tail is), a + y < b] ++ [last is + x]
    x = 100000
    y = 3*x

