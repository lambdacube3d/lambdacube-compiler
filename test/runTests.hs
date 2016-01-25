{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
module Main where

import Data.List
import Data.Time.Clock
import Control.Applicative
import Control.Arrow
import Control.Concurrent
import Control.Concurrent.Async
import Control.Monad
import Control.Monad.Reader

import System.Environment
import System.Exit
import System.Directory
import System.FilePath
import System.IO
import Control.Exception hiding (catch)
import Control.Monad.Trans.Control
import Control.Monad.Catch
import Control.DeepSeq
import qualified Data.Set as Set
import Options.Applicative
import Options.Applicative.Types
import Text.Printf

import qualified Data.Text as T
import qualified Data.Text.IO as TIO

import LambdaCube.Compiler.Pretty hiding ((</>))
import LambdaCube.Compiler.Driver
import LambdaCube.Compiler.CoreToIR
import IR (Backend(..))
import Text.Parsec.Pos

------------------------------------------ utils

instance NFData Res where
    rnf a = a `seq` ()

readFileStrict :: FilePath -> IO String
readFileStrict = fmap T.unpack . TIO.readFile

getDirectoryContentsRecursive path = do
  l <- map (path </>) . filter (`notElem` [".",".."]) <$> getDirectoryContents path
  -- ignore sub directories that name include .ignore
  dirs <- filter (not . isInfixOf ".ignore") <$> filterM doesDirectoryExist l
  files <- filterM doesFileExist l
  innerContent <- mapM getDirectoryContentsRecursive dirs
  return $ concat $ filter ((".lc" ==) . takeExtension) files : innerContent

takeExtensions' :: FilePath -> [String]
takeExtensions' fn = case splitExtension fn of
    (_, "") -> []
    (fn', ext) -> ext: takeExtensions' fn'

------------------------------------------

data Config
  = Config
  { cfgVerbose :: Bool
  , cfgReject  :: Bool
  , cfgTimeout :: Int -- in seconds
  } deriving Show

arguments :: Parser (Config, [String])
arguments =
  (,) <$> (Config <$> switch (short 'v' <> long "verbose" <> help "Verbose output during test runs")
                  <*> switch (short 'r' <> long "reject" <> help "Reject new and different values inmediatelly")
                  <*> flag 60 (15 * 60) (short 't' <> long "notimeout" <> help "Disable timeout for tests"))
      <*> many (strArgument idm)

testDataPath = "./testdata"
dirs = [".",testDataPath]

data Res = Passed | Accepted | New | TimedOut | Rejected | Failed | ErrorCatched
    deriving (Eq, Ord, Show)

erroneous = (>= TimedOut)

type TestCaseInfo = (WipInfo, Bool)  -- True: accept test; False: reject test

data WipInfo = Normal | WorkInProgress
  deriving (Eq, Show)

instance NFData WipInfo where
    rnf a = a `seq` ()

testCaseVal = snd

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  hSetBuffering stdin NoBuffering
  (cfg, samplesToTest) <- execParser $
           info (helper <*> arguments)
                (fullDesc <> header "LambdaCube 3D compiler test suite")

  testData <- sort <$> getDirectoryContentsRecursive testDataPath
  let setNub = Set.toList . Set.fromList
      -- select test set: all test or user selected
      testSet = if null samplesToTest
                  then testData
                  else setNub $ concat [filter (isInfixOf s) testData | s <- samplesToTest]

      testSet' = [((if ".wip" `elem` tags then WorkInProgress else Normal, ".reject" `notElem` tags), dropExtension n) | n <- testSet, let tags = takeExtensions' n ]
  when (null testSet') $ do
    liftIO $ putStrLn $ "test files not found: " ++ show samplesToTest
    exitFailure

  liftIO $ putStrLn $ "------------------------------------ Running " ++ show (length testSet') ++ " tests"
  resultDiffs <- acceptTests cfg testSet'

  let sh b ty = [(if erroneous ty then "!" else "") ++ show noOfResult ++ " " ++ pad 10 (b ++ plural ++ ": ") ++ "\n" ++ unlines ss | not $ null ss]
          where
            noOfResult = length ss
            plural = if noOfResult == 1 then "" else "s"
            wips = [x | ((WorkInProgress, _), x) <- testSet']
            wipPassedFilter Passed s = s `elem` wips
            wipPassedFilter _      _ = True
            ss = sort [s | ((_, ty'), (_, s)) <- zip resultDiffs testSet', ty' == ty, wipPassedFilter ty s]

  unless (null resultDiffs) $ putStrLn $ unlines $ concat
          [ ["------------------------------------ Summary"]
          , sh "crashed test" ErrorCatched
          , sh "failed test" Failed
          , sh "rejected result" Rejected
          , sh "timed out test" TimedOut
          , sh "new result" New
          , sh "accepted result" Accepted
          , sh "wip passed test" Passed
          , ["Overall time: " ++ showTime (sum $ map fst resultDiffs)]
          ]

  when (or [erroneous r | ((_, r), ((Normal, _), _)) <- zip resultDiffs testSet']) exitFailure
  putStrLn "All OK"
  when (or [erroneous r | ((_, r), ((WorkInProgress, _), _)) <- zip resultDiffs testSet']) $
        putStrLn "Only work in progress test cases are failing."

acceptTests Config{..} tests
    = fmap (either (error "impossible") id . fst)
    $ runMM (ioFetch dirs')
    $ forM (zip [1..] tests) mkTest
  where
    dirs' = nub $ dirs ++ [takeDirectory f | f <- map testCaseVal tests, takeFileName f /= f]

    mkTest (i, ((wip, accept), n)) = do
        let er e = return (tab "!Crashed" e, ErrorCatched)
        (runtime, (msg, result)) <- timeOut cfgTimeout ("!Timed Out", TimedOut) $ catchErr er $ do
            result <- liftIO . evaluate =<< (force <$> action n)
            liftIO $ case result of
                Left e -> return (tab "!Failed" e, Failed)
                Right (op, x) -> (,) "" <$> (if cfgReject then alwaysReject else compareResult) (pad 15 op) (head dirs' </> (n ++ ".out")) x
        liftIO $ putStrLn $ n ++" (" ++ showTime runtime ++ ")" ++ if null msg then "" else "    " ++ msg
        return (runtime, result)
      where
        f | accept = \case
            Left e -> Left e
            Right (fname, Left e, i) -> Right ("typechecked", unlines $ e: "tooltips:": [showRange (b, e) ++ "  " ++ intercalate " | " m | (b, e, m) <- listInfos i, sourceName b == fname])
            Right (fname, Right e, i)
                | True <- i `deepseq` False -> error "impossible"
                | tyOf e == outputType
                    -> Right ("compiled main", show . compilePipeline OpenGL33 $ e)
                | e == trueExp -> Right ("main ~~> True", ppShow e)
                | tyOf e == boolType -> Left $ "main should be True but it is \n" ++ ppShow e
                | otherwise -> Right ("reduced main " ++ ppShow (tyOf e), ppShow e)
          | otherwise = \case
            Left e -> Right ("error message", e)
            Right _ -> Left "failed to catch error"

        action n = f <$> (Right <$> getDef n "main" Nothing) `catchMM` (return . Left . show)

        tab msg
            | wip == WorkInProgress = const msg
            | otherwise = ((msg ++ "\n") ++) . unlines . map ("  " ++) . lines

        -- Reject unrigestered or chaned results automatically
        alwaysReject msg ef e = doesFileExist ef >>= \b -> case b of
            False -> putStrLn ("Unregistered - " ++ msg) >> return Rejected
            True -> do
                e' <- readFileStrict ef
                case map fst $ filter snd $ zip [0..] $ zipWith (/=) e e' of
                  [] -> return Passed
                  rs -> do
                    printOldNew msg (showRanges ef rs e') (showRanges ef rs e)
                    return Rejected

        compareResult msg ef e = doesFileExist ef >>= \b -> case b of
            False -> writeFile ef e >> putStrLn ("OK - " ++ msg ++ " is written") >> return New
            True -> do
                e' <- readFileStrict ef
                case map fst $ filter snd $ zip [0..] $ zipWith (/=) e e' ++ replicate (abs $  length e - length e') True of
                  [] -> return Passed
                  rs -> do
                    printOldNew msg (showRanges ef rs e') (showRanges ef rs e)
                    putStr $ "Accept new " ++ msg ++ " (y/n)? "
                    c <- length e' `seq` getChar
                    if c `elem` ("yY\n" :: String)
                        then writeFile ef e >> putStrLn " - accepted." >> return Accepted
                        else putStrLn " - not Accepted." >> return Rejected


showTime delta = let t = realToFrac delta :: Double
                     res  | t > 1e-1  = printf "%.3fs" t
                          | t > 1e-3  = printf "%.1fms" (t/1e-3)
                          | otherwise = printf "%.0fus" (t/1e-6)
                 in res

timeOut :: Int -> a -> MM a -> MM (NominalDiffTime, a)
timeOut n d = mapMMT $ \m ->
  control $ \runInIO ->
    race' (runInIO $ timeDiff m)
          (runInIO $ timeDiff $ liftIO (threadDelay $ n * 1000000) >> return d)
  where
    race' a b = either id id <$> race a b
    timeDiff m = (\s x e -> (diffUTCTime e s, x))
      <$> liftIO getCurrentTime
      <*> m
      <*> liftIO getCurrentTime

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

