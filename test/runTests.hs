{-# LANGUAGE OverloadedStrings, PackageImports, LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor #-}
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

import qualified Data.Text as T
import qualified Data.Text.IO as TIO

import LambdaCube.Compiler.Pretty hiding ((</>))
import LambdaCube.Compiler.Driver
import LambdaCube.Compiler.CoreToIR
import IR (Backend(..))
import Text.Parsec.Pos

testDataPath = "./testdata"

data Res = Accepted | New | Passed | Rejected | Failed | ErrorCatched
    deriving (Eq, Ord, Show)

erroneous = (>= Rejected)

instance NFData Res where
    rnf a = a `seq` ()

readFileStrict :: FilePath -> IO String
readFileStrict = fmap T.unpack . TIO.readFile

getDirectoryContentsRecursive path = do
  l <- map (path </>) . filter (\n -> notElem n [".",".."]) <$> getDirectoryContents path
  -- ignore sub directories that name include .ignore
  dirs <- filter (not . isInfixOf ".ignore") <$> filterM doesDirectoryExist l
  files <- filterM doesFileExist l
  innerContent <- mapM getDirectoryContentsRecursive dirs
  return $ concat $ (filter ((".lc" ==) . takeExtension) files) : innerContent

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
                  <*> flag 15 (15 * 60) (short 't' <> long "notimeout" <> help "Disable timeout for tests"))
      <*> many (strArgument idm)

data TestCase a = Normal a | WorkInProgress a
  deriving (Functor, Show)

testCaseElim normal wip = \case
  Normal x         -> normal x
  WorkInProgress x -> wip x

testCaseVal = testCaseElim id id

instance NFData a => NFData (TestCase a) where
    rnf a = a `seq` ()

type TestCasePath = TestCase FilePath

isNormalTC :: TestCase a -> Bool
isNormalTC (Normal _) = True
isNormalTC _          = False

-- Is TestCase is work in progress?
isWipTC :: TestCase a -> Bool
isWipTC (WorkInProgress _) = True
isWipTC _                  = False

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  hSetBuffering stdin NoBuffering
  (cfg, samplesToTest) <- execParser opts
  testData <- sort <$> getDirectoryContentsRecursive testDataPath
  let setNub = Set.toList . Set.fromList
      -- select test set: all test or user selected
      testSet = if null samplesToTest
                  then testData
                  else setNub $ concat [filter (isInfixOf s) testData | s <- samplesToTest]
      -- filter in test set according the file extesnion
      filterTestSet testtype ext = map (testtype . dropExtension) . filter (\n -> ext == takeExtensions n) $ testSet
      testToAccept  = filterTestSet Normal ".lc"
      testToReject  = filterTestSet Normal ".reject.lc"
      -- work in progress test
      testToAcceptWIP  = filterTestSet WorkInProgress ".wip.lc"
      testToRejectWIP  = filterTestSet WorkInProgress ".wip.reject.lc" ++ filterTestSet WorkInProgress ".reject.wip.lc"
  when (null $ concat [testToAccept, testToReject, testToAcceptWIP, testToRejectWIP]) $ do
    liftIO $ putStrLn $ "test files not found: " ++ show samplesToTest
    exitFailure

  resultDiffs <- runMM' $ do
      liftIO $ putStrLn $ "------------------------------------ Checking valid pipelines"
      acceptDiffs <- acceptTests cfg $ testToAccept ++ testToAcceptWIP

      liftIO $ putStrLn $ "------------------------------------ Catching errors (must get an error)"
      rejectDiffs <- rejectTests cfg $ testToReject ++ testToRejectWIP

      return $ acceptDiffs ++ rejectDiffs

  let sh b ty = [(if erroneous ty then "!" else "") ++ show noOfResult ++ " " ++ pad 10 (b ++ plural ++ ": ") ++ "\n" ++ unlines ss | not $ null ss]
          where
            noOfResult = length ss
            plural = if noOfResult == 1 then "" else "s"
            wips = map testCaseVal (testToRejectWIP ++ testToAcceptWIP)
            wipPassedFilter Passed s = s `elem` wips
            wipPassedFilter _      _ = True
            ss = sort [s | (ty', s) <- map testCaseVal resultDiffs, ty' == ty, wipPassedFilter ty s]

  putStrLn $ "------------------------------------ Summary\n" ++
    if null resultDiffs
        then ""
        else unlines $ concat
          [ sh "crashed test" ErrorCatched
          , sh "failed test" Failed
          , sh "rejected result" Rejected
          , sh "new result" New
          , sh "accepted result" Accepted
          , sh "wip passed test" Passed
          ]
  when (any erroneous (map (fst . testCaseVal) $ filter isNormalTC resultDiffs))
       exitFailure
  putStrLn "All OK"
  unless (null resultDiffs) $ putStrLn "Only work in progress test cases are failing."
  where
    opts = info (helper <*> arguments)
                (fullDesc <> header "LambdaCube 3D compiler test suite")

acceptTests cfg = testFrame cfg [".",testDataPath] $ \case
    Left e -> Left e
    Right (fname, Left e, i) -> Right ("typechecked", unlines $ e: "tooltips:": [showRange (b, e) ++ "  " ++ intercalate " | " m | (b, e, m) <- listInfos i, sourceName b == fname])
    Right (fname, Right e, i)
        | True <- i `deepseq` False -> error "impossible"
        | tyOf e == outputType
            -> Right ("compiled main", show . compilePipeline OpenGL33 $ e)
        | e == trueExp -> Right ("main ~~> True", ppShow e)
        | tyOf e == boolType -> Left $ "main should be True but it is \n" ++ ppShow e
        | otherwise -> Right ("reduced main " ++ ppShow (tyOf e), ppShow e)
--        | otherwise -> Right ("System-F main ", ppShow . toCore mempty $ e)

rejectTests cfg = testFrame cfg [".",testDataPath] $ \case
    Left e -> Right ("error message", e)
    Right _ -> Left "failed to catch error"

runMM' = fmap (either (error "impossible") id . fst) . runMM (ioFetch [])

testFrame :: Config -> [FilePath] -> (Either String (FilePath, Either String Exp, Infos) -> Either String (String, String)) -> [TestCasePath] -> MMT IO [TestCase (Res, String)]
testFrame Config{..} dirs f tests
    = local (const $ ioFetch dirs')
    $ testFrame_
        cfgTimeout
        (if cfgReject then alwaysReject else compareResult)
        (head dirs')
        (\n -> f <$> (Right <$> getDef n "main" Nothing) `catchMM` (return . Left . show))
        tests
  where
    dirs_ = [takeDirectory f | f <- map testCaseVal tests, takeFileName f /= f]
    dirs' = dirs ++ dirs_ -- if null dirs_ then dirs else dirs_


timeOut :: Int -> a -> MM a -> MM (NominalDiffTime, a)
timeOut n d = mapMMT $ \m ->
  control (\runInIO ->
    race' (runInIO $ timeDiff m)
          (runInIO $ timeDiff ((liftIO $ threadDelay (n * 1000000)) >> return d))
  )
  where
    race' a b = either id id <$> race a b
    timeDiff m = (\s x e -> (diffUTCTime e s, x))
      <$> liftIO getCurrentTime
      <*> m
      <*> liftIO getCurrentTime

testFrame_ timeout compareResult path action tests = fmap concat $ forM (zip [1..] (tests :: [TestCasePath])) $ \(i, tn) -> do
    let n = testCaseVal tn
    let er e = do
            liftIO $ putStr $ "!Crashed " ++ n ++ "\n" ++ tab e
            return $ [(,) ErrorCatched <$> tn]
    catchErr er $ do
        liftIO $ putStrLn $ unwords ["\nStart to compile", n]
        (runtime, result) <- timeOut timeout (Left "Timed Out") (action n)
        liftIO $ case result of
            Left e -> do
              putStr $ "!Failed " ++ n ++ "\n" ++ tab e
              putStrLn $ unwords ["Runtime:", show runtime]
              return [(,) Failed <$> tn]
            Right (op, x) -> do
              putStrLn $ unwords ["Runtime:", show runtime]
              length x `seq` compareResult tn (pad 15 op) (path </> (n ++ ".out")) x
  where
    tab = unlines . map ("  " ++) . lines

-- Reject unrigestered or chaned results automatically
alwaysReject tn msg ef e = do
  let n = testCaseVal tn
  doesFileExist ef >>= \b -> case b of
    False -> putStrLn ("Unregistered - " ++ msg) >> return [(,) Rejected <$> tn]
    True -> do
        e' <- readFileStrict ef
        case map fst $ filter snd $ zip [0..] $ zipWith (/=) e e' of
          [] -> return [(,) Passed <$> tn]
          rs -> do
            putStrLn $ msg ++ " has changed."
            putStrLn "------------------------------------------- Old"
            putStrLn $ showRanges ef rs e'
            putStrLn "------------------------------------------- New"
            putStrLn $ showRanges ef rs e
            putStrLn "-------------------------------------------"
            return [(,) Rejected <$> tn, (,) Failed <$> tn]

compareResult tn msg ef e = do
  let n = testCaseVal tn
  doesFileExist ef >>= \b -> case b of
    False -> writeFile ef e >> putStrLn ("OK - " ++ msg ++ " is written") >> return [(,) New <$> tn]
    True -> do
        e' <- readFileStrict ef
        case map fst $ filter snd $ zip [0..] $ zipWith (/=) e e' ++ replicate (abs $  length e - length e') True of
          [] -> return [(,) Passed <$> tn]
          rs -> do
            putStrLn $ msg ++ " has changed."
            putStrLn "------------------------------------------- Old"
            putStrLn $ showRanges ef rs e'
            putStrLn "------------------------------------------- New"
            putStrLn $ showRanges ef rs e
            putStrLn "-------------------------------------------"
            putStr $ "Accept new " ++ msg ++ " (y/n)? "
            c <- length e' `seq` getChar
            if c `elem` ("yY\n" :: String)
                then writeFile ef e >> putStrLn " - accepted." >> return [(,) Accepted <$> tn, (,) Passed <$> tn]
                else putStrLn " - not Accepted." >> return [(,) Rejected <$> tn, (,) Failed <$> tn]

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

