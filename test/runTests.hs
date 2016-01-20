{-# LANGUAGE OverloadedStrings, PackageImports, LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
module Main where

import Data.List
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

import LambdaCube.Compiler.Pretty hiding ((</>))
import LambdaCube.Compiler.Driver
import LambdaCube.Compiler.CoreToIR
import IR (Backend(..))
import Text.Parsec.Pos

instance NFData SourcePos where
    rnf _ = ()

testDataPath = "./testdata"

data Res = Accepted | New | Rejected | Failed | ErrorCatched
    deriving (Eq, Ord, Show)

erroneous = (>= Rejected)

instance NFData Res where
    rnf a = a `seq` ()

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

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  hSetBuffering stdin NoBuffering
  (cfg, samplesToAccept) <- execParser opts
  testData <- sort <$> getDirectoryContentsRecursive testDataPath
  let setNub = Set.toList . Set.fromList
      -- select test set: all test or user selected
      testSet = if null samplesToAccept
                  then testData
                  else setNub $ concat [filter (isInfixOf s) testData | s <- samplesToAccept]
      -- filter in test set according the file extesnion
      filterTestSet ext = map dropExtension . filter (\n -> ext == takeExtensions n) $ testSet
      testToAccept  = filterTestSet ".lc"
      testToReject  = filterTestSet ".reject.lc"
      -- work in progress test
      testToAcceptWIP  = filterTestSet ".wip.lc"
      testToRejectWIP  = filterTestSet ".wip.reject.lc" ++ filterTestSet ".reject.wip.lc"
  when (null $ testToAccept ++ testToReject) $ do
    liftIO $ putStrLn $ "test files not found: " ++ show samplesToAccept
    exitFailure

  n <- runMM' $ do
      liftIO $ putStrLn $ "------------------------------------ Checking valid pipelines"
      n1 <- acceptTests cfg testToAccept

      liftIO $ putStrLn $ "------------------------------------ Catching errors (must get an error)"
      n2 <- rejectTests cfg testToReject

      return $ n1 ++ n2

  let sh b ty = [(if erroneous ty then "!" else "") ++ show (length ss) ++ " " ++ pad 10 (b ++ ": ") ++ intercalate ", " ss | not $ null ss]
          where
            ss = sort [s | (ty', s) <- n, ty' == ty]
  let results = [t | (t,_) <- n]

  putStrLn $ "------------------------------------ Summary\n" ++
    if null n 
        then "All OK"
        else unlines $
            sh "crashed test" ErrorCatched
         ++ sh "failed test" Failed
         ++ sh "rejected result" Rejected
         ++ sh "new result" New
         ++ sh "accepted result" Accepted
  when (any erroneous results) exitFailure
  where
    opts = info (helper <*> arguments)
                (fullDesc <> header "LambdaCube 3D compiler test suite")

acceptTests cfg = testFrame cfg [".",testDataPath] $ \case
    Left e -> Left e
    Right (fname, Left e, i) -> Right ("typechecked", unlines $ e: "tooltips:": [showRange (b, e) ++ "  " ++ m | (b, e, m) <- nub{-temporal; TODO: fail in case of duplicate items-} i, sourceName b == fname])
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

testFrame :: Config -> [FilePath] -> (Either String (FilePath, Either String Exp, Infos) -> Either String (String, String)) -> [String] -> MMT IO [(Res, String)]
testFrame Config{..} dirs f tests
    = local (const $ ioFetch dirs')
    $ testFrame_
        cfgTimeout
        (if cfgReject then alwaysReject else compareResult)
        (head dirs')
        (\n -> f <$> (Right <$> getDef n "main" Nothing) `catchMM` (return . Left . show))
        tests
  where
    dirs_ = [takeDirectory f | f <- tests, takeFileName f /= f]
    dirs' = dirs ++ dirs_ -- if null dirs_ then dirs else dirs_


timeOut :: Int -> a -> MM a -> MM a
timeOut n d = mapMMT $ \m ->
  control (\runInIO ->
    race' (runInIO m)
          (threadDelay (n * 1000000) >> (runInIO $ return d)))
  where
    race' a b = either id id <$> race a b

testFrame_ timeout compareResult path action tests = fmap concat $ forM (zip [1..] (tests :: [String])) $ \(i, n) -> do
    let er e = do
            liftIO $ putStrLn $ "\n!Crashed " ++ n ++ "\n" ++ tab e
            return [(ErrorCatched, n)]
    catchErr er $ do
        result <- timeOut timeout (Left "Timed Out") (action n)
        liftIO $ case result of
          Left e -> do
            putStrLn $ "\n!Failed " ++ n ++ "\n" ++ tab e
            return [(Failed, n)]
          Right (op, x) -> do
            length x `seq` compareResult n (pad 15 op) (path </> (n ++ ".out")) x
  where
    tab = unlines . map ("  " ++) . lines

-- Reject unrigestered or chaned results automatically
alwaysReject n msg ef e = doesFileExist ef >>= \b -> case b of
    False -> putStrLn ("Unregistered - " ++ msg) >> return [(Rejected, n)]
    True -> do
        e' <- readFile ef
        case map fst $ filter snd $ zip [0..] $ zipWith (/=) e e' of
          [] -> return []
          rs -> do
            putStrLn $ msg ++ " has changed."
            putStrLn "------------------------------------------- Old"
            putStrLn $ showRanges ef rs e'
            putStrLn "------------------------------------------- New"
            putStrLn $ showRanges ef rs e
            putStrLn "-------------------------------------------"
            return [(Rejected, n)]

compareResult n msg ef e = doesFileExist ef >>= \b -> case b of
    False -> writeFile ef e >> putStrLn ("OK - " ++ msg ++ " is written") >> return [(New, n)]
    True -> do
        e' <- readFile ef
        case map fst $ filter snd $ zip [0..] $ zipWith (/=) e e' ++ replicate (abs $  length e - length e') True of
          [] -> return []
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
                then writeFile ef e >> putStrLn " - accepted." >> return [(Accepted, n)]
                else putStrLn " - not Accepted." >> return [(Rejected, n)]

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

