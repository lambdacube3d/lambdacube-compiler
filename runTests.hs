{-# LANGUAGE OverloadedStrings, PackageImports, LambdaCase #-}

import Data.List
import Control.Applicative
import Control.Monad
import Control.Monad.Reader

import System.Environment
import System.Directory
import System.FilePath
import System.IO
import Control.Exception (ErrorCall)
import Control.Monad.Catch
import Control.DeepSeq

import Pretty hiding ((</>))
import Type
import Typecheck
import Parser
import Driver
import CoreToIR
import IR (Backend(..))
import Text.Parsec.Pos

instance NFData SourcePos where
    rnf _ = ()

acceptPath = "./tests/accept"
rejectPath = "./tests/reject"

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  hSetBuffering stdin NoBuffering
  args <- getArgs

  let (verboseFlags,samplesToAccept) = partition (== "-v") args
      verbose = verboseFlags /= []
  (testToAccept,testToReject) <- case samplesToAccept of
    [] -> do
      toAccept <- filter (\n -> ".lc" == takeExtension n) <$> getDirectoryContents acceptPath
      toReject <- filter (\n -> ".lc" == takeExtension n) <$> getDirectoryContents rejectPath
      return (map dropExtension toAccept,map dropExtension toReject)
    _ -> return (samplesToAccept,[])

  n <- runMM' $ do
      liftIO $ putStrLn $ "------------------------------------ Checking valid pipelines"
      n1 <- acceptTests testToAccept

      liftIO $ putStrLn $ "------------------------------------ Catching errors (must get an error)"
      n2 <- rejectTests testToReject

      return $ n1 ++ n2
  putStrLn $ "------------------------------------ Summary\n" ++
    if null n 
        then "All OK"
        else "!" ++ show (length n) ++ " tests failed: " ++ intercalate ", " n

writeReduced = runMM' . (testFrame [acceptPath] $ \case
    Left e -> Left e
    Right (Left e) -> Right ("typechecked", show e)
    Right (Right e) -> Right ("reduced main ", ppShow e))

main' x = runMM' $ acceptTests [x]
main'' x = runMM' $ rejectTests [x]

acceptTests = testFrame [acceptPath, rejectPath] $ \case
    Left e -> Left e
    Right (Left e) -> Right ("typechecked", show e)
    Right (Right e)
        | tyOf e == TCon0 "Output"
            -> Right ("compiled main", show . compilePipeline OpenGL33 $ e)
        | tyOf e == TCon0 "Bool" -> case e of
            x@(A0 "True") -> Right ("main ~~> True", ppShow x)
            x -> Left $ "main should be True but it is \n" ++ ppShow x
        | otherwise -> Right ("reduced main " ++ ppShow (tyOf e), ppShow e)
--        | otherwise -> Right ("System-F main ", ppShow . toCore mempty $ e)

rejectTests = testFrame [rejectPath, acceptPath] $ \case
    Left e -> Right ("error message", e)
    Right (Left e) -> Left "failed to catch error"
    Right (Right e) -> Left "failed to catch error"

runMM' = fmap (either (error "impossible") id . fst) . runMM freshTypeVars (ioFetch [])

testFrame dirs f tests = fmap concat $ local (const $ ioFetch dirs) $ forM (zip [1..] (tests :: [String])) $ \(i, n) -> do
--    liftIO $ putStr $ " # " ++ pad 4 (show i) ++ pad 15 n ++ " ... "
    let catchErr m = catch m getErr
        getErr :: ErrorCall -> MM [String]
        getErr e = catchErr $ do
            liftIO $ putStrLn $ "\n!Failed " ++ n ++ "\n" ++ tab (show e)
            return [n]
    catchErr $ do
        result <- catchMM $ getDef (ExpN n) (ExpN "main") Nothing
        liftIO $ case f (((\(r, infos) -> infos `deepseq` r) <$>) <$> result) of
          Left e -> do
            putStrLn $ "\n!Failed " ++ n ++ "\n" ++ tab e
            return [n]
          Right (op, x) -> do
            length x `seq` return [] --compareResult (pad 15 op) (head dirs </> (n ++ ".out")) x
    --        return []
  where
    tab = unlines . map ("  " ++) . lines

compareResult msg ef e = doesFileExist ef >>= \b -> case b of
    False -> writeFile ef e >> putStrLn ("OK - " ++ msg ++ " is written")
    True -> do
        e' <- readFile ef
        case map fst $ filter snd $ zip [0..] $ zipWith (/=) e e' of
          [] -> putStrLn $ "OK - " ++ msg ++ " agrees"
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
                then writeFile ef e >> putStrLn " - accepted."
                else putStrLn " - not Accepted."

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

