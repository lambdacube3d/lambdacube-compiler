{-# LANGUAGE ViewPatterns, TupleSections #-}
import Data.Char
import System.Directory
import System.FilePath
import Text.Printf
import Control.Monad
import Data.Map (Map,(!))
import qualified Data.Map as Map

-- HINT: lambdacube-compiler-test-suite --overall-time performance +RTS -tcurrent.log --machine-readable
-- output: current.log overall-time.txt

resultPath = "performance"

main = do
  -- read current result
  overallTime <- read <$> readFile "overall-time.txt" :: IO Double
  let toDouble = read :: String -> Double
      toInteger = read :: String -> Integer
  new <- Map.fromList . (:) ("overall_time",show overallTime) . read . unlines . tail . lines <$> readFile "current.log" :: IO (Map String String)
  let totalAlloc a = toInteger $ a ! "bytes allocated"
      peakAlloc a = toInteger $ a ! "peak_megabytes_allocated"
      totalAllocF a = toDouble $ a ! "bytes allocated"
      peakAllocF a = toDouble $ a ! "peak_megabytes_allocated"
      overallTime a = toDouble $ a ! "overall_time"

  putStrLn $ printf "%-20s time: % 6.3fs \tpeak mem: % 6d MBytes total alloc: %d bytes" "CURRENT" (overallTime new) (peakAlloc new) (totalAlloc new)
  -- read previous results
  perfs <- filter ((".perf" ==) . takeExtension) <$> getDirectoryContents "performance" >>= mapM (\n -> (n,) . read <$> readFile (resultPath </> n)) :: IO [(String,Map String String)]
  forM_ perfs $ \(name,old) -> do
    putStrLn $ printf "%-20s time: %+6.3f%% \tpeak mem: %+6.3f%% \ttotal alloc: %+6.3f%%"
      name (100*(overallTime new / overallTime old - 1)) (100*(peakAllocF new / peakAllocF old - 1)) (100*(totalAllocF new / totalAllocF old - 1))
  --TODO
  --writeFile "performance/release-0.5.perf" $ show new