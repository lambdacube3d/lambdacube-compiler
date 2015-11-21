import qualified Data.Map as M

import Infer (parse, infer)
import CGExp (toExp)
import CoreToIR (compilePipeline)
import IR

main = do
    let f = "gfx.lc"
    s <- readFile f
    case parse f s >>= infer of
      Left e -> putStrLn e
      Right s -> do
          print $ compilePipeline False WebGL1 $ toExp $ fst $ s M.! "main"





