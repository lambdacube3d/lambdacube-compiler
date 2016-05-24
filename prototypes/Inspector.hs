{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

import Data.List
import Data.Maybe
import Control.Arrow
import Control.Category hiding ((.), id)
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Identity
import Debug.Trace
import System.Environment
import System.IO

import LambdaCube.Compiler.Pretty

import LamMachine

--------------------------------------------------------------------------------

data StepTree a b
    = NoStep
--    | Ready a
    | Step a b (StepTree a b)
    | Steps a (StepTree a b) (StepTree a b)
  deriving Show

stepTree :: MSt -> StepTree StepTag MSt
stepTree = fst . steps 0
                       (runState $ return NoStep)
                       (\t c -> runState $ Step t <$> get <*> state c)
                       (\t c2 c1 -> runState $ Steps t <$> state c1 <*> state c2)

stepList (initSt -> st) = ("Start", st): f (stepTree st)
  where
    f = \case
        NoStep -> []
        Step t x st -> (t, x): f st
        Steps _ a b -> f a ++ f b


data Command = UpArrow | DownArrow | LeftArrow | RightArrow
    | IntArg Int | ProgramChange
    deriving (Eq, Show)

getCommand pr msg = do
  putStr $ (if pr then "\n" else "\CR") ++ "-------------- " ++ msg ++ " --------> "
  getChar >>= \case
    '\ESC' -> getChar >>= \case
     '[' -> getChar >>= \case
      'A' -> c 4 >> ret UpArrow
      'B' -> c 4 >> ret DownArrow
      'C' -> c 4 >> ret LeftArrow
      'D' -> c 4 >> ret RightArrow
      c -> clear c
     c -> clear c
    d | '0' <= d && d <= '9' -> readI [d]
    'n' -> ret ProgramChange
    c -> clear c
  where
    ret a = {-putStr ("  --  " ++ show a) >> -} return a
    readI ds = getChar >>= \case
        d | '0' <= d && d <= '9' -> readI $ d: ds
        '\n' -> c 1 >> ret (IntArg $ read $ reverse ds)
        c -> clear c
    clear _ = getCommand True msg
    c n = replicateM n $ putChar '\b'


main = do
  hSetBuffering stdin NoBuffering
  hSetBuffering stdout NoBuffering
  getArgs >>= \case
    [b, n] -> 
        putStrLn $ ppShow $ hnf $ case b of
            "lazy" -> t' $ read n
            "seq" -> t'' $ read n
    _ -> cycle True mempty
  where
    cycle (pr :: Bool) st = do
        n <- getCommand pr $ message st
        case (n, st) of
            (DownArrow, st@(_, _:_:_)) -> cycle' $ goLeft st
            (UpArrow, st@(_:_, _)) -> cycle' $ goRight st
            (LeftArrow, st@(_, _:_:_)) -> cycle' $ iterate goLeft st !! 100
            (RightArrow, st@(_:_, _)) -> cycle' $ iterate goRight st !! 100
            (IntArg n, _) -> cycle' ([], stepList $ t' n)
            (ProgramChange, _) -> cycle' ([], stepList $ test) --t'' 0)
            _ ->  cycle False st

    cycle' st@(h, (_, x): _) = do
        putStr $ "\n" ++ ppShow x
        cycle True st
    cycle' st = cycle True st

    goLeft (xs, y: ys) = (y: xs, ys)
    goLeft xs = xs
    goRight (x: xs, ys) = (xs, x: ys)
    goRight xs = xs

    message ([], []) = ""
    message (h, x) = show (length h) ++ " " ++ f x
        where
          f ((msg,_):_) = msg
          f _ = ""

mread :: Read a => String -> Maybe a
mread s = case reads s of
    [(a, "")] -> Just a
    _ -> Nothing


