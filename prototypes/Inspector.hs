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

data DSt = DSt [(StepTag, Int, MSt)]

getFinal' (DSt (x: _)) = x
getFinal x = case getFinal' x of (a, b, c) -> (a, c)

goUp (DSt [_]) = Nothing
goUp (DSt xs) = case xs of
    (Begin{}, _, _): xs -> f 0 xs
    xs -> f 0 xs
  where
    f n ((End{}, _, _): xs@(_: _)) = f (n+1) xs
    f 0 xs@((Begin{}, _, _): _) = Just $ DSt xs
    f n ((Begin{}, _, _): xs@(_: _)) = f (n-1) xs
    f n (_: xs@(_: _)) = f n xs
    f n [x] = Just $ DSt [x]
    f _ _ = Nothing

steps' n = steps Nothing (\a b -> Just (a, n + 1, b))

limit = 2000

goDown st@(DSt xs) | (_, n, s) <- getFinal' st = case steps' n s of
    Nothing -> Nothing
    Just x -> Just $ DSt $ x: reduce n xs
  where
    reduce n ((End{}, _, _): (Begin{}, _, _): xs@((_, n', _): _)) | n - n' < limit = reduce n xs
    reduce n xs@((Begin{}, n', _): _) = xs
    reduce n xs@((End{}, n', _): _) = xs
    reduce n (_: xs@((_, n', _): _)) | n - n' < limit = reduce n xs
    reduce _ xs = xs


inHNF' = inHNF . snd . getFinal

goRight (goDown -> Just st@(getFinal -> (Begin{}, _))) = f 0 st
  where
    g st | inHNF' st = Just st
    g (goRight -> Just st) = h st
    g st = h st

    h (goDown -> Just st@(getFinal -> (Step{}, _))) = h st
    h st = Just st

    f n st_@(goDown -> Just st) = case getFinal st of
        (m@End{}, s) | n == 0 -> g st
        (End{}, s) -> f (n-1) st
        (Begin{}, s) -> f (n+1) st
        (_, s) -> f n st
goRight _ = Nothing

goLeft st@(getFinal' -> (_, n, _)) = f <$> goLeft' st
  where
    f st@(getFinal' -> (_, n', _)) = iterate (fromJust . goDown) st !! (n - n' - 1)

goLeft' (DSt (_: y@(_:_))) = Just $ DSt y
goLeft' _ = Nothing

current :: DSt -> MSt
current = snd . getFinal

jumpTo n st@(getFinal' -> (_, n', _))
    | n > n' = f (n - n' - 1) <$> goDown st
    | n < n' = (\st -> fromMaybe st $ jumpTo n st) <$> goUp st
  where
    f 0 st = st
    f n st = maybe st (f $ n - 1) $ goDown st
jumpTo _ _ = Nothing

message :: DSt -> String
--message (DSt xs) = show [(n, m) | (m, n, _) <- xs]
message (getFinal' -> (m, n, _)) = show n ++ " " ++ show m

stepList (initSt -> st) = DSt [(Begin "start", 0, st)]

data Command = UpArrow | DownArrow | LeftArrow | RightArrow
    | IntArg Int | Jump Int | ProgramChange | ViewChange
    deriving (Eq, Show)

type MSt' = (String, MSt)

data St = St Bool [DSt] DSt

getCommand pr msg = do
  putStr $ (if pr then "\n" else "\CR") ++ "-------------- " ++ msg ++ " --------> "
  getChar >>= \case
    '\ESC' -> getChar >>= \case
     '[' -> getChar >>= \case
      'A' -> c 4 >> ret UpArrow
      'B' -> c 4 >> ret DownArrow
      'C' -> c 4 >> ret RightArrow
      'D' -> c 4 >> ret LeftArrow
      c -> clear c
     c -> clear c
    d | '0' <= d && d <= '9' -> readI (ret . IntArg) [d]
    'n' -> ret ProgramChange
    'j' -> readI (ret . Jump) ['0']
    'v' -> ret ViewChange
    c -> clear c
  where
    ret a = {-putStr ("  --  " ++ show a) >> -} return a
    readI f ds = getChar >>= \case
        d | '0' <= d && d <= '9' -> readI f $ d: ds
        '\n' -> c 1 >> f (read $ reverse ds)
        c -> clear c
    clear _ = getCommand True msg
    c n = replicateM n $ putChar '\b'

programs :: [DSt]
programs = cycle $ map stepList
    [ iterate (id_ `App`) id_ !! 20
    , iterate (`App` id_) id_ !! 20
    , iterate (\x -> x `App` x) id_ !! 5
    , twiceTest 2
    , twiceTest 3
    , twiceTest2
    , t' 20
    , t'' 20
    ]

main = do
  hSetBuffering stdin NoBuffering
  hSetBuffering stdout NoBuffering
  getArgs >>= \case
    ["twice"] -> pPrint $ hnf $ twiceTest 3
    ["twice2"] -> pPrint $ hnf twiceTest2
    [b, n] ->
        putStrLn $ ppShow $ hnf $ case b of
            "lazy" -> t' $ read n
            "seq" -> t'' $ read n
    _ -> cycle_ True $ St False programs $ stepList test

main' x = cycle' $ St False programs $ stepList x

cycle' st@(St vi ps (current -> x)) = do
    putStr $ "\n" ++ show (viewShow vi x)
    cycle_ True st
--cycle' st = cycle_ True st

cycle_ (pr :: Bool) s@(St vi ps st) = do
    n <- getCommand pr $ message st
    case (n, st) of
        (DownArrow, goDown -> Just st) -> cycle' $ f s $ const st
        (UpArrow, goUp -> Just st) -> cycle' $ f s $ const st
        (LeftArrow, goLeft -> Just st) -> cycle' $ f s $ const st
        (RightArrow, goRight -> Just st) -> cycle' $ f s $ const st
        (IntArg n, _) -> cycle' $ f s $ const $ stepList $ t' n
        (Jump n, jumpTo n -> Just st) -> cycle' $ f s $ const st
        (ProgramChange, _) -> cycle' $ St vi (tail ps) $ head ps
        (ViewChange, _) -> cycle' $ St (not vi) ps st
        _ ->  cycle_ False s
  where
    f (St a ps b) g = St a ps (g b)

mread :: Read a => String -> Maybe a
mread s = case reads s of
    [(a, "")] -> Just a
    _ -> Nothing


