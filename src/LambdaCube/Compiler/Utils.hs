{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module LambdaCube.Compiler.Utils where

import qualified Data.IntSet as IS
import qualified Data.Text as T
import qualified Text.Show.Pretty as PP
--import Control.Monad.Catch
import Control.Monad.Except
import Control.Monad.RWS
import System.Directory
import qualified Data.Text.IO as TIO
import qualified Text.Megaparsec as P
import qualified Text.Megaparsec.Prim as P

------------------------------------------------------- general functions

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip (<$>)

dropIndex :: Int -> [a] -> [a]
dropIndex i xs = take i xs ++ drop (i+1) xs

iterateN :: Int -> (a -> a) -> a -> a
iterateN n f e = iterate f e !! n

foldlrev :: Foldable t => (a -> b -> a) -> a -> t b -> a
foldlrev f = foldr (flip f)

------------------------------------------------------- Void data type

data Void

instance Eq Void where x == y = elimVoid x

elimVoid :: Void -> a
elimVoid v = case v of

------------------------------------------------------- supplementary data wrapper

-- supplementary data: data with no semantic relevance
newtype SData a = SData a

instance Eq (SData a) where _ == _ = True
instance Ord (SData a) where _ `compare` _ = EQ

------------------------------------------------------- strongly connected component calculation

type Children k = k -> [k]

data Task a = Return a | Visit a

scc :: forall k . (k -> Int) -> Children k -> Children k -> [k]{-roots-} -> [[k]]
scc key children revChildren
    = filter (not . null) . uncurry (revMapWalk revChildren) . revPostOrderWalk children
  where
    revPostOrderWalk :: Children k -> [k] -> (IS.IntSet, [k])
    revPostOrderWalk children = collect IS.empty [] . map Visit where

        collect :: IS.IntSet -> [k] -> [Task k] -> (IS.IntSet, [k])
        collect s acc [] = (s, acc)
        collect s acc (Return h: t) = collect s (h: acc) t
        collect s acc (Visit h: t)
            | key h `IS.member` s = collect s acc t
            | otherwise = collect (IS.insert (key h) s) acc $ map Visit (children h) ++ Return h: t

    revMapWalk :: Children k -> IS.IntSet -> [k] -> [[k]]
    revMapWalk children = f []
     where
        f :: [[k]] -> IS.IntSet -> [k] -> [[k]]
        f acc s [] = acc
        f acc s (h:t) = f (c: acc) s' t
            where (s', c) = collect s [] [h]

        collect :: IS.IntSet -> [k] -> [k] -> (IS.IntSet, [k])
        collect s acc [] = (s, acc)
        collect s acc (h:t)
            | not (key h `IS.member` s) = collect s acc t
            | otherwise = collect (IS.delete (key h) s) (h: acc) (children h ++ t)

------------------------------------------------------- wrapped pretty show

prettyShowUnlines :: Show a => a -> String
prettyShowUnlines = goPP 0 . PP.ppShow
  where
    goPP :: Int -> String -> String
    goPP _ [] = []
    goPP n ('"':xs) | isMultilineString xs = "\"\"\"\n" ++ indent ++ go xs where
        indent = replicate n ' ' :: String
        go :: String -> String
        go ('\\':'n':xs) = "\n" ++ indent ++ go xs
        go ('\\':c:xs) = '\\':c:go xs
        go ('"':xs) = "\n" ++ indent ++ "\"\"\"" ++ goPP n xs
        go (x:xs) = x : go xs
    goPP n (x:xs) = x : goPP (if x == '\n' then 0 else n+1) xs

    isMultilineString :: String -> Bool
    isMultilineString ('\\':'n':xs) = True
    isMultilineString ('\\':c:xs) = isMultilineString xs
    isMultilineString ('"':xs) = False
    isMultilineString (x:xs) = isMultilineString xs
    isMultilineString [] = False

------------------------------------------------------- file handling

readFileStrict :: FilePath -> IO String
readFileStrict = fmap T.unpack . TIO.readFile

readFileIfExists :: FilePath -> IO (Maybe (IO String))
readFileIfExists fname = do
    b <- doesFileExist fname
    return $ if b then Just $ readFileStrict fname else Nothing

------------------------------------------------------- missing instances
{-
instance MonadMask m => MonadMask (ExceptT e m) where
    mask f = ExceptT $ mask $ \u -> runExceptT $ f (mapExceptT u)
    uninterruptibleMask = error "not implemented: uninterruptibleMask for ExcpetT"
-}
