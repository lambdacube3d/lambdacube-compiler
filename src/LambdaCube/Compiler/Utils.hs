{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
module LambdaCube.Compiler.Utils where

import qualified Data.IntSet as IS

(<&>) = flip (<$>)

dropNth i xs = take i xs ++ drop (i+1) xs
iterateN n f e = iterate f e !! n

unfoldNat z s 0         = z
unfoldNat z s n | n > 0 = s $ unfoldNat z s (n-1)

data Void

instance Show Void where show = elimVoid
instance Eq Void where x == y = elimVoid x

elimVoid :: Void -> a
elimVoid _ = error "impossible"

-- supplementary data: data with no semantic relevance
newtype SData a = SData a

instance Show (SData a) where show _ = "SData"
instance Eq (SData a) where _ == _ = True
instance Ord (SData a) where _ `compare` _ = EQ

------------------------------------------------------------------------ strongly connected component calculation

type Children k = k -> [k]

data Task a = Return a | Visit a

scc :: forall k . (k -> Int) -> Children k -> Children k -> [k]{-roots-} -> [[k]]
scc key children revChildren
    = filter (not . null) . uncurry (revMapWalk revChildren) . revPostOrderWalk children
  where
    revPostOrderWalk :: Children k -> [k] -> (IS.IntSet, [k])
    revPostOrderWalk children = collect IS.empty [] . map Visit where

        collect s acc [] = (s, acc)
        collect s acc (Return h: t) = collect s (h: acc) t
        collect s acc (Visit h: t)
            | key h `IS.member` s = collect s acc t
            | otherwise = collect (IS.insert (key h) s) acc $ map Visit (children h) ++ Return h: t

    revMapWalk :: Children k -> IS.IntSet -> [k] -> [[k]]
    revMapWalk children = f []
     where
        f acc s [] = acc
        f acc s (h:t) = f (c: acc) s' t
            where (s', c) = collect s [] [h]

        collect s acc [] = (s, acc)
        collect s acc (h:t)
            | not (key h `IS.member` s) = collect s acc t
            | otherwise = collect (IS.delete (key h) s) (h: acc) (children h ++ t)



