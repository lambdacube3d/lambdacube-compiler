{-
Pattern match compilation + exhaustiveness check

Ideas came mainly from the following sources:

-   "GADTs meet their match"
-   "The implementation of functional programming languages", Chapter 5, "Efficient compilation of pattern matching"
-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Either
import Control.Arrow ((***))
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Writer hiding (Alt)
import Text.Show.Pretty (ppShow)

-------------------------------------------------------------------------------- Name generator monad

type NewName = StateT Int

newName :: Monad m => NewName m String
newName = state $ \i -> ("v" ++ show i, i + 1)

-------------------------------------------------------------------------------- data types

type Loc = Int  -- location info
type VarName = String
type ConName = String

------------------------------- source data structure

{-
   match  a b c  with
      (x:y) (f x -> Just ((>3) -> True)) v@(_:_)@v'@(g  -> True)
        | x > 4 -> ...
        | Just (z: v) <- h y, Nothing <- h' z, h'' v -> ...
        | ...
       where
        ...
      ...
-}


{-
    match a with
        x: y | [] <- a -> ... x ... y ... z ... v ...
-}


data Match = Match [VarName] [Clause]   -- match expression (generalized case expression)
data Clause = Clause [ParPat] (WhereBlock [([PatGuard], Exp)])
data PatGuard = PatGuard ParPat Exp
data WhereBlock a = WhereBlock [(VarName, Exp)] a
    deriving (Show, Eq)

type ParPat = [Pat]     -- parallel patterns like  v@(f -> [])@(Just x)

data Pat
    = PVar VarName
    | Con ConName [ParPat]
    | ViewPat Exp ParPat
  deriving Show

------------------------------- intermediate data structures

data GuardTree
    = GuardNode Loc Exp ConName [ParPat] (WhereBlock [GuardTree])
    | GuardLeaf Loc Exp
  deriving Show

type CasesInfo = [(Exp, Either (String, [String]) (Exp, Exp))]
type InfoWriter = Writer ([Loc], [Loc], [CasesInfo])

------------------------------- target data structures

data Exp
    = IdExp (Map VarName Exp) Loc       -- arbitrary expression
    | Undefined
    | Otherwise
    | Case Exp [Alt]
    | Var VarName
    | ViewApp Exp Exp
    | Let (WhereBlock Exp)
  deriving (Show, Eq)

data Alt = Alt ConName [VarName] Exp
  deriving (Show, Eq)

getId = \case
    IdExp _ i -> i

data Info
    = Uncovered [ParPat]
    | Inaccessible Int
    | Removable Int
    | Shared Int Int
  deriving Show

-------------------------------------------------------------------------------- conversions between data structures

matchToGuardTree :: Match -> [GuardTree]
matchToGuardTree (Match [] _) = error "matchToGuardTree"
matchToGuardTree (Match vs cs)
    = cs >>= \(Clause ps (WhereBlock wh rhs)) -> helper (getId' rhs) (zip3 (map Var vs) ps $ ff ps wh) (rhs >>= uncurry h)
  where
    h [] e = [GuardLeaf (getId e) e]
    h (PatGuard p x: gs) e = helper (getId e) [(x, p, [])] $ h gs e

    getId' ((_, e): _) = getId e    -- TODO

helper :: Loc -> [(Exp, [Pat], [(VarName, Exp)])] -> [GuardTree] -> [GuardTree]
helper _ [] l = l
helper i ((v, ws, wh): vs) e = case ws of
    [] -> helper i vs e
    w: ws -> case w of
        PVar x -> helper i (map (\(a,b,c) -> (a, subst x v b, map (id *** subst x v) c)) $ (v, ws, wh): vs) $ subst x v e
        ViewPat f p -> helper i ((ViewApp f v, p, []): (v, ws, wh): vs) e
        Con s ps' -> [GuardNode i v s ps' $ WhereBlock wh $ helper i ((v, ws, wh): vs) e]

guardTreeToCases :: CasesInfo -> [GuardTree] -> NewName InfoWriter Exp
guardTreeToCases seq = \case
    [] -> tell ([], [], [seq]) >> return Undefined
    GuardLeaf i e: _ -> tell ([i], [], []) >> return e
    cs@(GuardNode i f s _ _: _) -> do
      tell ([], [i], [])
      Case f <$> sequence
        [ do
            ns <- replicateM cv newName
            fmap (Alt cn ns) $ guardTreeToCases ((f, Left (cn, ns)): appAdd f seq) $ cs >>= filterGuardTree f cn ns
        | (cn, cv) <- fromJust $ find ((s `elem`) . map fst) contable
        ]
  where
    appAdd (ViewApp f v) x = (v, Right (f, ViewApp f v)): appAdd v x
    appAdd _ x = x

filterGuardTree :: Exp -> ConName -> [VarName] -> GuardTree -> [GuardTree]
filterGuardTree f s ns = \case
    GuardLeaf i e -> [GuardLeaf i e]
    GuardNode i f' s' ps (WhereBlock wh gs)
        | f /= f'   -> [GuardNode i f' s' ps $ WhereBlock wh $ gs >>= filterGuardTree f s ns]
        | s == s'   -> helper i (zip3 (map Var ns) ps $ ff ps wh) gs >>= filterGuardTree f s ns
        | otherwise -> []

-- TODO
ff [] _ = []
ff l w = replicate (length l - 1) [] ++ [w]

mkInfo :: Int -> InfoWriter ([VarName], Exp) -> (Exp, [Info])
mkInfo i (runWriter -> ((ns, e'), (is, nub -> js, us)))
    = ( e'
      , [ (if n > 1 then Shared n else if j `elem` js then Inaccessible else Removable) j
        | j <- [1..i], let n = length $ filter (==j) is, n /= 1
        ] ++ map (Uncovered . mkPat (map Var ns)) us
      )
  where
    mkPat :: [Exp] -> CasesInfo -> [ParPat]
    mkPat ns ls = map f ns
      where
        f v' = mconcat [either (\(s, vs) -> [Con s $ map (f . Var) vs]) (\(s, v) -> [ViewPat s $ f v]) ps | (v, ps) <- ls, v == v']

tester :: [[ParPat]] -> IO ()
tester cs@(ps: _) = putStrLn . ppShow . mkInfo (length cs) . flip evalStateT 1 $ do
    vs <- replicateM (length ps) newName
    let gs = matchToGuardTree (Match vs $ zipWith (\a b -> Clause a $ WhereBlock [] b) cs $ map ((:[]) . (,) [] . IdExp mempty) [1..])
    (,) vs <$> guardTreeToCases [] gs

-------------------------------------------------------------------------------- substitution

class Subst a where subst :: VarName -> Exp -> a -> a

substs :: (Subst b) => [(VarName, Exp)] -> b -> b
substs rs g = foldr (uncurry subst) g rs

instance Subst a => Subst [a] where subst a b = map (subst a b)
instance (Subst a, Subst b) => Subst (a, b) where subst a b (c, d) = (subst a b c, subst a b d)
instance Subst Exp where
  subst a b = \case
    Var v | v == a -> b
          | otherwise -> Var v
    ViewApp f x -> ViewApp (subst a b f) (subst a b x)
    IdExp m i -> IdExp (Map.insert a b $ subst a b <$> m) i
instance Subst Pat where
    subst as v = \case
        Con s ps -> Con s $ map (subst as v) ps
        ViewPat f p -> ViewPat (subst as v f) $ subst as v p
        PVar x -> PVar x
instance Subst GuardTree where
    subst a b = \case
        GuardNode i e y z x -> GuardNode i (subst a b e) y (subst a b z) $ subst a b x
        GuardLeaf i e -> GuardLeaf i (subst a b e)
instance Subst PatGuard where
    subst a b (PatGuard p e) = PatGuard (subst a b p) (subst a b e)
instance Subst a => Subst (WhereBlock a) where
    subst a b (WhereBlock l e) = WhereBlock (map (id *** subst a b) l) $ subst a b e

-------------------------------------------------------------------------------- constructors

contable =
    [ ["Nil" # 0, "Cons" # 2]
    , ["False" # 0, "True" # 0]
    , ["Nothing" # 0, "Just" # 1]
    ] where (#) = (,)
 
pattern Nil = Con' "Nil" []
pattern Cons a b = Con' "Cons" [a, b]
pattern T = Con' "True" []
pattern F = Con' "False" []
pattern No = Con' "Nothing" []
pattern Ju a = Con' "Just" [a]

pattern W = []
pattern V v = [PVar v]
pattern Con' s ps = [Con s ps]
pattern Vi f p = [ViewPat (Var f) p]

pattern Guard e = PatGuard T e

-------------------------------------------------------------------------------- test cases

diagonal_test = tester
    [ [W, T, F]
    , [F, W, T]
    , [T, F, W]
    ]
seq_test = tester
    [ [W, F]
    , [T, F]
    , [W, W]
    ]
reverseTwo_test = tester
    [ [Cons (V "x") (Cons (V "y") Nil)]
    , [V "xs"]
    ]
xor_test = tester
    [ [V "x", F]
    , [F, T]
    , [T, T]
    ]
unwieldy_test = tester
    [ [Nil, Nil]
    , [V "xs", V "ys"]
    ]
last_test = tester
    [ [Cons (V "x") Nil]
    , [Cons (V "y") (V "xs")]
    ]
last_test' = tester
    [ [Cons (V "x") Nil]
    , [Cons (V "y") (Cons (V "x") (V "xs"))]
    ]
zipWith_test = tester
    [ [V "g", Nil, W]
    , [V "f", W, Nil]
    , [V "f", Cons (V "x") (V "xs"), Cons (V "y") (V "ys")]
    ]
zipWith_test' = tester
    [ [V "f", Cons (V "x") (V "xs"), Cons (V "y") (V "ys")]
    , [V "g", W, W]
    ]
zipWith_test'' = tester
    [ [V "f", Cons (V "x") (V "xs"), Cons (V "y") (V "ys")]
    , [V "g", Nil, Nil]
    ]
uncovered_test = tester
    [ [Cons (V "x") $ Cons (V "y") $ Cons (V "z") (V "v")] ]
view_test = tester
    [ [Vi "f" (Cons (V "y") (V "s"))] ]
view_test' = tester
    [ [Vi "f" (Cons (Vi "g" $ Ju (V "y")) (V "s"))]
    , [Vi "h" T]
    ]
view_test'' = tester
    [ [V "x", [ViewPat (ViewApp (Var "f") (Var "x")) (T `mappend` V "q")] `mappend` V "z"] ]       -- TODO: prevent V "q" expansion
guard_test = tester
    [ [V "x" `mappend` Vi "graterThan5" T] 
    , [V "x"]
    ]


