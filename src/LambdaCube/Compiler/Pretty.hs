{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
module LambdaCube.Compiler.Pretty
    ( module LambdaCube.Compiler.Pretty
    , Doc
    , (<+>), (</>), (<$$>)
    , hsep, hcat, vcat
    , punctuate
    , tupled, braces, parens
    , text
    , nest
    ) where

import Data.String
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Arrow hiding ((<+>))
import Debug.Trace

import Text.PrettyPrint.Leijen hiding ((<$>))

import LambdaCube.Compiler.Utils

--------------------------------------------------------------------------------

instance IsString Doc where fromString = text

instance Monoid Doc where
    mempty = empty
    mappend = (<>)

class PShow a where
    pShowPrec :: Int -> a -> Doc

pShow = pShowPrec (-2)
ppShow = show . pShow

ppShow' = show


{-
prec 0: no outer parens needed
prec 10: argument of a function


f x (g y)


-}

--------------------------------------------------------------------------------

pParens p x
    | p = tupled [x]
    | otherwise = x

pOp i j k sep p a b = pParens (p >= i) $ pShowPrec j a <+> sep <+> pShowPrec k b
pOp' i j k sep p a b = pParens (p >= i) $ pShowPrec j a </> sep <+> pShowPrec k b

pInfixl i = pOp i (i-1) i
pInfixr i = pOp i i (i-1)
pInfixr' i = pOp' i i (i-1)
pInfix  i = pOp i i i

pTyApp = pInfixl 10 "@"
pApps p x [] = pShowPrec p x
pApps p x xs = pParens (p > 9) $ hsep $ pShowPrec 9 x: map (pShowPrec 10) xs
pApp p a b = pApps p a [b]

showRecord = braces . hsep . punctuate (pShow ',') . map (\(a, b) -> pShow a <> ":" <+> pShow b)

--------------------------------------------------------------------------------

instance PShow Bool where
    pShowPrec p b = if b then "True" else "False"

instance (PShow a, PShow b) => PShow (a, b) where
    pShowPrec p (a, b) = tupled [pShow a, pShow b]

instance (PShow a, PShow b, PShow c) => PShow (a, b, c) where
    pShowPrec p (a, b, c) = tupled [pShow a, pShow b, pShow c]

instance PShow a => PShow [a] where
    pShowPrec p = brackets . sep . punctuate comma . map pShow

instance PShow a => PShow (Maybe a) where
    pShowPrec p = \case
        Nothing -> "Nothing"
        Just x -> "Just" <+> pShow x

instance PShow a => PShow (Set a) where
    pShowPrec p = pShowPrec p . Set.toList

instance (PShow s, PShow a) => PShow (Map s a) where
    pShowPrec p = braces . vcat . map (\(k, t) -> pShow k <> colon <+> pShow t) . Map.toList

instance (PShow a, PShow b) => PShow (Either a b) where
    pShowPrec p = either (("Left" <+>) . pShow) (("Right" <+>) . pShow)

instance PShow Doc where
    pShowPrec p x = x

instance PShow Int     where pShowPrec _ = int
instance PShow Integer where pShowPrec _ = integer
instance PShow Double  where pShowPrec _ = double
instance PShow Char    where pShowPrec _ = char
instance PShow ()      where pShowPrec _ _ = "()"


-------------------------------------------------------------------------------- ANSI terminal colors

pattern ESC a b <- (splitESC -> Just (a, b)) where ESC a b | 'm' `notElem` a = "\ESC[" ++ a ++ "m" ++ b

splitESC ('\ESC':'[': (span (/='m') -> (a, c: b))) | c == 'm' = Just (a, b)
splitESC _ = Nothing

withEsc i s = ESC (show i) $ s ++ ESC "" ""

inGreen = withEsc 32    -- TODO
inBlue = withEsc 34
inRed = withEsc 31
underlined = withEsc 47

removeEscs :: String -> String
removeEscs (ESC _ cs) = removeEscs cs
removeEscs (c: cs) = c: removeEscs cs
removeEscs [] = []

correctEscs :: String -> String
correctEscs = (++ "\ESC[K") . f ["39","49"] where
    f acc (ESC i@(_:_) cs) = esc (i /= head acc) i $ f (i: acc) cs
    f (a: acc) (ESC "" cs) = esc (a /= head acc) (compOld (cType a) acc) $ f acc cs
    f acc (c: cs) = c: f acc cs
    f acc [] = []

    esc b i = if b then ESC i else id
    compOld x xs = head $ filter ((== x) . cType) xs

    cType n
        | "30" <= n && n <= "39" = 0
        | "40" <= n && n <= "49" = 1
        | otherwise = 2

putStrLn_ = putStrLn . correctEscs
error_ = error . correctEscs
trace_ = trace . correctEscs
throwError_ = throwError . correctEscs


-------------------------------------------------------------------------------- fixity

data FixityDir = Infix | InfixL | InfixR
    deriving (Eq, Show)

data Fixity = Fixity !FixityDir !Int
    deriving (Eq, Show)

-------------------------------------------------------------------------------- pretty print

data NDoc
    = DAtom String
    | DOp Fixity NDoc String NDoc
    | DPar String NDoc String
    | DLam String [NDoc] String NDoc
    | DVar Int
    | DFreshName Bool{-False: dummy-} NDoc
    | DUp Int NDoc
    | DColor Color NDoc
    -- add wl-pprint combinators as necessary here
    deriving (Eq)

pattern DParen x = DPar "(" x ")"
pattern DBrace x = DPar "{" x "}"
pattern DArr x y = DOp (Fixity InfixR (-1)) x "->" y
pattern DAnn x y = DOp (Fixity InfixR (-3)) x ":" y

data Color = Green | Blue | Underlined
    deriving (Eq)

inGreen' = DColor Green
inBlue' = DColor Blue
epar = DColor Underlined

strip = \case
    DColor _ x     -> strip x
    DUp _ x        -> strip x
    DFreshName _ x -> strip x
    x -> x

simple x = case strip x of
    DAtom{} -> True
    DVar{} -> True
    DPar{} -> True
    _ -> False

renderDocX :: NDoc -> Doc
renderDocX = render . addPar (-10) . flip runReader [] . flip evalStateT (flip (:) <$> iterate ('\'':) "" <*> ['a'..'z']) . showVars
  where
    showVars x = case x of
        DAtom s -> pure x
        DColor c x -> DColor c <$> showVars x
        DPar l x r -> DPar l <$> showVars x <*> pure r
        DOp pr x s y -> DOp pr <$> showVars x <*> pure s <*> showVars y
        DVar i -> asks $ DAtom . lookupVarName i
        DFreshName True x -> gets head >>= \n -> modify tail >> local (n:) (showVars x)
        DFreshName False x -> local ("_":) $ showVars x
        DUp i x -> local (dropNth i) $ showVars x
        DLam lam vs arr e -> DLam lam <$> (mapM showVars vs) <*> pure arr <*> showVars e
      where
        lookupVarName i xs | i < length xs = xs !! i
        lookupVarName i _ = ((\s n -> n: '_': s) <$> iterate ('\'':) "" <*> ['a'..'z']) !! i

    addPar :: Int -> NDoc -> NDoc
    addPar pr x = case x of
        DAtom{} -> x
        DColor c x -> DColor c $ addPar pr x
        DPar l x r -> DPar l (addPar (-20) x) r
        DOp pr' x s y -> paren $ DOp pr' (addPar (precL pr') x) s (addPar (precR pr') y)
        DLam lam vs arr e -> paren $ DLam lam (addPar 10 <$> vs) arr (addPar (-10) e)
      where
        paren d
            | protect x = DParen d
            | otherwise = d
          where
            protect x = case x of
                DAtom{} -> False
                DPar{} -> False
                DOp (Fixity _ pr') _ _ _ -> pr' < pr
                DLam{}                   -> -10 < pr 

        precL (Fixity Infix  i) = i+1
        precL (Fixity InfixL i) = i
        precL (Fixity InfixR i) = i+1
        precR (Fixity Infix  i) = i+1
        precR (Fixity InfixL i) = i+1
        precR (Fixity InfixR i) = i

    render x = case x of
        DColor Green x -> text $ inGreen $ show $ render x -- TODO
        DColor Blue x -> text $ inBlue $ show $ render x -- TODO
        DColor Underlined x -> text $ underlined $ show $ render x -- TODO
        DAtom s -> text s
        DPar l x r -> text l <> render x <> text r
        DOp _ x s y -> case s of
            "" -> render x <+> render y
            _ | simple x && simple y && s /= "," -> render x <> text s <> render y
              | otherwise -> (render x <++> s) <+> render y
        DLam lam vs arr e -> text lam <> hsep (render <$> vs) <+> text arr <+> render e
      where
        x <++> "," = x <> text ","
        x <++> s = x <+> text s
        
showDoc :: NDoc -> String
showDoc = show . renderDocX

showDoc_ :: NDoc -> Doc
showDoc_ = renderDocX

shVar = DVar

shLet i a b = shLam' (cpar . shLet' (inBlue' $ shVar i) $ DUp i a) (DUp i b)
shLet_ a b = DFreshName True $ shLam' (cpar . shLet' (shVar 0) $ DUp 0 a) b

-----------------------------------------

shAtom = DAtom

shTuple [] = DAtom "()"
shTuple [x] = DParen $ DParen x
shTuple xs = DParen $ foldr1 (\x y -> DOp (Fixity InfixR (-20)) x "," y) xs

shAnn _ True x y | strip y == DAtom "Type" = x
shAnn s _ x y = DOp (Fixity InfixR (-3)) x s y

shApp _ x y = DOp (Fixity InfixL 10) x "" y

shArr = DArr

shCstr x y = DOp (Fixity Infix (-2)) x "~" y

shLet' x y = DOp (Fixity Infix (-4)) x ":=" y

getFN (DFreshName True a) = first (+1) $ getFN a
getFN a = (0, a)

shLam' x (getFN -> (i, DLam "\\" xs "->" y)) = iterateN i (DFreshName True) $ DLam "\\" (iterateN i (DUp 0) x: xs) "->" y
shLam' x y = DLam "\\" [x] "->" y

cpar s | simple s = s
cpar s = DParen s


