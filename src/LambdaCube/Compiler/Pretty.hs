{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
module LambdaCube.Compiler.Pretty
    ( module LambdaCube.Compiler.Pretty
    ) where

import Data.Monoid
import Data.String
--import qualified Data.Set as Set
--import qualified Data.Map as Map
import Control.Monad.Reader
import Control.Monad.State
import Control.Arrow hiding ((<+>))
--import Debug.Trace

import qualified Text.PrettyPrint.ANSI.Leijen as P

import LambdaCube.Compiler.Utils

type Doc = NDoc
hsep [] = mempty
hsep xs = foldr1 (<+>) xs
vcat [] = mempty
vcat xs = foldr1 (<$$>) xs
text = DAtom

--------------------------------------------------------------------------------

class PShow a where
    pShow :: a -> NDoc

ppShow = show . pShow

--------------------------------------------------------------------------------

instance PShow Bool where
    pShow b = if b then "True" else "False"

instance (PShow a, PShow b) => PShow (a, b) where
    pShow (a, b) = tupled [pShow a, pShow b]

instance (PShow a, PShow b, PShow c) => PShow (a, b, c) where
    pShow (a, b, c) = tupled [pShow a, pShow b, pShow c]

instance PShow a => PShow [a] where
--    pShow = P.brackets . P.sep . P.punctuate P.comma . map pShow  -- TODO

instance PShow a => PShow (Maybe a) where
    pShow = maybe "Nothing" (("Just" `DApp`) . pShow)

--instance PShow a => PShow (Set a) where
--    pShow = pShow . Set.toList

--instance (PShow s, PShow a) => PShow (Map s a) where
--    pShow = braces . vcat . map (\(k, t) -> pShow k <> P.colon <+> pShow t) . Map.toList

instance (PShow a, PShow b) => PShow (Either a b) where
   pShow = either (("Left" `DApp`) . pShow) (("Right" `DApp`) . pShow)

instance PShow NDoc where
    pShow x = x

instance PShow Int     where pShow = fromString . show
instance PShow Integer where pShow = fromString . show
instance PShow Double  where pShow = fromString . show
instance PShow Char    where pShow = fromString . show
instance PShow ()      where pShow _ = "()"

---------------------------------------------------------------------------------
-- TODO: remove

pattern ESC a b <- (splitESC -> Just (a, b)) where ESC a b | 'm' `notElem` a = "\ESC[" ++ a ++ "m" ++ b

splitESC ('\ESC':'[': (span (/='m') -> (a, c: b))) | c == 'm' = Just (a, b)
splitESC _ = Nothing

removeEscs :: String -> String
removeEscs (ESC _ cs) = removeEscs cs
removeEscs (c: cs) = c: removeEscs cs
removeEscs [] = []

-------------------------------------------------------------------------------- fixity

data FixityDir = Infix | InfixL | InfixR
    deriving (Eq, Show)

data Fixity = Fixity !FixityDir !Int
    deriving (Eq, Show)

-------------------------------------------------------------------------------- doc data type

data NDoc
    = DAtom String
    | DOp Fixity NDoc String NDoc
    | DPar String NDoc String
    | DLam String [NDoc] String NDoc
    | DVar Int
    | DFreshName Bool{-False: dummy-} NDoc
    | DUp Int NDoc
    | DDoc (DocOp NDoc) --Color Color NDoc
    -- add wl-pprint combinators as necessary here
    deriving (Eq)

data DocOp a
    = DOColor Color a
    | DOHSep a a
    | DOHCat a a
    | DOSoftSep a a
    | DOVCat a a
    | DONest Int a
    | DOTupled [a]
    deriving (Eq, Functor, Foldable, Traversable)

pattern DColor c a = DDoc (DOColor c a)

a <+> b = DDoc $ DOHSep a b
a </> b = DDoc $ DOSoftSep a b
a <$$> b = DDoc $ DOVCat a b
nest n = DDoc . DONest n
tupled = DDoc . DOTupled

instance Monoid NDoc where
    mempty = fromString ""
    a `mappend` b = DDoc $ DOHCat a b

pattern DParen x = DPar "(" x ")"
pattern DBrace x = DPar "{" x "}"
pattern DArr x y = DOp (Fixity InfixR (-1)) x "->" y
pattern DAnn x y = DOp (Fixity InfixR (-3)) x ":" y

braces = DBrace
parens = DParen

data Color = Green | Blue | Underlined
    deriving (Eq)

inGreen' = DColor Green
inBlue' = DColor Blue
epar = DColor Underlined

strip = \case
    DColor _ x     -> strip x
    DUp _ x        -> strip x
    DFreshName _ x -> strip x
    x              -> x

simple x = case strip x of
    DAtom{} -> True
    DVar{} -> True
    DPar{} -> True
    _ -> False

renderDocX :: NDoc -> P.Doc
renderDocX = render . addPar (-10) . flip runReader [] . flip evalStateT (flip (:) <$> iterate ('\'':) "" <*> ['a'..'z']) . showVars
  where
    showVars x = case x of
        DAtom s -> pure x
        DDoc d -> DDoc <$> traverse showVars d
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
        DDoc d -> DDoc $ addPar (-10) <$> d
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
        DDoc d -> case render <$> d of
            DOColor c x -> colorFun c x
            DOHSep a b  -> a P.<+> b
            DOHCat a b  -> a <> b
            DOSoftSep a b -> a P.</> b
            DOVCat a b  -> a P.<$$> b
            DONest n a  -> P.nest n a
            DOTupled a  -> P.tupled a
        DAtom s -> P.text s
        DPar l x r -> P.text l <> render x <> P.text r
        DOp _ x s y -> case s of
            ""  -> render x P.<> render y
            " " -> render x P.<+> render y
            _ | simple x && simple y && s /= "," -> render x <> P.text s <> render y
              | otherwise -> (render x <++> s) P.<+> render y
        DLam lam vs arr e -> P.text lam <> P.hsep (render <$> vs) P.<+> P.text arr P.<+> render e
      where
        x <++> "," = x <> P.text ","
        x <++> s = x P.<+> P.text s

        colorFun = \case
            Green       -> P.dullgreen
            Blue        -> P.dullblue
            Underlined  -> P.underline
        
instance Show NDoc where
    show = show . renderDocX

showDoc_ :: NDoc -> P.Doc
showDoc_ = renderDocX

shVar = DVar

shLet i a b = shLam' (shLet' (inBlue' $ shVar i) $ DUp i a) (DUp i b)
shLet_ a b = DFreshName True $ shLam' (shLet' (shVar 0) $ DUp 0 a) b

-----------------------------------------

instance IsString NDoc where
    fromString = DAtom

shAtom = DAtom

shTuple [] = "()"
shTuple [x] = DParen $ DParen x
shTuple xs = DParen $ foldr1 (\x y -> DOp (Fixity InfixR (-20)) x "," y) xs

shAnn _ True x y | strip y == "Type" = x
shAnn s _ x y = DOp (Fixity InfixR (-3)) x s y

pattern DApp x y = DOp (Fixity InfixL 10) x " " y

shArr = DArr

shCstr x y = DOp (Fixity Infix (-2)) x "~" y

shLet' x y = DOp (Fixity Infix (-4)) x ":=" y

getFN (DFreshName True a) = first (+1) $ getFN a
getFN a = (0, a)

shLam' x (getFN -> (i, DLam "\\" xs "->" y)) = iterateN i (DFreshName True) $ DLam "\\" (iterateN i (DUp 0) x: xs) "->" y
shLam' x y = DLam "\\" [x] "->" y


