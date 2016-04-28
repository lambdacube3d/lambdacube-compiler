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

hsep [] = mempty
hsep xs = foldr1 (<+>) xs
vcat [] = mempty
vcat xs = foldr1 (<$$>) xs

--------------------------------------------------------------------------------

class PShow a where
    pShow :: a -> Doc

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

instance PShow Doc where
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

data Fixity
    = Infix  !Int
    | InfixL !Int
    | InfixR !Int
    deriving (Eq, Show)

precedence = \case
    Infix i  -> i
    InfixR i -> i
    InfixL i -> i

-------------------------------------------------------------------------------- doc data type

data Doc
    = DAtom_ Atom
    | DOp Fixity Doc String Doc
    | DVar Int
    | DFreshName Bool{-False: dummy-} Doc
    | DUp Int Doc
    | DDoc (DocOp Doc)
    deriving (Eq)

data Atom
    = AEnd String
    | ACons String Int Doc Atom
    deriving (Eq)

data DocOp a
    = DOColor Color a
    | DOHSep a a
    | DOHCat a a
    | DOSoftSep a a
    | DOVCat a a
    | DONest Int a
    | DOTupled [a]
    -- add wl-pprint combinators as necessary here
    deriving (Eq, Functor, Foldable, Traversable)

interpretDocOp = \case
    DOHSep a b  -> a P.<+> b
    DOHCat a b  -> a <> b
    DOSoftSep a b -> a P.</> b
    DOVCat a b  -> a P.<$$> b
    DONest n a  -> P.nest n a
    DOTupled a  -> P.tupled a
    DOColor c x -> case c of
        Green       -> P.dullgreen x
        Blue        -> P.dullblue  x
        Underlined  -> P.underline x

text = DAtom_ . AEnd
pattern DPar l d r = DAtom_ (ACons l (-20) d (AEnd r))

pattern DColor c a = DDoc (DOColor c a)

a <+> b = DDoc $ DOHSep a b
a </> b = DDoc $ DOSoftSep a b
a <$$> b = DDoc $ DOVCat a b
nest n = DDoc . DONest n
tupled = DDoc . DOTupled

instance Monoid Doc where
    mempty = fromString ""
    a `mappend` b = DDoc $ DOHCat a b

pattern DParen x = DPar "(" x ")"
pattern DBrace x = DPar "{" x "}"
pattern DArr x y = DOp (InfixR (-1)) x "->" y
pattern DAnn x y = DOp (InfixR (-3)) x ":" y
pattern DApp x y = DOp (InfixL 10) x " " y
pattern DGlueR pr x y = DOp (InfixR pr) x " " y

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
    DAtom_{} -> True
    DVar{} -> True
    _ -> False

renderDocX :: Doc -> P.Doc
renderDocX = render . addPar (-10) . flip runReader [] . flip evalStateT (flip (:) <$> iterate ('\'':) "" <*> ['a'..'z']) . showVars
  where
    showVars x = case x of
        DAtom_ s -> DAtom_ <$> showVarA s
        DDoc d -> DDoc <$> traverse showVars d
        DOp pr x s y -> DOp pr <$> showVars x <*> pure s <*> showVars y
        DVar i -> asks $ text . lookupVarName i
        DFreshName True x -> gets head >>= \n -> modify tail >> local (n:) (showVars x)
        DFreshName False x -> local ("_":) $ showVars x
        DUp i x -> local (dropNth i) $ showVars x
      where
        showVarA (AEnd s) = pure $ AEnd s
        showVarA (ACons s i d a) = ACons s i <$> showVars d <*> showVarA a

        lookupVarName i xs | i < length xs = xs !! i
        lookupVarName i _ = ((\s n -> n: '_': s) <$> iterate ('\'':) "" <*> ['a'..'z']) !! i

    addPar :: Int -> Doc -> Doc
    addPar pr x = case x of
        DAtom_ x -> DAtom_ $ addParA x
        DOp pr' x s y -> paren $ DOp pr' (addPar (precL pr') x) s (addPar (precR pr') y)
        DColor c x -> DColor c $ addPar pr x
        DDoc d -> DDoc $ addPar (-10) <$> d
      where
        addParA (AEnd s) = AEnd s
        addParA (ACons s i d a) = ACons s i (addPar i d) $ addParA a

        paren = if protect then DParen else id
          where
            protect = case x of
                DOp f _ _ _ -> precedence f < pr
                _ -> False

        precL (InfixL i) = i
        precL (Infix  i) = i+1
        precL (InfixR i) = i+1
        precR (InfixR i) = i
        precR (Infix  i) = i+1
        precR (InfixL i) = i+1

    render x = case x of
        DDoc d -> interpretDocOp $ render <$> d
        DAtom_ x -> renderA x
        DOp _ x s y -> case s of
            ""  -> render x P.<> render y
            " " -> render x P.<+> render y
            _ | simple x && simple y && s /= "," -> render x <> P.text s <> render y
              | otherwise -> (render x <++> s) P.<+> render y
      where
        renderA (AEnd s) = P.text s
        renderA (ACons s _ d a) = P.text s <> render d <> renderA a

        x <++> "," = x <> P.text ","
        x <++> s = x P.<+> P.text s
        
instance Show Doc where
    show = show . renderDocX

showDoc_ :: Doc -> P.Doc
showDoc_ = renderDocX

shVar = DVar

shLet i a b = shLam' (shLet' (inBlue' $ shVar i) $ DUp i a) (DUp i b)
shLet_ a b = DFreshName True $ shLam' (shLet' (shVar 0) $ DUp 0 a) b

-----------------------------------------

instance IsString Doc where
    fromString = text

shTuple [] = "()"
shTuple [x] = DParen $ DParen x
shTuple xs = DParen $ foldr1 (\x y -> DOp (InfixR (-20)) x "," y) xs

shAnn _ True x y | strip y == "Type" = x
shAnn s _ x y = DOp (InfixR (-3)) x s y

shArr = DArr

shCstr x y = DOp (Infix (-2)) x "~" y

shLet' x y = DOp (Infix (-4)) x ":=" y

pattern DLam vs e = DGlueR (-10) (DAtom_ (ACons "\\" 11 vs (AEnd " ->"))) e

hardSpace a b = DOp (InfixR 11) a " " b
dLam vs e = DLam (foldr1 hardSpace vs) e

shLam' x (DFreshName True d) = DFreshName True $ shLam' (DUp 0 x) d
shLam' x (DLam xs y) = DLam (hardSpace x xs) y
shLam' x y = dLam [x] y


