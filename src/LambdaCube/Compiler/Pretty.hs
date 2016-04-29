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
import Control.DeepSeq
--import Debug.Trace

import qualified Text.PrettyPrint.ANSI.Leijen as P

import LambdaCube.Compiler.Utils

-------------------------------------------------------------------------------- inherited doc operations

-- add wl-pprint combinators as necessary here
data DocOp a
    = DOColor Formatting a
    | DOHSep a a
    | DOHCat a a
    | DOSoftSep a a
    | DOVCat a a
    | DONest Int a
    | DOTupled [a]
    deriving (Eq, Functor, Foldable, Traversable)

data Formatting
    = ForeColor Color
    | BackColor Color
    | Underline Bool
    deriving (Eq)

data Color = Red | Green | Blue
    deriving (Eq)

interpretDocOp :: DocOp P.Doc -> P.Doc
interpretDocOp = \case
    DOHSep a b  -> a P.<+> b
    DOHCat a b  -> a <> b
    DOSoftSep a b -> a P.</> b
    DOVCat a b  -> a P.<$$> b
    DONest n a  -> P.nest n a
    DOTupled a  -> P.tupled a
    DOColor c x -> case c of
        ForeColor Red         -> P.dullred   x
        ForeColor Green       -> P.dullgreen x
        ForeColor Blue        -> P.dullblue  x
        BackColor Red         -> P.ondullred   x
        BackColor Green       -> P.ondullgreen x
        BackColor Blue        -> P.ondullblue  x
        Underline True        -> P.underline   x
        Underline False       -> P.deunderline x

-------------------------------------------------------------------------------- fixity

data Fixity
    = Infix  !Int
    | InfixL !Int
    | InfixR !Int
    deriving (Eq, Show)

instance PShow Fixity where
    pShow = \case
        Infix  i -> "infix"  `DApp` pShow i
        InfixL i -> "infixl" `DApp` pShow i
        InfixR i -> "infixr" `DApp` pShow i

precedence, leftPrecedence, rightPrecedence :: Fixity -> Int

precedence = \case
    Infix i  -> i
    InfixR i -> i
    InfixL i -> i

leftPrecedence (InfixL i) = i
leftPrecedence f = precedence f + 1

rightPrecedence (InfixR i) = i
rightPrecedence f = precedence f + 1

-------------------------------------------------------------------------------- doc data type

data Doc
    = DDoc (DocOp Doc)

    | DAtom DocAtom
    | DInfix Fixity Doc DocAtom Doc

    | DFreshName Bool{-used-} Doc
    | DVar Int
    | DUp Int Doc
    deriving (Eq)

data DocAtom
    = SimpleAtom String
    | ComplexAtom String Int Doc DocAtom
    deriving (Eq)

instance IsString Doc where
    fromString = text

text = DText
pattern DText s = DAtom (SimpleAtom s)

instance Monoid Doc where
    mempty = text ""
    a `mappend` b = DDoc $ DOHCat a b

instance NFData Doc where
    rnf x = rnf $ show x    -- TODO

pattern DColor c a = DDoc (DOColor c a)

strip :: Doc -> Doc
strip = \case
    DColor _ x     -> strip x
    DUp _ x        -> strip x
    DFreshName _ x -> strip x
    x              -> x

simple :: Doc -> Bool
simple x = case strip x of
    DAtom{} -> True
    DVar{} -> True
    _ -> False

instance Show Doc where
    show = show . renderDoc

plainShow :: PShow a => a -> String
plainShow = show . P.plain . renderDoc . pShow

renderDoc :: Doc -> P.Doc
renderDoc
    = render
    . addPar (-10)
    . flip runReader ((\s n -> '_': n: s) <$> iterate ('\'':) "" <*> ['a'..'z'])
    . flip evalStateT (flip (:) <$> iterate ('\'':) "" <*> ['a'..'z'])
    . showVars
  where
    showVars = \case
        DAtom s -> DAtom <$> showVarA s
        DDoc d -> DDoc <$> traverse showVars d
        DInfix pr x op y -> DInfix pr <$> showVars x <*> showVarA op <*> showVars y
        DVar i -> asks $ text . (!! i)
        DFreshName True x -> gets head >>= \n -> modify tail >> local (n:) (showVars x)
        DFreshName False x -> local ("_":) $ showVars x
        DUp i x -> local (dropIndex i) $ showVars x
      where
        showVarA (SimpleAtom s) = pure $ SimpleAtom s
        showVarA (ComplexAtom s i d a) = ComplexAtom s i <$> showVars d <*> showVarA a

    addPar :: Int -> Doc -> Doc
    addPar pr x = case x of
        DAtom x -> DAtom $ addParA x
        DInfix pr' x op y -> (if protect then DParen else id)
                       $ DInfix pr' (addPar (leftPrecedence pr') x) (addParA op) (addPar (rightPrecedence pr') y)
        DColor c x -> DColor c $ addPar pr x
        DDoc d -> DDoc $ addPar (-10) <$> d
      where
        addParA (SimpleAtom s) = SimpleAtom s
        addParA (ComplexAtom s i d a) = ComplexAtom s i (addPar i d) $ addParA a

        protect = case x of
            DInfix f _ _ _ -> precedence f < pr
            _ -> False

    render :: Doc -> P.Doc
    render = \case
        DDoc d -> interpretDocOp $ render <$> d
        DAtom x -> renderA x
        DInfix _ x op y -> case op of
            SimpleAtom ""  -> render x P.<> render y
            SimpleAtom " " -> render x P.<+> render y
            _   -> (render x <++> op) P.<+> render y
      where
        renderA (SimpleAtom s) = P.text s
        renderA (ComplexAtom s _ d a) = P.text s <> render d <> renderA a

        x <++> SimpleAtom "," = x <> P.text ","
        x <++> s = x P.<+> renderA s

-------------------------------------------------------------------------- combinators

red         = DColor $ ForeColor Red
green       = DColor $ ForeColor Green
blue        = DColor $ ForeColor Blue
onred       = DColor $ BackColor Red
ongreen     = DColor $ BackColor Green
onblue      = DColor $ BackColor Blue
underline   = DColor $ Underline True

a <+>  b = DDoc $ DOHSep    a b
a </>  b = DDoc $ DOSoftSep a b
a <$$> b = DDoc $ DOVCat    a b
nest n = DDoc . DONest n
tupled = DDoc . DOTupled
bracketed [] = text "[]"
bracketed xs = DPar "[" (foldr1 DComma xs) "]"

hsep [] = mempty
hsep xs = foldr1 (<+>) xs

vcat [] = mempty
vcat xs = foldr1 (<$$>) xs

shVar = DVar

pattern DPar l d r = DAtom (ComplexAtom l (-20) d (SimpleAtom r))
pattern DParen x = DPar "(" x ")"
pattern DBrace x = DPar "{" x "}"
pattern DOp s f l r = DInfix f l (SimpleAtom s) r
pattern DSep p a b = DOp " " p a b
pattern DGlue p a b = DOp "" p a b

pattern DArr_ s x y = DOp s (InfixR (-1)) x y
pattern DArr x y = DArr_ "->" x y
pattern DAnn x y = DOp "::" (InfixR (-3)) x y
pattern DApp x y = DSep (InfixL 10) x y
pattern DGlueR pr x y = DSep (InfixR pr) x y
pattern DComma a b = DOp "," (InfixR (-20)) a b

braces = DBrace
parens = DParen

shTuple [] = "()"
shTuple [x] = DParen $ DParen x
shTuple xs = DParen $ foldr1 DComma xs

shLet i a b = shLam' (shLet' (blue $ shVar i) $ DUp i a) (DUp i b)
shLet_ a b = DFreshName True $ shLam' (shLet' (shVar 0) $ DUp 0 a) b
shLet' = DOp ":=" (Infix (-4))

shAnn True x y | strip y == "Type" = x
shAnn _ x y = DOp "::" (InfixR (-3)) x y

shArr = DArr

shCstr = DOp "~" (Infix (-2))

pattern DForall vs e = DArr_ "." (DSep (Infix 10) (DText "forall") vs) e
pattern DContext vs e = DArr_ "=>" vs e
pattern DParContext vs e = DContext (DParen vs) e
pattern DLam vs e = DGlueR (-10) (DAtom (ComplexAtom "\\" 11 vs (SimpleAtom " ->"))) e

shLam' x (DFreshName True d) = DFreshName True $ shLam' (DUp 0 x) d
shLam' x (DLam xs y) = DLam (DSep (InfixR 11) x xs) y
shLam' x y = DLam x y

showForall x (DFreshName u d) = DFreshName u $ showForall (DUp 0 x) d
showForall x (DForall xs y) = DForall (DSep (InfixR 11) x xs) y
showForall x y = DForall x y

showContext x (DFreshName u d) = DFreshName u $ showContext (DUp 0 x) d
showContext x (DParContext xs y) = DParContext (DComma x xs) y
showContext x (DContext xs y) = DParContext (DComma x xs) y
showContext x y = DContext x y

--------------------------------------------------------------------------------

class PShow a where
    pShow :: a -> Doc

ppShow :: PShow a => a -> String
ppShow = show . pShow

instance PShow Doc     where pShow = id
instance PShow Int     where pShow = fromString . show
instance PShow Integer where pShow = fromString . show
instance PShow Double  where pShow = fromString . show
instance PShow Char    where pShow = fromString . show
instance PShow ()      where pShow _ = "()"

instance PShow Bool where
    pShow b = if b then "True" else "False"

instance (PShow a, PShow b) => PShow (Either a b) where
   pShow = either (("Left" `DApp`) . pShow) (("Right" `DApp`) . pShow)

instance (PShow a, PShow b) => PShow (a, b) where
    pShow (a, b) = tupled [pShow a, pShow b]

instance (PShow a, PShow b, PShow c) => PShow (a, b, c) where
    pShow (a, b, c) = tupled [pShow a, pShow b, pShow c]

instance PShow a => PShow [a] where
    pShow = bracketed . map pShow

instance PShow a => PShow (Maybe a) where
    pShow = maybe "Nothing" (("Just" `DApp`) . pShow)

--instance PShow a => PShow (Set a) where
--    pShow = pShow . Set.toList

--instance (PShow s, PShow a) => PShow (Map s a) where
--    pShow = braces . vcat . map (\(k, t) -> pShow k <> P.colon <+> pShow t) . Map.toList

