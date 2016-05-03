{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}
module LambdaCube.Compiler.Pretty
    ( module LambdaCube.Compiler.Pretty
    ) where

import Data.Maybe
import Data.String
import Data.Char
--import qualified Data.Set as Set
--import qualified Data.Map as Map
import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Arrow hiding ((<+>))
import Control.DeepSeq
--import Debug.Trace

import qualified Text.PrettyPrint.ANSI.Leijen as P

import LambdaCube.Compiler.Utils

-------------------------------------------------------------------------------- fixity

data Fixity
    = Infix  !Int
    | InfixL !Int
    | InfixR !Int
    deriving (Eq)

instance PShow Fixity where
    pShow = \case
        Infix  i -> "infix"  <+> pShow i
        InfixL i -> "infixl" <+> pShow i
        InfixR i -> "infixr" <+> pShow i

precedence, leftPrecedence, rightPrecedence :: Fixity -> Int

precedence = \case
    Infix i  -> i
    InfixR i -> i
    InfixL i -> i

leftPrecedence (InfixL i) = i
leftPrecedence f = precedence f + 1

rightPrecedence (InfixR i) = i
rightPrecedence f = precedence f + 1

defaultFixity :: Maybe Fixity -> Fixity
defaultFixity = fromMaybe (InfixL 9)

-------------------------------------------------------------------------------- doc data type

data Doc
    = forall f . Traversable f => DDocOp (f P.Doc -> P.Doc) (f Doc)
    | DFormat (P.Doc -> P.Doc) Doc
    | DTypeNamespace Bool Doc

    | DAtom DocAtom
    | DInfix Fixity Doc DocAtom Doc
    | DPreOp Int DocAtom Doc

    | DFreshName Bool{-used-} Doc
    | DVar Int
    | DUp Int Doc
    | DResetFreshNames Doc

    | DExpand Doc Doc

data DocAtom
    = SimpleAtom String
    | ComplexAtom String Int Doc DocAtom

mapDocAtom f (SimpleAtom s) = SimpleAtom s
mapDocAtom f (ComplexAtom s i d a) = ComplexAtom s i (f s i d) $ mapDocAtom f a

instance IsString Doc where
    fromString = text

text = DText
pattern DText s = DAtom (SimpleAtom s)

instance Monoid Doc where
    mempty = text ""
    mappend = dTwo mappend

instance NFData Doc where
    rnf x = rnf $ show x    -- TODO

instance Show Doc where
    show = ($ "") . P.displayS . P.renderPretty 0.4 200 . renderDoc

plainShow :: PShow a => a -> String
plainShow = ($ "") . P.displayS . P.renderPretty 0.6 150 . P.plain . renderDoc . pShow

simpleShow :: PShow a => a -> String
simpleShow = ($ "") . P.displayS . P.renderPretty 0.4 200 . P.plain . renderDoc . pShow

renderDoc :: Doc -> P.Doc
renderDoc
    = render
    . addPar (-10, -10)
    . namespace False
    . flip runReader freeNames
    . flip evalStateT freshNames
    . showVars
    . expand True
  where
    freshNames = flip (:) <$> iterate ('\'':) "" <*> ['a'..'z']
    freeNames = map ('_':) freshNames

    noexpand = expand False
    expand full = \case
        DExpand short long -> expand full $ if full then long else short
        DFormat c x -> DFormat c $ expand full x
        DTypeNamespace c x -> DTypeNamespace c $ expand full x
        DDocOp x d -> DDocOp x $ expand full <$> d
        DAtom s -> DAtom $ mapDocAtom (\_ _ -> noexpand) s
        DInfix pr x op y -> DInfix pr (noexpand x) (mapDocAtom (\_ _ -> noexpand) op) (noexpand y)
        DPreOp pr op y -> DPreOp pr (mapDocAtom (\_ _ -> noexpand) op) (noexpand y)
        DVar i -> DVar i
        DFreshName b x -> (if full then DResetFreshNames else id) $ DFreshName b $ noexpand x
        DResetFreshNames x -> DResetFreshNames $ expand full x
        DUp i x -> DUp i $ noexpand x

    showVars = \case
        DAtom s -> DAtom <$> showVarA s
        DFormat c x -> DFormat c <$> showVars x
        DTypeNamespace c x -> DTypeNamespace c <$> showVars x
        DDocOp x d -> DDocOp x <$> traverse showVars d
        DInfix pr x op y -> DInfix pr <$> showVars x <*> showVarA op <*> showVars y
        DPreOp pr op y -> DPreOp pr <$> showVarA op <*> showVars y
        DVar i -> asks $ text . (!! i)
        DFreshName True x -> gets head >>= \n -> modify tail >> local (n:) (showVars x)
        DFreshName False x -> local ("_":) $ showVars x
        DResetFreshNames x -> do
            st <- get
            put freshNames
            local (const freeNames) (showVars x) <* put st
        DUp i x -> local (dropIndex i) $ showVars x
      where
        showVarA (SimpleAtom s) = pure $ SimpleAtom s
        showVarA (ComplexAtom s i d a) = ComplexAtom s i <$> showVars d <*> showVarA a

    namespace :: Bool -> Doc -> Doc
    namespace tn x = case x of
        DAtom x -> DAtom $ namespaceA x
        DText "'List" `DApp` x -> namespace tn $ DBracket x
        DInfix pr' x op y -> DInfix pr' (namespace tn x) (namespaceA op) (namespace tn y)
        DPreOp pr' op y -> DPreOp pr' (namespaceA op) (namespace tn y)
        DFormat c x -> DFormat c $ namespace tn x
        DTypeNamespace c x -> namespace c x
        DDocOp x d -> DDocOp x $ namespace tn <$> d
      where
        namespaceA (SimpleAtom s) = SimpleAtom $ switch tn s
        namespaceA (ComplexAtom s i d a) = ComplexAtom s i (namespace tn d) $ namespaceA a

        switch True ('`': '\'': cs@(c: _)) | isUpper c = '`': cs
        switch True ('\'': cs@(c: _)) | isUpper c {- && last cs /= '\'' -} = cs
        switch True "Type" = "Type"  -- TODO: remove
        switch True cs@(c:_) | isUpper c = '\'': cs
        switch _ x = x

    addPar :: (Int, Int) -> Doc -> Doc
    addPar pr@(prl, prr) x = case x of
        DAtom x -> DAtom $ addParA x
        DOp0 s f -> DParen $ DOp0 s f
        DOp0 s f `DApp` x `DApp` y -> addPar pr $ DOp (addBackquotes s) f x y
        DInfix pr' x op y
            | precedence pr' < prl || precedence pr' < prr
            -> DParen $ DInfix pr' (addPar (-20, leftPrecedence pr') x) (addParA op) (addPar (rightPrecedence pr', -20) y)
            | otherwise -> DInfix pr' (addPar (prl, leftPrecedence pr') x) (addParA op) (addPar (rightPrecedence pr', prr) y)
        DPreOp pr' op y
            | pr' < prr -> DParen $ DPreOp pr' (addParA op) (addPar (pr', -20) y)
            | otherwise -> DPreOp pr' (addParA op) (addPar (pr', prr) y)
        DFormat c x -> DFormat c $ addPar pr x
        DTypeNamespace c x -> DTypeNamespace c $ addPar pr x
        DDocOp x d -> DDocOp x $ addPar (-10, -10) <$> d
      where
        addParA (SimpleAtom s) = SimpleAtom s
        addParA (ComplexAtom s i d a) = ComplexAtom s i (addPar (i, i) d) $ addParA a

        addBackquotes "EqCTt" = "~"
        addBackquotes s@(c:_) | isAlpha c || c == '_' || c == '\'' = '`': s ++ "`"
        addBackquotes s = s

    getApps (DApp (getApps -> (n, xs)) x) = (n, x: xs)
    getApps x = (x, [])

    render :: Doc -> P.Doc
    render = snd . render'
      where
        render' = \case
            DText "Nil" -> rtext "[]"
            DText "'Nil" -> rtext "'[]"
            DAtom x -> renderA x
            DFormat c x -> second c $ render' x
            DDocOp f d -> (('\0', '\0'), f $ render <$> d)
            DPreOp _ op y -> renderA op <++> render' y
            DSep (InfixR 11) a b -> gr $ render' a <+++> render' b
            x@DApp{} -> case getApps x of
--                (DText "List", [x]) -> gr $ rtext "[" <+++> render' x <++> rtext "]"
                (n, reverse -> xs) -> ((\xs -> (fst $ head xs, snd $ last xs)) *** P.nest 2 . P.sep) (unzip $ render' n: (render' <$> xs))
            DInfix _ x op y -> gr $ render' x <+++> renderA op <++> render' y

        renderA (SimpleAtom s) = rtext s
        renderA (ComplexAtom s _ d a) = rtext s <++> render' d <++> renderA a

        gr = second (P.nest 2. P.group)

        rtext "" = (('\0', '\0'), mempty)
        rtext s@(h:_) = ((h, last s), P.text s)

        ((lx, rx), x) <++> ((ly, ry), y) = ((lx, ry), z)
          where
            z | sep rx ly = x P.<+> y
              | otherwise = x P.<> y

        ((lx, rx), x) <+++> ((ly, ry), y) = ((lx, ry), z)
          where
            z | sep rx ly = x P.<> P.line P.<> y
              | otherwise = x P.<> y

        sep x y
            | x == '\0' || y == '\0' = False
            | isSpace x || isSpace y = False
            | y == ',' = False
            | x == ',' = True
--            | y == ':' && not (graphicChar x) = False
            | x == '\\' && (isOpen y || isAlph y) = False
            | isOpen x = False
            | isClose y = False
            | otherwise = True
          where
            isAlph c = isAlphaNum c || c `elem` ("'_" :: String)
            isOpen c = c `elem` ("({[" :: String)
            isClose c = c `elem` (")}]" :: String)

isOpName (c:cs) | c `elem` ("#<>!.:^&@|-+*/\\~%=$" :: String) = True
isOpName _ = False

-------------------------------------------------------------------------- combinators

-- add wl-pprint combinators as necessary here
red         = DFormat P.dullred
green       = DFormat P.dullgreen
blue        = DFormat P.dullblue
onred       = DFormat P.ondullred
ongreen     = DFormat P.ondullgreen
onblue      = DFormat P.ondullblue
underline   = DFormat P.underline

-- add wl-pprint combinators as necessary here
hardline = dZero P.hardline
(<+>)  = dTwo (P.<+>)
(</>)  = dTwo (P.</>)
(<$$>) = dTwo (P.<$$>)
nest n = dOne (P.nest n)
tupled = dList P.tupled
sep    = dList P.sep
hsep   = dList P.hsep
vcat   = dList P.vcat

dZero x    = DDocOp (const x) (Const ())
dOne f     = DDocOp (f . runIdentity) . Identity
dTwo f x y = DDocOp (\(Two x y) -> f x y) (Two x y)
dList f    = DDocOp f

data Two a = Two a a
    deriving (Functor, Foldable, Traversable)

bracketed [] = text "[]"
bracketed xs = DPar "[" (foldr1 DComma xs) "]"

shVar = DVar

shortForm d = DPar "" d ""
expand = DExpand

infixl 4 `DApp`

pattern DAt x       = DGlue     (InfixR   20) (DText "@") x
pattern DApp x y    = DSep      (InfixL   10)  x y
pattern DArr_ s x y = DOp s     (InfixR  (-1)) x y      -- -> => .
pattern DCstr x y   = DOp "~"   (Infix   (-2)) x y
pattern DAnn x y    = DOp "::"  (Infix   (-3)) x (DTypeNamespace True y)
pattern DLet s x y  = DOp s     (Infix   (-4)) x y      -- := =
pattern DComma a b  = DOp ","   (InfixR (-20)) a b
pattern DPar l d r  = DAtom (ComplexAtom l (-20) d (SimpleAtom r))

pattern DParen x = DPar "(" x ")"
pattern DBrace x = DPar "{" x "}"
pattern DBracket x = DPar "[" x "]"
pattern DOp s f l r = DInfix f l (SimpleAtom s) r
pattern DOp0 s f = DOp s f (DText "") (DText "")
pattern DSep p a b = DOp " " p a b
pattern DGlue p a b = DOp "" p a b

pattern DArr x y = DArr_ "->" x y

braces = DBrace
parens = DParen

dApp x y = DApp x y

shCstr = DCstr

shTuple [] = "()"
shTuple [x] = DParen $ DParen x
shTuple xs = DParen $ foldr1 DComma xs

shAnn = DAnn

shArr = DArr


pattern DForall s vs e = DArr_ s (DPreOp 10 (SimpleAtom "forall") vs) e
pattern DContext vs e = DArr_ "=>" vs e
pattern DParContext vs e = DContext (DParen vs) e
pattern DLam vs e = DPreOp (-10) (ComplexAtom "\\" 11 vs (SimpleAtom "->")) e

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

instance PShow Void where
    pShow = elimVoid

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

