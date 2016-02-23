{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}  -- instance NFData SourcePos
{-# OPTIONS -fno-warn-unused-do-bind -fno-warn-name-shadowing #-}
module LambdaCube.Compiler.Lexer
    ( module LambdaCube.Compiler.Lexer
    , module Pr
    ) where

import Data.Monoid
import Data.Maybe
import Data.List
import Data.Char
import qualified Data.Set as Set
import qualified Data.Map as Map

import Control.Monad.Except
import Control.Monad.RWS
import Control.Arrow hiding ((<+>))
import Control.Applicative
import Control.DeepSeq

import Text.Megaparsec
import Text.Megaparsec as Pr hiding (try, label, Message)
import Text.Megaparsec.Lexer hiding (lexeme, symbol, space, negate, symbol', indentBlock)
import Text.Megaparsec.Pos

import LambdaCube.Compiler.Pretty hiding (Doc, braces, parens)

-------------------------------------------------------------------------------- parser utils

-- see http://blog.ezyang.com/2014/05/parsec-try-a-or-b-considered-harmful/comment-page-1/#comment-6602
try_ s m = try m <?> s

manyNM a b _ | b < a || b < 0 || a < 0 = mzero
manyNM 0 0 _ = pure []
manyNM 0 n p = option [] $ (:) <$> p <*> manyNM 0 (n-1) p
manyNM k n p = (:) <$> p <*> manyNM (k-1) (n-1) p

-------------------------------------------------------------------------------- parser type

type P = ParsecT String (RWS ((DesugarInfo, Namespace), (Int, Int){-indentation level-}) [PostponedCheck] SourcePos)

type PostponedCheck = Maybe String

type DesugarInfo = (FixityMap, ConsMap)

type ConsMap = Map.Map SName{-constructor name-}
                (Either ((SName{-case eliminator name-}, Int{-num of indices-}), [(SName, Int)]{-constructors with arities-})
                        Int{-arity-})

dsInfo :: P DesugarInfo
dsInfo = asks $ fst . fst

namespace :: P Namespace
namespace = asks $ snd . fst

runP_ r f p = (\(a, s, w) -> (a, w)) $ runRWS p (r, (0, 0)) (initialPos f)

runP r f p s = runP_ r f $ runParserT p f s

runP' r f p st = runP_ r f $ runParserT' p st

-------------------------------------------------------------------------------- literals

data Lit
    = LInt Integer
    | LChar Char
    | LFloat Double
    | LString String
  deriving (Eq)

instance Show Lit where
    show = \case
        LFloat x  -> show x
        LString x -> show x
        LInt x    -> show x
        LChar x   -> show x

-------------------------------------------------------------------------------- names

type SName = String

pattern CaseName :: String -> String
pattern CaseName cs <- (getCaseName -> Just cs) where CaseName = caseName

caseName (c:cs) = toLower c: cs ++ "Case"
getCaseName cs = case splitAt 4 $ reverse cs of
    (reverse -> "Case", xs) -> Just $ reverse xs
    _ -> Nothing

pattern MatchName cs <- (getMatchName -> Just cs) where MatchName = matchName

matchName cs = "match" ++ cs
getMatchName ('m':'a':'t':'c':'h':cs) = Just cs
getMatchName _ = Nothing


-------------------------------------------------------------------------------- source infos

instance NFData SourcePos where
    rnf x = x `seq` ()

data Range = Range SourcePos SourcePos
    deriving (Eq, Ord)

instance NFData Range where
    rnf (Range a b) = rnf a `seq` rnf b `seq` ()

instance PShow Range where
    pShowPrec _ (Range b e) | sourceName b == sourceName e = text (sourceName b) <+> f b <> "-" <> f e
      where
        f x = pShow (sourceLine x) <> ":" <> pShow (sourceColumn x)

joinRange :: Range -> Range -> Range
joinRange (Range b e) (Range b' e') = Range (min b b') (max e e')

data SI
    = NoSI (Set.Set String) -- no source info, attached debug info
    | RangeSI Range

instance NFData SI where
    rnf = \case
        NoSI x -> rnf x
        RangeSI r -> rnf r

instance Show SI where show _ = "SI"
instance Eq SI where _ == _ = True
instance Ord SI where _ `compare` _ = EQ

instance Monoid SI where
  mempty = NoSI Set.empty
  mappend (RangeSI r1) (RangeSI r2) = RangeSI (joinRange r1 r2)
  mappend (NoSI ds1) (NoSI ds2) = NoSI  (ds1 `Set.union` ds2)
  mappend r@RangeSI{} _ = r
  mappend _ r@RangeSI{} = r

instance PShow SI where
    pShowPrec _ (NoSI ds) = hsep $ map pShow $ Set.toList ds
    pShowPrec _ (RangeSI r) = pShow r

showSI _ (NoSI ds) = unwords $ Set.toList ds
showSI srcs si@(RangeSI (Range s e)) = case Map.lookup (sourceName s) srcs of
    Just source -> show str
      where
        startLine = sourceLine s - 1
        endline = sourceLine e - if sourceColumn e == 1 then 1 else 0
        len = endline - startLine
        str = vcat $ text (show s <> ":"){- <+> "-" <+> text (show e)-}:
                   map text (take len $ drop startLine $ lines source)
                ++ [text $ replicate (sourceColumn s - 1) ' ' ++ replicate (sourceColumn e - sourceColumn s) '^' | len == 1]
    Nothing -> showSourcePosSI si

showSourcePosSI (NoSI ds) = unwords $ Set.toList ds
showSourcePosSI (RangeSI (Range s _)) = show s

-- TODO: remove
validSI RangeSI{} = True
validSI _ = False

debugSI a = NoSI (Set.singleton a)

si@(RangeSI r) `validate` xs | all validSI xs && r `notElem` [r | RangeSI r <- xs]  = si
_ `validate` _ = mempty

sourceNameSI (RangeSI (Range a _)) = sourceName a

sameSource r@RangeSI{} q@RangeSI{} = sourceNameSI r == sourceNameSI q
sameSource _ _ = True

class SourceInfo si where
    sourceInfo :: si -> SI

instance SourceInfo SI where
    sourceInfo = id

instance SourceInfo si => SourceInfo [si] where
    sourceInfo = foldMap sourceInfo

class SetSourceInfo a where
    setSI :: SI -> a -> a

appRange :: P (SI -> a) -> P a
appRange p = (\p1 a p2 -> a $ RangeSI $ Range p1 p2) <$> getPosition <*> p <*> get

type SIName = (SI, SName)

-- todo: eliminate
psn p = appRange $ flip (,) <$> p

-------------------------------------------------------------------------------- namespace handling

data Namespace = TypeNS | ExpNS
  deriving (Eq, Show)

tick = (\case TypeNS -> switchTick; _ -> id)

tick' c = (`tick` c) <$> namespace

switchNamespace = \case ExpNS -> TypeNS; TypeNS -> ExpNS

switchTick ('\'': n) = n
switchTick n = '\'': n
 
modifyLevel f = local $ first $ second f

typeNS, expNS, switchNS :: P a -> P a
typeNS   = modifyLevel $ const TypeNS
expNS    = modifyLevel $ const ExpNS
switchNS = modifyLevel $ switchNamespace

-------------------------------------------------------------------------------- identifiers

lowerLetter     = satisfy $ \c -> isLower c || c == '_'
upperLetter     = satisfy isUpper
identStart      = satisfy $ \c -> isLetter c || c == '_'
identLetter     = satisfy $ \c -> isAlphaNum c || c == '_' || c == '\'' || c == '#'
lowercaseOpLetter = oneOf "!#$%&*+./<=>?@\\^|-~"
opLetter          = lowercaseOpLetter <|> char ':'

maybeStartWith p i = i <|> (:) <$> satisfy p <*> i

upperCase       = identifier (tick' =<< maybeStartWith (=='\'') ((:) <$> upperLetter <*> many identLetter)) <?> "uppercase ident"
lowerCase       = identifier ((:) <$> lowerLetter <*> many identLetter) <?> "lowercase ident"
backquotedIdent = identifier ((:) <$ char '`' <*> identStart <*> many identLetter <* char '`') <?> "backquoted ident"
symbols         = operator (some opLetter) <?> "symbols"
lcSymbols       = operator ((:) <$> lowercaseOpLetter <*> many opLetter) <?> "symbols"
colonSymbols    = operator ((:) <$> satisfy (== ':') <*> many opLetter) <?> "op symbols"
moduleName      = identifier (intercalate "." <$> sepBy1 ((:) <$> upperLetter <*> many identLetter) (char '.')) <?> "module name"

patVar          = second f <$> lowerCase where
    f "_" = ""
    f x = x
lhsOperator     = lcSymbols <|> backquotedIdent
rhsOperator     = symbols <|> backquotedIdent
varId           = lowerCase <|> parens (symbols <|> backquotedIdent)
upperLower      = lowerCase <|> upperCase <|> parens symbols

-------------------------------------------------------------------------------- fixity handling

data FixityDef = Infix | InfixL | InfixR deriving (Show)
type Fixity = (FixityDef, Int)
type FixityMap = Map.Map SName Fixity

calcPrec
  :: (Show e, Show f)
     => (f -> e -> e -> e)
     -> (f -> Fixity)
     -> e
     -> [(f, e)]
     -> e
calcPrec app getFixity e = compileOps [((Infix, -1000), error "calcPrec", e)]
  where
    compileOps [(_, _, e)] [] = e
    compileOps acc [] = compileOps (shrink acc) []
    compileOps acc@((p, g, e1): ee) es_@((op, e'): es) = case compareFixity (pr, op) (p, g) of
        Right GT -> compileOps ((pr, op, e'): acc) es
        Right LT -> compileOps (shrink acc) es_
        Left err -> error err
      where
        pr = getFixity op

    shrink ((_, op, e): (pr, op', e'): es) = (pr, op', app op e' e): es

    compareFixity ((dir, i), op) ((dir', i'), op')
        | i > i' = Right GT
        | i < i' = Right LT
        | otherwise = case (dir, dir') of
            (InfixL, InfixL) -> Right LT
            (InfixR, InfixR) -> Right GT
            _ -> Left $ "fixity error:" ++ show (op, op')

parseFixityDecl :: P [(SIName, Fixity)]
parseFixityDecl = do
    dir <-    Infix  <$ reserved "infix"
          <|> InfixL <$ reserved "infixl"
          <|> InfixR <$ reserved "infixr"
    LInt n <- parseLit
    let i = fromIntegral n
    ns <- commaSep1 rhsOperator
    return $ (,) <$> ns <*> pure (dir, i)

getFixity :: DesugarInfo -> SName -> Fixity
getFixity (fm, _) n = fromMaybe (InfixL, 9) $ Map.lookup n fm


----------------------------------------------------------- operators and identifiers

reservedOp name = lexeme $ try $ string name *> notFollowedBy opLetter

reserved name = lexeme $ try $ string name *> notFollowedBy identLetter

expect msg p i = i >>= \n -> if p n then unexpected (msg ++ " " ++ show n) else return n

identifier ident = lexeme_ $ try $ expect "reserved word" (`Set.member` theReservedNames) ident

operator oper = lexeme_ $ try $ trCons <$> expect "reserved operator" (`Set.member` theReservedOpNames) oper
  where
    trCons ":" = "Cons"
    trCons x = x

theReservedOpNames = Set.fromList ["::","..","=","\\","|","<-","->","@","~","=>"]

theReservedNames = Set.fromList $
    ["let","in","case","of","if","then","else"
    ,"data","type"
    ,"class","default","deriving","do","import"
    ,"infix","infixl","infixr","instance","module"
    ,"newtype","where"
    ,"primitive"
    -- "as","qualified","hiding"
    ] ++
    ["foreign","import","export","primitive"
    ,"_ccall_","_casm_"
    ,"forall"
    ]

----------------------------------------------------------- indentation, white space, symbols

checkIndent = do
    (r, c) <- asks snd
    pos <- getPosition
    if (sourceColumn pos <= c && sourceLine pos /= r) then fail "wrong indentation" else return pos

indentMS null p = (if null then option [] else id) $ do
    pos' <- checkIndent
    (if null then many else some) $ do
        pos <- getPosition
        guard (sourceColumn pos == sourceColumn pos')
        local (second $ const (sourceLine pos, sourceColumn pos)) p

lexeme' sp p = do
    p1 <- checkIndent
    x <- p
    p2 <- getPosition
    put p2
    sp
    return (RangeSI $ Range p1 p2, x)

lexeme = fmap snd . lexeme' whiteSpace

lexeme_  = lexeme' whiteSpace

----------------------------------------------------------------------
----------------------------------------------------------------------
-- based on
--
-- Module      :  Text.Parsec.Token
-- Copyright   :  (c) Daan Leijen 1999-2001, (c) Paolo Martini 2007
-- License     :  BSD-style

symbol = symbol' whiteSpace

symbol' sp name
    = lexeme' sp (string name)

whiteSpace = skipMany (simpleSpace <|> oneLineComment <|> multiLineComment <?> "")

simpleSpace
    = skipSome (satisfy isSpace)

oneLineComment
    =  try (string "--" >> many (char '-') >> notFollowedBy opLetter)
    >> skipMany (satisfy (/= '\n'))

multiLineComment = try (string "{-") *> inCommentMulti

inCommentMulti
    =   try (() <$ string "-}")
    <|> multiLineComment         *> inCommentMulti
    <|> skipSome (noneOf "{}-")  *> inCommentMulti
    <|> oneOf "{}-"              *> inCommentMulti
    <?> "end of comment"


parens          = between (symbol "(") (symbol ")")
braces          = between (symbol "{") (symbol "}")
brackets        = between (symbol "[") (symbol "]")

commaSep p      = sepBy p $ symbol ","
commaSep1 p     = sepBy1 p $ symbol ","

parseLit = lexeme $ charLiteral <|> stringLiteral <|> natFloat
  where
    charLiteral     = LChar <$> between (char '\'')
                                        (char '\'' <?> "end of character")
                                        (char '\\' *> escapeCode <|> satisfy (\c -> c > '\026' && c /= '\'') <?> "literal character")
                    <?> "character"

    stringLiteral   = between (char '"')
                              (char '"' <?> "end of string")
                              (LString . concat <$> many stringChar)
                    <?> "literal string"

    stringChar      = char '\\' *> stringEscape <|> (:[]) <$> satisfy (\c -> c > '\026' && c /= '"') <?> "string character"

    stringEscape    = [] <$ some simpleSpace <* (char '\\' <?> "end of string gap")
                  <|> [] <$ char '&'
                  <|> (:[]) <$> escapeCode

    -- escape codes
    escapeCode      = charEsc <|> charNum <|> charAscii <|> char '^' *> charControl <?> "escape code"

    charControl     = toEnum . (+ (- fromEnum 'A')) . fromEnum <$> satisfy isUpper <?> "uppercase letter"

    charNum         = toEnum . fromInteger <$> (decimal <|> char 'o' *> octal <|> char 'x' *> hexadecimal)

    charEsc         = choice $ zipWith (<$) "\a\b\f\n\r\t\v\\\"\'" $ map char "abfnrtv\\\"\'" 

    charAscii       = choice $ zipWith (<$) ascii $ map (try . string) $ asciicodes

    -- escape code tables
    asciicodes      = ["BS","HT","LF","VT","FF","CR","SO","SI","EM"
                      ,"FS","GS","RS","US","SP"
                      ,"NUL","SOH","STX","ETX","EOT","ENQ","ACK","BEL"
                      ,"DLE","DC1","DC2","DC3","DC4","NAK","SYN","ETB"
                      ,"CAN","SUB","ESC","DEL"]

    ascii           = ['\BS','\HT','\LF','\VT','\FF','\CR','\SO','\SI'
                      ,'\EM','\FS','\GS','\RS','\US','\SP'
                      ,'\NUL','\SOH','\STX','\ETX','\EOT','\ENQ','\ACK'
                      ,'\BEL','\DLE','\DC1','\DC2','\DC3','\DC4','\NAK'
                      ,'\SYN','\ETB','\CAN','\SUB','\ESC','\DEL']


    natFloat        = char '0' *> zeroNumFloat <|> decimalFloat

    zeroNumFloat    =   LInt <$> (oneOf "xX" *> hexadecimal <|> oneOf "oO" *> octal)
                    <|> decimalFloat
                    <|> fractFloat 0
                    <|> return (LInt 0)

    decimalFloat    = decimal >>= \n -> option (LInt n) (fractFloat n)

    fractFloat n    = LFloat <$> fractExponent (fromInteger n)

    fractExponent n = (*) <$> ((n +) <$> fraction) <*> option 1.0 exponent'
                  <|> (n *) <$> exponent'

    fraction        = foldr op 0.0 <$ char '.' <*> some digitChar <?> "fraction"
                    where
                      op d f    = (f + fromIntegral (digitToInt d))/10.0

    exponent'       = (10^^) <$ oneOf "eE" <*> ((negate <$ char '-' <|> id <$ char '+' <|> return id) <*> decimal) <?> "exponent"

