-- contains modified Haskell source code copied from Text.Parsec.Token, see below
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
import Text.Megaparsec.Lexer hiding (lexeme, symbol, space, negate, symbol', indentBlock)
import Text.Megaparsec as Pr hiding (try, label, Message)
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
                (Either ((SName{-type name-}, Int{-num of indices-}), [(SName, Int)]{-constructors with arities-})
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

caseName (c:cs) = toLower c: cs ++ "Case"

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

showSI_ _ (NoSI ds) = unwords $ Set.toList ds
showSI_ source (RangeSI (Range s e)) = show str
  where
    startLine = sourceLine s - 1
    endline = sourceLine e - if sourceColumn e == 1 then 1 else 0
    len = endline - startLine
    str = vcat $ text (show s <> ":"){- <+> "-" <+> text (show e)-}:
               map text (take len $ drop startLine $ lines source)
            ++ [text $ replicate (sourceColumn s - 1) ' ' ++ replicate (sourceColumn e - sourceColumn s) '^' | len == 1]

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

withRange :: (SI -> a -> b) -> P a -> P b
withRange f p = appRange $ flip f <$> p

infix 9 `withRange`

type SIName = (SI, SName)

parseSIName :: P String -> P SIName
parseSIName = withRange (,)

-------------------------------------------------------------------------------- namespace handling

data Level = TypeLevel | ExpLevel
  deriving (Eq, Show)

data Namespace = Namespace
    { namespaceLevel       :: Maybe Level
    , constructorNamespace :: Bool -- True means that the case of the first letter of identifiers matters
    }
  deriving (Show)

tick = (\case TypeLevel -> switchTick; _ -> id) . fromMaybe ExpLevel . namespaceLevel

tick' c = (`tick` c) <$> namespace

switchTick ('\'': n) = n
switchTick n = '\'': n
 
modifyLevel f = local $ (first . second) $ \(Namespace l p) -> Namespace (f <$> l) p

typeNS, expNS, switchNS :: P a -> P a
typeNS   = modifyLevel $ const TypeLevel
expNS    = modifyLevel $ const ExpLevel
switchNS = modifyLevel $ \case ExpLevel -> TypeLevel; TypeLevel -> ExpLevel

ifNoCNamespace p = namespace >>= \ns -> if constructorNamespace ns then mzero else p

-------------------------------------------------------------------------------- identifiers

lcIdentStart    = satisfy $ \c -> isLower c || c == '_'
identStart      = satisfy $ \c -> isLetter c || c == '_'
identLetter     = satisfy $ \c -> isAlphaNum c || c == '_' || c == '\'' || c == '#'
lowercaseOpLetter = oneOf "!#$%&*+./<=>?@\\^|-~"
opLetter          = oneOf ":!#$%&*+./<=>?@\\^|-~"

maybeStartWith p i = i <|> (:) <$> satisfy p <*> i

lowerLetter = lcIdentStart <|> ifNoCNamespace identStart
upperLetter = satisfy isUpper <|> ifNoCNamespace identStart

upperCase, lowerCase, symbols, colonSymbols, backquotedIdent :: P SName

upperCase       = identifier (tick' =<< maybeStartWith (=='\'') ((:) <$> upperLetter <*> many identLetter)) <?> "uppercase ident"
lowerCase       = identifier ((:) <$> lowerLetter <*> many identLetter) <?> "lowercase ident"
backquotedIdent = identifier ((:) <$ char '`' <*> identStart <*> many identLetter <* char '`') <?> "backquoted ident"
symbols         = operator (some opLetter) <?> "symbols"
lcSymbols       = operator ((:) <$> lowercaseOpLetter <*> many opLetter) <?> "symbols"
colonSymbols    = operator ((:) <$> satisfy (== ':') <*> many opLetter) <?> "op symbols"
moduleName      = identifier (intercalate "." <$> sepBy1 ((:) <$> upperLetter <*> many identLetter) (char '.')) <?> "module name"

patVar          = f <$> lowerCase where
    f "_" = ""
    f x = x
lhsOperator     = lcSymbols <|> backquotedIdent
rhsOperator     = symbols <|> backquotedIdent
varId           = lowerCase <|> parens rhsOperator
upperLower      = lowerCase <|> upperCase <|> parens rhsOperator

--qIdent          = {-qualified_ todo-} (lowerCase <|> upperCase)

-------------------------------------------------------------------------------- fixity handling

data FixityDef = Infix | InfixL | InfixR deriving (Show)
type Fixity = (FixityDef, Int)
type MFixity = Maybe Fixity
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
    ns <- commaSep1 (parseSIName rhsOperator)
    return $ (,) <$> ns <*> pure (dir, i)

getFixity :: DesugarInfo -> SName -> Fixity
getFixity (fm, _) n = fromMaybe (InfixL, 9) $ Map.lookup n fm


----------------------------------------------------------- operators and identifiers

reservedOp name = lexeme $ try $ string name *> notFollowedBy opLetter

reserved name = lexeme $ try $ string name *> notFollowedBy identLetter

expect msg p i = i >>= \n -> if (p n) then unexpected (msg ++ " " ++ show n) else return n

identifier ident = lexeme $ try $ expect "reserved word" (`Set.member` theReservedNames) ident

operator oper = lexeme $ try $ trCons <$> expect "reserved operator" (`Set.member` theReservedOpNames) oper
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

checkIndent = asks snd >>= \(r, c) -> getPosition >>= \pos -> when (sourceColumn pos <= c && sourceLine pos /= r) $ fail "wrong indentation"

indentMS null p = (if null then option [] else id) $ do
    checkIndent
    lvl <- indentLevel
    (if null then many else some) $ do
        pos <- getPosition
        guard (sourceColumn pos == lvl)
        local (second $ const (sourceLine pos, sourceColumn pos)) p

lexeme' sp p = checkIndent *> p <* (getPosition >>= put) <* sp

lexeme = lexeme' whiteSpace

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


----------------------------------------------------------------------
----------------------------------------------------------------------
-- modified version of
--
-- Module      :  Text.Parsec.Token
-- Copyright   :  (c) Daan Leijen 1999-2001, (c) Paolo Martini 2007
-- License     :  BSD-style

-----------------------------------------------------------
-- Bracketing
-----------------------------------------------------------
parens p        = between (symbol "(") (symbol ")") p
braces p        = between (symbol "{") (symbol "}") p
angles p        = between (symbol "<") (symbol ">") p
brackets p      = between (symbol "[") (symbol "]") p

commaSep p      = sepBy p $ symbol ","
commaSep1 p     = sepBy1 p $ symbol ","

-----------------------------------------------------------

parseLit = lexeme $ charLiteral <|> stringLiteral <|> natFloat
  where
    -----------------------------------------------------------
    -- Chars & Strings
    -----------------------------------------------------------
    charLiteral     = LChar <$> between (char '\'')
                                      (char '\'' <?> "end of character")
                                      characterChar
                    <?> "character"

    characterChar   = charLetter <|> charEscape
                    <?> "literal character"

    charEscape      = do{ char '\\'; escapeCode }
    charLetter      = satisfy (\c -> (c /= '\'') && (c /= '\\') && (c > '\026'))



    stringLiteral   = LString <$> 
                      do{ str <- between (char '"')
                                         (char '"' <?> "end of string")
                                         (many stringChar)
                        ; return (foldr (maybe id (:)) "" str)
                        }
                      <?> "literal string"

    stringChar      =   do{ c <- stringLetter; return (Just c) }
                    <|> stringEscape
                    <?> "string character"

    stringLetter    = satisfy (\c -> (c /= '"') && (c /= '\\') && (c > '\026'))

    stringEscape    = do{ char '\\'
                        ;     do{ escapeGap  ; return Nothing }
                          <|> do{ escapeEmpty; return Nothing }
                          <|> do{ esc <- escapeCode; return (Just esc) }
                        }

    escapeEmpty     = char '&'
    escapeGap       = do{ some simpleSpace
                        ; char '\\' <?> "end of string gap"
                        }



    -- escape codes
    escapeCode      = charEsc <|> charNum <|> charAscii <|> charControl
                    <?> "escape code"

    charControl     = do{ char '^'
                        ; code <- satisfy isUpper <?> "uppercase letter"
                        ; return (toEnum (fromEnum code - fromEnum 'A'))
                        }

    charNum         = do{ code <- decimal
                                  <|> do{ char 'o'; number 8 octDigitChar }
                                  <|> do{ char 'x'; number 16 hexDigitChar }
                        ; return (toEnum (fromInteger code))
                        }

    charEsc         = choice (map parseEsc escMap)
                    where
                      parseEsc (c,code)     = do{ char c; return code }

    charAscii       = choice (map parseAscii asciiMap)
                    where
                      parseAscii (asc,code) = try (do{ string asc; return code })


    -- escape code tables
    escMap          = zip ("abfnrtv\\\"\'") ("\a\b\f\n\r\t\v\\\"\'")
    asciiMap        = zip (ascii3codes ++ ascii2codes) (ascii3 ++ ascii2)

    ascii2codes     = ["BS","HT","LF","VT","FF","CR","SO","SI","EM",
                       "FS","GS","RS","US","SP"]
    ascii3codes     = ["NUL","SOH","STX","ETX","EOT","ENQ","ACK","BEL",
                       "DLE","DC1","DC2","DC3","DC4","NAK","SYN","ETB",
                       "CAN","SUB","ESC","DEL"]

    ascii2          = ['\BS','\HT','\LF','\VT','\FF','\CR','\SO','\SI',
                       '\EM','\FS','\GS','\RS','\US','\SP']
    ascii3          = ['\NUL','\SOH','\STX','\ETX','\EOT','\ENQ','\ACK',
                       '\BEL','\DLE','\DC1','\DC2','\DC3','\DC4','\NAK',
                       '\SYN','\ETB','\CAN','\SUB','\ESC','\DEL']


    -----------------------------------------------------------
    -- Numbers
    -----------------------------------------------------------

    -- floats
    natFloat        = do{ char '0'
                        ; zeroNumFloat
                        }
                      <|> decimalFloat

    zeroNumFloat    =  do{ n <- hexadecimal <|> octal
                         ; return (LInt n)
                         }
                    <|> decimalFloat
                    <|> fractFloat 0
                    <|> return (LInt 0)

    decimalFloat    = do{ n <- decimal
                        ; option (LInt n)
                                 (fractFloat n)
                        }

    fractFloat n    = do{ f <- fractExponent n
                        ; return (LFloat f)
                        }

    fractExponent n = do{ fract <- fraction
                        ; expo  <- option 1.0 exponent'
                        ; return ((fromInteger n + fract)*expo)
                        }
                    <|>
                      do{ expo <- exponent'
                        ; return ((fromInteger n)*expo)
                        }

    fraction        = do{ char '.'
                        ; digits <- some digitChar <?> "fraction"
                        ; return (foldr op 0.0 digits)
                        }
                      <?> "fraction"
                    where
                      op d f    = (f + fromIntegral (digitToInt d))/10.0

    exponent'       = do{ oneOf "eE"
                        ; f <- sign
                        ; e <- decimal <?> "exponent"
                        ; return (power (f e))
                        }
                      <?> "exponent"
                    where
                       power e  | e < 0      = 1.0/power(-e)
                                | otherwise  = fromInteger (10^e)


    -- integers and naturals
    sign            =   (char '-' >> return negate)
                    <|> (char '+' >> return id)
                    <|> return id

    decimal         = number 10 digitChar
    hexadecimal     = do{ oneOf "xX"; number 16 hexDigitChar }
    octal           = do{ oneOf "oO"; number 8 octDigitChar  }

    number base baseDigit
        = do{ digits <- some baseDigit
            ; let n = foldl' (\x d -> base*x + toInteger (digitToInt d)) 0 digits
            ; seq n (return n)
            }


