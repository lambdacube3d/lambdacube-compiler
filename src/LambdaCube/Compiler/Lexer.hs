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
module LambdaCube.Compiler.Lexer where

import Data.Monoid
import Data.Maybe
import Data.List
import Data.Char
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Arrow hiding ((<+>))
import Control.Applicative
import Control.DeepSeq

import Text.Parsec hiding ((<|>), many)
import qualified Text.ParserCombinators.Parsec.Language as Pa
import Text.Parsec.Indentation
import qualified Text.Parsec.Indentation as Pa
import Text.Parsec.Indentation.Char

import LambdaCube.Compiler.Pretty hiding (Doc, braces, parens)

-------------------------------------------------------------------------------- parser utils

-- see http://blog.ezyang.com/2014/05/parsec-try-a-or-b-considered-harmful/comment-page-1/#comment-6602
try_ s m = try m <?> s

manyNM a b _ | b < a || b < 0 || a < 0 = mzero
manyNM 0 0 _ = pure []
manyNM 0 n p = option [] $ (:) <$> p <*> manyNM 0 (n-1) p
manyNM k n p = (:) <$> p <*> manyNM (k-1) (n-1) p

-------------------------------------------------------------------------------- parser type

type P = ParsecT (IndentStream (CharIndentStream String)) SourcePos InnerP
type InnerP = WriterT [PostponedCheck] (Reader (DesugarInfo, Namespace))

type PostponedCheck = Maybe String

type DesugarInfo = (FixityMap, ConsMap)

type ConsMap = Map.Map SName{-constructor name-}
                (Either ((SName{-type name-}, Int{-num of indices-}), [(SName, Int)]{-constructors with arities-})
                        Int{-arity-})

dsInfo :: P DesugarInfo
dsInfo = asks fst

namespace :: P Namespace
namespace = asks snd


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
    = NoSI (Set String) -- no source info, attached debug info
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

sameSource r@(RangeSI {}) q@(RangeSI {}) = sourceNameSI r == sourceNameSI q
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
appRange p = (\p1 a p2 -> a $ RangeSI $ Range p1 p2) <$> getPosition <*> p <*> getState

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

tick :: Namespace -> SName -> SName
tick = (\case TypeLevel -> switchTick; _ -> id) . fromMaybe ExpLevel . namespaceLevel

switchTick ('\'': n) = n
switchTick n = '\'': n
 
modifyLevel f = local $ second $ \(Namespace l p) -> Namespace (f <$> l) p

typeNS, expNS, switchNS :: P a -> P a
typeNS   = modifyLevel $ const TypeLevel
expNS    = modifyLevel $ const ExpLevel
switchNS = modifyLevel $ \case ExpLevel -> TypeLevel; TypeLevel -> ExpLevel

ifNoCNamespace p = namespace >>= \ns -> if constructorNamespace ns then mzero else p

-------------------------------------------------------------------------------- identifiers

lcIdentStart    = satisfy $ \c -> isLower c || c == '_'
identStart      = satisfy $ \c -> isLetter c || c == '_'
identLetter     = satisfy $ \c -> isAlphaNum c || c `elem` ("_'#" :: String)
lowercaseOpLetter = oneOf "!#$%&*+./<=>?@\\^|-~"
opLetter          = oneOf ":!#$%&*+./<=>?@\\^|-~"

maybeStartWith p i = i <|> (:) <$> satisfy p <*> i

lowerLetter = lcIdentStart <|> ifNoCNamespace identStart
upperLetter = satisfy isUpper <|> ifNoCNamespace identStart

upperCase, lowerCase, symbols, colonSymbols, backquotedIdent :: P SName

upperCase       = identifier (tick <$> namespace <*> maybeStartWith (=='\'') ((:) <$> upperLetter <*> many identLetter)) <?> "uppercase ident"
lowerCase       = identifier ((:) <$> lowerLetter <*> many identLetter) <?> "lowercase ident"
backquotedIdent = identifier ((:) <$ char '`' <*> identStart <*> many identLetter <* char '`') <?> "backquoted ident"
symbols         = operator (some opLetter) <?> "symbols"
lcSymbols       = operator ((:) <$> lowercaseOpLetter <*> many opLetter) <?> "symbols"
colonSymbols    = operator ((:) <$> satisfy (== ':') <*> many opLetter) <?> "op symbols"

patVar          = f <$> lowerCase where
    f "_" = ""
    f x = x
lhsOperator     = lcSymbols <|> backquotedIdent
rhsOperator     = symbols <|> backquotedIdent
varId           = lowerCase <|> parens rhsOperator
upperLower      = lowerCase <|> upperCase <|> parens rhsOperator
moduleName      = {-qualified_ todo-} expNS upperCase

--qIdent          = {-qualified_ todo-} (lowerCase <|> upperCase)
{-
qualified_ id = do
    q <- try_ "qualification" $ upperCase' <* dot
    (N t qs n i) <- qualified_ id
    return $ N t (q:qs) n i
  <|>
    id
  where
    upperCase' = (:) <$> satisfy isUpper <*> many (satisfy isAlphaNum)
-}

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
  localIndentation Gt $ do
    i <- fromIntegral <$> natural
    ns <- commaSep1 (parseSIName rhsOperator)
    return $ (,) <$> ns <*> pure (dir, i)

getFixity :: DesugarInfo -> SName -> Fixity
getFixity (fm, _) n = fromMaybe (InfixL, 9) $ Map.lookup n fm


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

semi            = symbol ";"
comma           = symbol ","
dot             = symbol "."
colon           = symbol ":"

commaSep p      = sepBy p comma
semiSep p       = sepBy p semi

commaSep1 p     = sepBy1 p comma
semiSep1 p      = sepBy1 p semi


-----------------------------------------------------------
-- Chars & Strings
-----------------------------------------------------------
charLiteral     = lexeme (between (char '\'')
                                  (char '\'' <?> "end of character")
                                  characterChar )
                <?> "character"

characterChar   = charLetter <|> charEscape
                <?> "literal character"

charEscape      = do{ char '\\'; escapeCode }
charLetter      = satisfy (\c -> (c /= '\'') && (c /= '\\') && (c > '\026'))



stringLiteral   = lexeme (
                  do{ str <- between (char '"')
                                     (localTokenMode (const Pa.Any) (char '"' <?> "end of string"))
                                     (localTokenMode (const Pa.Any) (many stringChar))
                    ; return (foldr (maybe id (:)) "" str)
                    }
                  <?> "literal string")

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
escapeGap       = do{ many1 space
                    ; char '\\' <?> "end of string gap"
                    }



-- escape codes
escapeCode      = charEsc <|> charNum <|> charAscii <|> charControl
                <?> "escape code"

charControl     = do{ char '^'
                    ; code <- upper
                    ; return (toEnum (fromEnum code - fromEnum 'A'))
                    }

charNum         = do{ code <- decimal
                              <|> do{ char 'o'; number 8 octDigit }
                              <|> do{ char 'x'; number 16 hexDigit }
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
naturalOrFloat  = lexeme (natFloat) <?> "number"

float           = lexeme floating   <?> "float"
integer         = lexeme int        <?> "integer"
natural         = lexeme nat        <?> "natural"


-- floats
floating        = do{ n <- decimal
                    ; fractExponent n
                    }


natFloat        = do{ char '0'
                    ; zeroNumFloat
                    }
                  <|> decimalFloat

zeroNumFloat    =  do{ n <- hexadecimal <|> octal
                     ; return (Left n)
                     }
                <|> decimalFloat
                <|> fractFloat 0
                <|> return (Left 0)

decimalFloat    = do{ n <- decimal
                    ; option (Left n)
                             (fractFloat n)
                    }

fractFloat n    = do{ f <- fractExponent n
                    ; return (Right f)
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
                    ; digits <- many1 digit <?> "fraction"
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
int             = do{ f <- lexeme sign
                    ; n <- nat
                    ; return (f n)
                    }

sign            =   (char '-' >> return negate)
                <|> (char '+' >> return id)
                <|> return id

nat             = zeroNumber <|> decimal

zeroNumber      = do{ char '0'
                    ; hexadecimal <|> octal <|> decimal <|> return 0
                    }
                  <?> ""

decimal         = number 10 digit
hexadecimal     = do{ oneOf "xX"; number 16 hexDigit }
octal           = do{ oneOf "oO"; number 8 octDigit  }

number base baseDigit
    = do{ digits <- many1 baseDigit
        ; let n = foldl' (\x d -> base*x + toInteger (digitToInt d)) 0 digits
        ; seq n (return n)
        }

-----------------------------------------------------------
-- Operators & reserved ops
-----------------------------------------------------------
reservedOp name =
    lexeme $ try $
    do{ string name
      ; notFollowedBy opLetter <?> ("end of " ++ show name)
      }

operator oper =
    lexeme $ try $ trCons <$> expect "reserved operator" (`Set.member` theReservedOpNames) oper
  where
    trCons ":" = "Cons"
    trCons x = x

theReservedOpNames = Set.fromList $ Pa.reservedOpNames Pa.haskellDef

expect msg p i = i >>= \n -> if (p n) then unexpected (msg ++ " " ++ show n) else return n

-----------------------------------------------------------
-- Identifiers & Reserved words
-----------------------------------------------------------
reserved name =
    lexeme $ try $
    do{ string name
      ; notFollowedBy identLetter <?> ("end of " ++ show name)
      }

identifier ident =
    lexeme $ try $ expect "reserved word" (`Set.member` theReservedNames) ident

theReservedNames = Set.fromList $ Pa.reservedNames Pa.haskellDef


-----------------------------------------------------------
-- White space & symbols
-----------------------------------------------------------
lexeme p
    = p <* (getPosition >>= setState >> whiteSpace)

symbol name
    = lexeme (string name)

whiteSpace = ignoreAbsoluteIndentation (localTokenMode (const Pa.Any) whiteSpace')
whiteSpace' = skipMany (simpleSpace <|> oneLineComment <|> multiLineComment <?> "")

simpleSpace =
    skipMany1 (satisfy isSpace)

oneLineComment =
    do{ try (string "--" >> many (char '-') >> notFollowedBy opLetter)
      ; skipMany (satisfy (/= '\n'))
      ; return ()
      }

commentStart    = "{-"
commentEnd      = "-}"

multiLineComment =
    do { try (string commentStart)
       ; inCommentMulti
       }

inCommentMulti
    =   do{ try (string commentEnd) ; return () }
    <|> do{ multiLineComment                     ; inCommentMulti }
    <|> do{ skipMany1 (noneOf startEnd)          ; inCommentMulti }
    <|> do{ oneOf startEnd                       ; inCommentMulti }
    <?> "end of comment"
    where
      startEnd   = commentEnd ++ commentStart

