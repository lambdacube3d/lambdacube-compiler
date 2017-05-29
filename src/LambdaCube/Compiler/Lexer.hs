{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
module LambdaCube.Compiler.Lexer
    ( module LambdaCube.Compiler.Lexer
    , module ParseUtils
    ) where

import Data.List
import Data.List.NonEmpty (fromList)
import Data.Char
import qualified Data.Set as Set
import Control.Monad.Except
import Control.Monad.RWS
import Control.Applicative
import Control.Arrow

import Text.Megaparsec hiding (State, ParseError)
import qualified Text.Megaparsec as P
import Text.Megaparsec as ParseUtils hiding (try, Message, State, ParseError)
import Text.Megaparsec.Lexer hiding (lexeme, symbol, negate)

import LambdaCube.Compiler.Pretty hiding (parens)
import LambdaCube.Compiler.DesugaredSource

-------------------------------------------------------------------------------- utils

-- try with error handling
-- see http://blog.ezyang.com/2014/05/parsec-try-a-or-b-considered-harmful/comment-page-1/#comment-6602
try_ :: String -> Parse r w a -> Parse r w a
try_ s m = try m <?> s

toSPos :: SourcePos -> SPos
toSPos p = SPos (fromIntegral $ unPos $ sourceLine p) (fromIntegral $ unPos $ sourceColumn p)

getSPos :: Parse r w SPos
getSPos = toSPos <$> getPosition

-------------------------------------------------------------------------------- literals

parseLit :: forall r w . Parse r w Lit
parseLit = lexeme (LChar <$> charLiteral <|> LString <$> stringLiteral <|> natFloat) <?> "literal"
  where
    charLiteral :: Parse r w Char
    charLiteral = between (char '\'')
                          (char '\'' <?> "end of character")
                          (char '\\' *> escapeCode <|> satisfy ((&&) <$> (> '\026') <*> (/= '\'')) <?> "character")

    stringLiteral :: Parse r w String
    stringLiteral = between (char '"')
                            (char '"' <?> "end of string")
                            (concat <$> many stringChar)
      where
        stringChar = char '\\' *> stringEscape <|> (:[]) <$> satisfy ((&&) <$> (> '\026') <*> (/= '"')) <?> "string character"

        stringEscape = [] <$ some simpleSpace <* (char '\\' <?> "end of string gap")
                   <|> [] <$ char '&'
                   <|> (:[]) <$> escapeCode

    escapeCode :: Parse r w Char
    escapeCode = choice (charEsc ++ charNum: (char '^' *> charControl): charAscii) <?> "escape code"
      where
        charControl = toEnum . (+ (-64)) . fromEnum <$> satisfy ((&&) <$> (>= 'A') <*> (<= '_')) <?> "control char"

        charNum     = toEnum . fromInteger <$> (decimal <|> char 'o' *> octal <|> char 'x' *> hexadecimal)

        charEsc   = zipWith (<$) "\a\b\t\n\v\f\r\\\"\'" $ map char "abtnvfr\\\"\'"

        charAscii = zipWith (<$) y $ try . string <$> words x
          where
            x = "NUL SOH STX ETX EOT ENQ ACK BEL BS HT LF VT FF CR SO SI DLE DC1 DC2 DC3 DC4 NAK SYN ETB CAN EM SUB ESC FS GS RS US SP DEL"
            --   0   1   2   3   4   5   6   7   8  9  10 11 12 13 14 15 16  17  18  19  20  21  22  23  24  25 26  27  28 29 30 31 32 127
            --       ^A  ^B  ^C  ^D  ^E  ^F  ^G  ^H ^I ^J ^K ^L ^M ^N ^O ^P  ^Q  ^R  ^S  ^T  ^U  ^V  ^W  ^X  ^Y ^Z  ^[  ^\ ^] ^^ ^_
            --                               \a  \b \t \n \v \f \r                                                                  ' '
            y = toEnum <$> ([0..32] ++ [127])

    natFloat :: Parse r w Lit
    natFloat = char '0' *> zeroNumFloat <|> decimalFloat
      where
        zeroNumFloat = LInt <$> (oneOf "xX" *> hexadecimal <|> oneOf "oO" *> octal)
                   <|> decimalFloat
                   <|> fractFloat 0
                   <|> return (LInt 0)

        decimalFloat = decimal >>= \n -> option (LInt n) (fractFloat n)

        fractFloat n = LFloat <$> try (fractExponent $ fromInteger n)

        fractExponent n = (*) <$> ((n +) <$> fraction) <*> option 1 exponent'
                      <|> (n *) <$> exponent'

        fraction = foldr op 0 <$ char '.' <*> some digitChar <?> "fraction"
          where
            op d f = (f + fromIntegral (digitToInt d))/10

        exponent' = (10^^) <$ oneOf "eE" <*> ((negate <$ char '-' <|> id <$ char '+' <|> return id) <*> decimal) <?> "exponent"

-------------------------------------------------------------------------------- parser type

data ParseEnv r = ParseEnv
    { fileInfo         :: FileInfo
    , desugarInfo      :: r
    , namespace        :: Namespace
    , indentationLevel :: SPos
    }

type ParseState r = (ParseEnv r, P.State String)

parseState :: FileInfo -> r -> ParseState r
parseState fi di = (ParseEnv fi di ExpNS (SPos 0 0), either (error "impossible") id $ runParser (getParserState :: Parsec Dec String (P.State String)) (filePath fi) (fileContent fi))

--type Parse r w = ReaderT (ParseEnv r) (WriterT [w] (StateT SPos (Parsec String)))
type Parse r w = RWST (ParseEnv r) [w] SPos (Parsec Dec String)

newtype ParseError = ParseErr (P.ParseError (Token String) Dec)

instance Show ParseError where
    show (ParseErr e) = parseErrorPretty e

runParse :: Parse r w a -> ParseState r -> Either ParseError (a, [w])
runParse p (env, st) = left ParseErr . snd . flip runParser' st $ evalRWST p env (error "spos")

getParseState :: Parse r w (ParseState r)
getParseState = (,) <$> ask <*> getParserState

----------------------------------------------------------- indentation, white space, symbols

getCheckedSPos :: Parse r w SPos
getCheckedSPos = do
    p <- getSPos
    p' <- asks indentationLevel
    when (p /= p' && column p <= column p') $ fail "wrong indentation"
    return p

identation :: Bool -> Parse r w t -> Parse r w [t]
identation allowempty p = (if allowempty then option [] else id) $ do
    pos' <- getCheckedSPos
    (if allowempty then many else some) $ do
        pos <- getSPos
        guard (column pos == column pos')
        local (\e -> e {indentationLevel = pos}) p

lexemeWithoutSpace :: Parse r w t -> Parse r w (SI, t)
lexemeWithoutSpace p = do
    p1 <- getCheckedSPos
    x <- p
    p2 <- getSPos
    put p2
    fi <- asks fileInfo
    return (RangeSI $ Range fi p1 p2, x)

-- TODO?: eliminate; when eliminated, the SPos in parser state can be eliminated too
appRange :: Parse r w (SI -> a) -> Parse r w a
appRange p = (\fi p1 a p2 -> a $ RangeSI $ Range fi p1 p2) <$> asks fileInfo <*> getSPos <*> p <*> getLexemeEnd

--getLexemeEnd :: _
getLexemeEnd = get

--noSpaceBefore :: _ --Parse r w a -> Parse r w a
noSpaceBefore p = try $ do
    pos <- getLexemeEnd
    x <- p
    guard $ case sourceInfo x of
        RangeSI (Range _ pos' _) -> pos == pos'
    return x

lexeme_ :: Parse r w a -> Parse r w (SI, a)
lexeme_ p = lexemeWithoutSpace p <* whiteSpace

lexeme :: Parse r w a -> Parse r w a
lexeme p = snd <$> lexeme_ p

lexemeName :: Parse r w SName -> Parse r w SIName
lexemeName p = uncurry SIName <$> lexeme_ p

symbolWithoutSpace :: String -> Parse r w (SI, String)
symbolWithoutSpace = lexemeWithoutSpace . string

symbol :: String -> Parse r w (SI, String)
symbol name = symbolWithoutSpace name <* whiteSpace

simpleSpace :: Parse r w ()
simpleSpace = skipSome (satisfy isSpace)

whiteSpace :: Parse r w ()
whiteSpace = skipMany (simpleSpace <|> oneLineComment <|> multiLineComment <?> "")
  where
    oneLineComment
        =  try (string "--" >> many (char '-') >> notFollowedBy opLetter)
        >> skipMany (satisfy (/= '\n'))

    multiLineComment = try (string "{-") *> inCommentMulti
      where
        inCommentMulti
            =   () <$ try (string "-}")
            <|> multiLineComment         *> inCommentMulti
            <|> skipSome (noneOf "{}-")  *> inCommentMulti
            <|> oneOf "{}-"              *> inCommentMulti
            <?> "end of comment"

parens, braces, brackets :: Parse r w a -> Parse r w a
parens   = between (symbol "(") (symbol ")")
braces   = between (symbol "{") (symbol "}")
brackets = between (symbol "[") (symbol "]")

commaSep, commaSep1 :: Parse r w a -> Parse r w [a]
commaSep p  = sepBy p  $ symbol ","
commaSep1 p = sepBy1 p $ symbol ","

-------------------------------------------------------------------------------- namespace handling

data Namespace = TypeNS | ExpNS
  deriving (Eq)

tick c = f <$> asks namespace
  where
    f = \case TypeNS -> switchTick c; _ -> c

switchNamespace :: Namespace -> Namespace
switchNamespace = \case ExpNS -> TypeNS; TypeNS -> ExpNS

modifyLevel :: (Namespace -> Namespace) -> Parse r w a -> Parse r w a
modifyLevel f = local $ \e -> e {namespace = f $ namespace e}

typeNS, expNS :: Parse r w a -> Parse r w a
typeNS   = modifyLevel $ const TypeNS
expNS    = modifyLevel $ const ExpNS

-------------------------------------------------------------------------------- identifiers
lowerLetter, upperLetter, identStart, identLetter, lowercaseOpLetter, opLetter :: Parse r w Char
lowerLetter       = satisfy $ (||) <$> isLower <*> (== '_')
upperLetter       = satisfy isUpper
identStart        = satisfy $ (||) <$> isLetter <*> (== '_')
identLetter       = satisfy $ (||) <$> isAlphaNum <*> (`elem` ("_\'#" :: [Char]))
lowercaseOpLetter = oneOf "!#$%&*+./<=>?@\\^|-~"
opLetter          = lowercaseOpLetter <|> char ':'

maybeStartWith :: (Char -> Bool) -> Parse r w String -> Parse r w String
maybeStartWith p i = i <|> (:) <$> satisfy p <*> i

upperCase, upperCase_, lowerCase, backquotedIdent, symbols, lcSymbols, colonSymbols, moduleName, patVar, lhsOperator, rhsOperator, varId, upperLower :: Parse r w SIName
upperCase       = identifier (tick =<< (:) <$> upperLetter <*> many identLetter) <?> "uppercase ident"
upperCase_      = identifier (tick =<< maybeStartWith (=='\'') ((:) <$> upperLetter <*> many identLetter)) <?> "uppercase ident"
lowerCase       = identifier ((:) <$> lowerLetter <*> many identLetter) <?> "lowercase ident"
backquotedIdent = identifier ((:) <$ char '`' <*> identStart <*> many identLetter <* char '`') <?> "backquoted ident"
symbols         = operator (some opLetter) <?> "symbols"
lcSymbols       = operator ((:) <$> lowercaseOpLetter <*> many opLetter) <?> "symbols"
colonSymbols    = operator ((:) <$> satisfy (== ':') <*> many opLetter) <?> "op symbols"
moduleName      = identifier (intercalate "." <$> sepBy1 ((:) <$> upperLetter <*> many identLetter) (char '.')) <?> "module name"

patVar          = f <$> lowerCase where
    f (SIName si "_") = SIName si ""
    f x = x
lhsOperator     = lcSymbols <|> backquotedIdent
rhsOperator     = symbols <|> backquotedIdent
varId           = lowerCase <|> parens (symbols <|> backquotedIdent)
upperLower      = lowerCase <|> upperCase_ <|> parens symbols

----------------------------------------------------------- operators and identifiers

reservedOp :: String -> Parse r w SI
reservedOp name = fst <$> lexeme_ (try $ string name *> notFollowedBy opLetter)

reserved :: String -> Parse r w SI
reserved name = fst <$> lexeme_ (try $ string name *> notFollowedBy identLetter)

expect :: String -> (String -> Bool) -> Parse r w String -> Parse r w String
expect msg p i = i >>= \n -> if p n then unexpected (Tokens $ fromList n) else return n

identifier :: Parse r w String -> Parse r w SIName
identifier name = lexemeName $ try $ expect "reserved word" (`Set.member` theReservedNames) name

operator :: Parse r w String -> Parse r w SIName
operator name = lexemeName $ try $ expect "reserved operator" (`Set.member` theReservedOpNames) name

theReservedOpNames :: Set.Set String
theReservedOpNames = Set.fromList ["::","..","=","\\","|","<-","->","@","~","=>"]

theReservedNames :: Set.Set String
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

parseFixity :: Parse r w Fixity
parseFixity = do
    dir <- Infix  <$ reserved "infix"
       <|> InfixL <$ reserved "infixl"
       <|> InfixR <$ reserved "infixr"
    LInt n <- parseLit
    return $ dir $ fromIntegral n

calcPrec
    :: (MonadError (f, f){-operator mismatch-} m)
    => (f -> e -> e -> e)
    -> (f -> Fixity)
    -> e
    -> [(f, e)]
    -> m e
calcPrec app getFixity = compileOps []
  where
    compileOps [] e [] = return e
    compileOps acc@ ~((op', e'): acc') e es@ ~((op, e''): es')
        | c == LT || c == EQ && isInfixL f && isInfixL f' = compileOps acc' (app op' e' e) es
        | c == GT || c == EQ && isInfixR f && isInfixR f' = compileOps ((op, e): acc) e'' es'
        | otherwise = throwError (op', op)  -- operator mismatch
      where
        isInfixR = \case InfixR{} -> True; _ -> False
        isInfixL = \case InfixL{} -> True; _ -> False
        f' = getFixity op'
        f  = getFixity op
        c | null es   = LT
          | null acc  = GT
          | otherwise = compare (precedence f) (precedence f')

