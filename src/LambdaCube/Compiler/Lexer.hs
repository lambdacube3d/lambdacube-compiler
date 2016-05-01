{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
module LambdaCube.Compiler.Lexer
    ( module LambdaCube.Compiler.Lexer
    , module ParseUtils
    ) where

import Data.List
import Data.Char
import qualified Data.Set as Set
import Control.Monad.Except
import Control.Monad.RWS
import Control.Applicative
--import Debug.Trace

import Text.Megaparsec hiding (State)
import qualified Text.Megaparsec as P
import Text.Megaparsec as ParseUtils hiding (try, Message, State)
import Text.Megaparsec.Lexer hiding (lexeme, symbol, negate)

import LambdaCube.Compiler.Pretty hiding (parens)
import LambdaCube.Compiler.DesugaredSource

-------------------------------------------------------------------------------- utils

-- try with error handling
-- see http://blog.ezyang.com/2014/05/parsec-try-a-or-b-considered-harmful/comment-page-1/#comment-6602
try_ s m = try m <?> s

toSPos :: SourcePos -> SPos
toSPos p = SPos (sourceLine p) (sourceColumn p)

getSPos = toSPos <$> getPosition

-------------------------------------------------------------------------------- literals

parseLit :: Parse r w Lit
parseLit = lexeme (LChar <$> charLiteral <|> LString <$> stringLiteral <|> natFloat) <?> "literal"
  where
    charLiteral = between (char '\'')
                          (char '\'' <?> "end of character")
                          (char '\\' *> escapeCode <|> satisfy ((&&) <$> (> '\026') <*> (/= '\'')) <?> "character")

    stringLiteral = between (char '"')
                            (char '"' <?> "end of string")
                            (concat <$> many stringChar)
      where
        stringChar = char '\\' *> stringEscape <|> (:[]) <$> satisfy ((&&) <$> (> '\026') <*> (/= '"')) <?> "string character"

        stringEscape = [] <$ some simpleSpace <* (char '\\' <?> "end of string gap")
                   <|> [] <$ char '&'
                   <|> (:[]) <$> escapeCode

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
parseState fi di = (ParseEnv fi di ExpNS (SPos 0 0), either (error "impossible") id $ runParser getParserState (filePath fi) (fileContent fi))

--type Parse r w = ReaderT (ParseEnv r) (WriterT [w] (StateT SPos (Parsec String)))
type Parse r w = RWST (ParseEnv r) [w] SPos (Parsec String)

runParse :: Parse r w a -> ParseState r -> Either ParseError (a, [w])
runParse p (env, st) = snd . flip runParser' st $ evalRWST p env (error "spos")

getParseState :: Parse r w (ParseState r)
getParseState = (,) <$> ask <*> getParserState

----------------------------------------------------------- indentation, white space, symbols

getCheckedSPos = do
    p@(SPos r c) <- getSPos
    SPos ri ci <- asks indentationLevel
    when (c <= ci && r > ri) $ fail "wrong indentation"
    return p

identation allowempty p = (if allowempty then option [] else id) $ do
    SPos _ cbase <- getCheckedSPos
    (if allowempty then many else some) $ do
        pos@(SPos _ c) <- getSPos
        guard (c == cbase)
        local (\e -> e {indentationLevel = pos}) p

lexemeWithoutSpace p = do
    p1 <- getCheckedSPos
    x <- p
    p2 <- getSPos
    put p2
    fi <- asks fileInfo
    return (RangeSI $ Range fi p1 p2, x)

-- TODO?: eliminate; when eliminated, the SPos in parser state can be eliminated too
appRange :: Parse r w (SI -> a) -> Parse r w a
appRange p = (\fi p1 a p2 -> a $ RangeSI $ Range fi p1 p2) <$> asks fileInfo <*> getSPos <*> p <*> get

lexeme_ p = lexemeWithoutSpace p <* whiteSpace

lexeme p = snd <$> lexeme_ p

lexemeName p = uncurry SIName <$> lexeme_ p

symbolWithoutSpace = lexemeWithoutSpace . string

symbol name = symbolWithoutSpace name <* whiteSpace

simpleSpace = skipSome (satisfy isSpace)

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

parens   = between (symbol "(") (symbol ")")
braces   = between (symbol "{") (symbol "}")
brackets = between (symbol "[") (symbol "]")

commaSep p  = sepBy p  $ symbol ","
commaSep1 p = sepBy1 p $ symbol ","

-------------------------------------------------------------------------------- namespace handling

data Namespace = TypeNS | ExpNS
  deriving (Eq)

tick c = f <$> asks namespace
  where
    f = \case TypeNS -> switchTick c; _ -> c

switchNamespace = \case ExpNS -> TypeNS; TypeNS -> ExpNS
 
modifyLevel f = local $ \e -> e {namespace = f $ namespace e}

typeNS, expNS :: Parse r w a -> Parse r w a
typeNS   = modifyLevel $ const TypeNS
expNS    = modifyLevel $ const ExpNS

-------------------------------------------------------------------------------- identifiers

lowerLetter       = satisfy $ (||) <$> isLower <*> (== '_')
upperLetter       = satisfy isUpper
identStart        = satisfy $ (||) <$> isLetter <*> (== '_')
identLetter       = satisfy $ (||) <$> isAlphaNum <*> (`elem` ("_\'#" :: [Char]))
lowercaseOpLetter = oneOf "!#$%&*+./<=>?@\\^|-~"
opLetter          = lowercaseOpLetter <|> char ':'

maybeStartWith p i = i <|> (:) <$> satisfy p <*> i

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

reservedOp name = lexeme $ try $ string name *> notFollowedBy opLetter

reserved name = lexeme $ try $ string name *> notFollowedBy identLetter

expect msg p i = i >>= \n -> if p n then unexpected (msg ++ " " ++ show n) else return n

identifier name = lexemeName $ try $ expect "reserved word" (`Set.member` theReservedNames) name

operator name = lexemeName $ try $ trCons <$> expect "reserved operator" (`Set.member` theReservedOpNames) name
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

