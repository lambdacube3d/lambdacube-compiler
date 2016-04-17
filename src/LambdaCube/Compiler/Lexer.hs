{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
module LambdaCube.Compiler.Lexer
    ( module LambdaCube.Compiler.Lexer
    , module ParseUtils
    ) where

import Data.Monoid
import Data.List
import Data.Char
import Data.Function
import Data.Bits
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Monad.RWS
import Control.Monad.Except
import Control.Arrow hiding ((<+>))
import Control.Applicative
import Control.DeepSeq
--import Debug.Trace

import Text.Megaparsec
import Text.Megaparsec as ParseUtils hiding (try, Message)
import Text.Megaparsec.Lexer hiding (lexeme, symbol, negate)

import LambdaCube.Compiler.Pretty hiding (braces, parens)

-------------------------------------------------------------------------------- utils

-- like 'many', but length of result is constrained by lower and upper limits
manyNM :: MonadPlus m => Int -> Int -> m t -> m [t]
manyNM a b _ | b < a || b < 0 || a < 0 = mzero
manyNM 0 0 _ = pure []
manyNM 0 n p = option [] $ (:) <$> p <*> manyNM 0 (n-1) p
manyNM k n p = (:) <$> p <*> manyNM (k-1) (n-1) p

-- try with error handling
-- see http://blog.ezyang.com/2014/05/parsec-try-a-or-b-considered-harmful/comment-page-1/#comment-6602
try_ s m = try m <?> s

-------------------------------------------------------------------------------- literals

data Lit
    = LInt    Integer
    | LChar   Char
    | LFloat  Double
    | LString String
  deriving (Eq)

instance Show Lit where
    show = \case
        LFloat x  -> show x
        LString x -> show x
        LInt x    -> show x
        LChar x   -> show x

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

        fractFloat n = LFloat <$> fractExponent (fromInteger n)

        fractExponent n = (*) <$> ((n +) <$> fraction) <*> option 1 exponent'
                      <|> (n *) <$> exponent'

        fraction = foldr op 0 <$ char '.' <*> some digitChar <?> "fraction"
          where
            op d f = (f + fromIntegral (digitToInt d))/10

        exponent' = (10^^) <$ oneOf "eE" <*> ((negate <$ char '-' <|> id <$ char '+' <|> return id) <*> decimal) <?> "exponent"

-------------------------------------------------------------------------------- source infos

-- source position without file name
data SPos = SPos
    { row    :: !Int    -- 1, 2, 3, ...
    , column :: !Int    -- 1, 2, 3, ...
    }
  deriving (Eq, Ord)

instance PShow SPos where
    pShowPrec _ (SPos r c) = pShow r <> ":" <> pShow c

toSPos :: SourcePos -> SPos
toSPos p = SPos (sourceLine p) (sourceColumn p)

getSPos = toSPos <$> getPosition

-------------

data FileInfo = FileInfo
    { fileId      :: !Int
    , filePath    :: FilePath
    , fileContent :: String
    }

instance Eq FileInfo where (==) = (==) `on` fileId
instance Ord FileInfo where compare = compare `on` fileId

instance PShow FileInfo where pShowPrec _ = text . filePath
instance Show FileInfo where show = ppShow

showPos :: FileInfo -> SPos -> Doc
showPos n p = pShow n <> ":" <> pShow p

-------------

data Range = Range !FileInfo !SPos !SPos
    deriving (Eq, Ord)

instance NFData Range where
    rnf Range{} = ()

-- short version
instance PShow Range where pShowPrec _ (Range n b e) = pShow n <+> pShow b <> "-" <> pShow e
instance Show Range where show = ppShow

-- long version
showRange :: Range -> Doc
showRange (Range n p@(SPos r c) (SPos r' c')) = vcat
     $ (showPos n p <> ":")
     : map text (drop (r - 1) $ take r' $ lines $ fileContent n)
    ++ [text $ replicate (c - 1) ' ' ++ replicate (c' - c) '^' | r' == r]

joinRange :: Range -> Range -> Range
joinRange (Range n b e) (Range n' b' e') {- | n == n' -} = Range n (min b b') (max e e')

-------------

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
    pShowPrec _ (NoSI ds) = hsep $ map text $ Set.toList ds
    pShowPrec _ (RangeSI r) = pShow r

-- long version
showSI (RangeSI r) = show $ showRange r
showSI x = ppShow x

hashPos :: FileInfo -> SPos -> Int
hashPos fn (SPos r c) = fileId fn `shiftL` 32 .|. r `shiftL` 16 .|. c

debugSI a = NoSI (Set.singleton a)

si@(RangeSI r) `validate` xs | all validSI xs && r `notElem` [r | RangeSI r <- xs]  = si
  where
    validSI RangeSI{} = True
    validSI _ = False
_ `validate` _ = mempty

sourceNameSI (RangeSI (Range n _ _)) = n

sameSource r@RangeSI{} q@RangeSI{} = sourceNameSI r == sourceNameSI q
sameSource _ _ = True

type SIName = (SI, SName)

-------------

class SourceInfo si where
    sourceInfo :: si -> SI

instance SourceInfo SI where
    sourceInfo = id

instance SourceInfo si => SourceInfo [si] where
    sourceInfo = foldMap sourceInfo

class SetSourceInfo a where
    setSI :: SI -> a -> a

-------------------------------------------------------------------------------- parser type

data ParseEnv x = ParseEnv
    { fileInfo         :: FileInfo
    , desugarInfo      :: x
    , namespace        :: Namespace
    , indentationLevel :: SPos
    }

type Parse r w = ParsecT String (RWS (ParseEnv r) [w] SPos)

runParse env p = (\(a, s, w) -> (a, w)) $ runRWS p env (SPos 1 1)

parseString fi di p s = runParse (ParseEnv fi di ExpNS (SPos 0 0)) $ runParserT p (filePath fi) s

getParseState = (,) <$> asks desugarInfo <*> ((,,,) <$> asks fileInfo <*> asks namespace <*> asks indentationLevel <*> getParserState)

parseWithState p (di, (fi, ns, l, st)) = runParse (ParseEnv fi di ns l) $ runParserT' p st

----------------------------------------------------------- indentation, white space, symbols

checkIndent = do
    (SPos r c) <- asks indentationLevel
    p@(SPos r' c') <- getSPos
    if (c' <= c && r' > r) then fail "wrong indentation" else return p

identation allowempty p = (if allowempty then option [] else id) $ do
    (SPos _ c) <- checkIndent
    (if allowempty then many else some) $ do
        pos@(SPos _ c') <- getSPos
        guard (c' == c)
        local (\e -> e {indentationLevel = pos}) p

lexemeWithoutSpace p = do
    p1 <- checkIndent
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


-------------------------------------------------------------------------------- namespace handling

data Namespace = TypeNS | ExpNS
  deriving (Eq, Show)

tick c = f <$> asks namespace
  where
    f = \case TypeNS -> switchTick c; _ -> c

switchTick ('\'': n) = n
switchTick n = '\'': n

switchNamespace = \case ExpNS -> TypeNS; TypeNS -> ExpNS
 
modifyLevel f = local $ \e -> e {namespace = f $ namespace e}

typeNS, expNS, switchNS :: Parse r w a -> Parse r w a
typeNS   = modifyLevel $ const TypeNS
expNS    = modifyLevel $ const ExpNS
switchNS = modifyLevel switchNamespace

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

patVar          = second f <$> lowerCase where
    f "_" = ""
    f x = x
lhsOperator     = lcSymbols <|> backquotedIdent
rhsOperator     = symbols <|> backquotedIdent
varId           = lowerCase <|> parens (symbols <|> backquotedIdent)
upperLower      = lowerCase <|> upperCase_ <|> parens symbols

----------------------------------------------------------- operators and identifiers

reservedOp name = lexeme $ try $ string name *> notFollowedBy opLetter

reserved name = lexeme $ try $ string name *> notFollowedBy identLetter

expect msg p i = i >>= \n -> if p n then unexpected (msg ++ " " ++ show n) else return n

identifier name = lexeme_ $ try $ expect "reserved word" (`Set.member` theReservedNames) name

operator name = lexeme_ $ try $ trCons <$> expect "reserved operator" (`Set.member` theReservedOpNames) name
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

-------------------------------------------------------------------------------- fixity handling

data FixityDef = Infix | InfixL | InfixR deriving (Eq, Show)
type Fixity = (FixityDef, Int)
type FixityMap = Map.Map SName Fixity

calcPrec
    :: (Show e, Show f, MonadError (f, f){-operator mismatch-} m)
    => (f -> e -> e -> e)
    -> (f -> Fixity)
    -> e
    -> [(f, e)]
    -> m e
calcPrec app getFixity = compileOps []
  where
    compileOps [] e [] = return e
    compileOps acc@ ~(((dir', i'), op', e'): acc') e es@ ~((op, e''): es')
        | c == LT || c == EQ && dir == dir' && dir == InfixL = compileOps acc' (app op' e' e) es
        | c == GT || c == EQ && dir == dir' && dir == InfixR = compileOps ((pr, op, e): acc) e'' es'
        | otherwise = throwError (op', op)  -- operator mismatch
      where
        pr@(dir, i) = getFixity op
        c | null es   = LT
          | null acc  = GT
          | otherwise = compare i i'

parseFixity :: Parse r w Fixity
parseFixity = do
    dir <- Infix  <$ reserved "infix"
       <|> InfixL <$ reserved "infixl"
       <|> InfixR <$ reserved "infixr"
    LInt n <- parseLit
    return (dir, fromIntegral n)

