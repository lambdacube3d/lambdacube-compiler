{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
module Parser
    ( parseLC
    , application
    , appP'
    , addContext
    , P, valueDef
    , toGuardTree, guardNodes
    , eLam, pVar, eVar, eApp
    , compileCasesOld
    ) where

import Data.Function
import Data.Char
import Data.List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Monoid
import Control.Applicative (some,liftA2,Alternative())
import Control.Arrow
import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Trans
import qualified Text.Parsec.Indentation.Char as I
import Text.Parsec.Indentation
import Text.Parsec hiding (optional)

import qualified Pretty as P
import Type
import ParserUtil

-- import Debug.Trace

-------------------------------------------------------------------------------- parser combinators

type P = P_ ()      -- no state for the parser

-- see http://blog.ezyang.com/2014/05/parsec-try-a-or-b-considered-harmful/comment-page-1/#comment-6602
try' s m = try m <?> s

qualified_ id = do
    q <- try' "qualification" $ upperCase' <* dot
    (N t qs n i) <- qualified_ id
    return $ N t (q:qs) n i
  <|>
    id
  where
    upperCase' = (:) <$> satisfy isUpper <*> many (satisfy isAlphaNum)

-------------------------------------------------------------------------------- position handling

-- compose ranges through getTag
infixl 9 <->
a <-> b = getTag a `mappend` getTag b

addPos :: (Range -> a -> b) -> P a -> P b
addPos f m = do
    p1 <- position
    a <- m
    p2 <- positionBeforeSpace
    return $ f (Range p1 p2) a

addDPos = addPos (,)
addPPos = addPos PatR
addEPos = addPos ExpR

-------------------------------------------------------------------------------- identifiers

check msg p m = try' msg $ do
    x <- m
    if p x then return x else fail $ msg ++ " expected"

upperCase, lowerCase, symbols, colonSymbols :: P String
upperCase = check "uppercase ident" (isUpper . head) $ ident lcIdents
lowerCase = check "lowercase ident" (isLower . head) (ident lcIdents) <|> try (('_':) <$ char '_' <*> ident lcIdents)
symbols   = check "symbols" ((/=':') . head) $ ident lcOps
colonSymbols = "Cons" <$ operator ":" <|> check "symbols" ((==':') . head) (ident lcOps)

--------------------------------------------------------------------------------

typeConstructor, upperCaseIdent, typeVar, var, varId, qIdent, operator', conOperator, moduleName :: P Name
typeConstructor = upperCase <&> \i -> TypeN' i (P.text i)
upperCaseIdent  = upperCase <&> ExpN
typeVar         = (\p i -> TypeN' i $ P.text $ i ++ show p) <$> position <*> lowerCase
var             = (\p i -> ExpN' i $ P.text $ i ++ show p) <$> position <*> lowerCase
qIdent          = qualified_ (var <|> upperCaseIdent)
conOperator     = (\p i -> ExpN' i $ P.text $ i ++ show p) <$> position <*> colonSymbols
varId           = var <|> parens operator'
backquotedIdent = try' "backquoted" $ char '`' *> (ExpN <$> ((:) <$> satisfy isAlpha <*> many (satisfy isAlphaNum))) <* char '`' <* whiteSpace
operator'       = (\p i -> ExpN' i $ P.text $ i ++ show p) <$> position <*> symbols
              <|> conOperator
              <|> backquotedIdent
moduleName      = qualified_ upperCaseIdent

-------------------------------------------------------------------------------- literals

literal :: P Lit
literal
    =   LFloat <$> try double
    <|> LInt <$> try natural
    <|> LChar <$> charLiteral
    <|> LString <$> stringLiteral

-------------------------------------------------------------------------------- patterns

getP (PatR _ x) = x
appP' (PCon' r n []) ps = PCon' r n ps
appP' p ps = error $ "appP' " ++ P.ppShow (p, ps)

---------------------

pattern', patternAtom :: P PatR
pattern'
    = addPPos $ PPrec_ <$> pat <*> ((op >>= pat') <|> return [])
  where
    pat' o = do
            (e, o') <- try $ (,) <$> pat <*> op
            es <- pat' o'
            return $ (o, e): es
        <|> do
            e <- pattern'
            return [(o, e)]

    pat = addPPos (PCon_ TWildcard <$> upperCaseIdent <*> many patternAtom) <|> patternAtom

    op = addPPos $ PCon_ TWildcard <$> conOperator <*> pure []

patternAtom = addPPos $
        PLit_ <$> literal
    <|> PAt_ <$> try' "at pattern'" (var <* operator "@") <*> patternAtom
    <|> PVar_ TWildcard <$> var
    <|> Wildcard_ TWildcard <$ operator "_"
    <|> PCon_ TWildcard <$> upperCaseIdent <*> pure []
    <|> pTuple <$> parens (commaSep1 pattern')
    <|> PRecord_ <$> braces (commaSep $ (,) <$> var <* colon <*> pattern')
    <|> getP . mkList <$> brackets (commaSep pattern')
  where
    mkList = foldr cons nil
      where
        nil = PCon' mempty (ExpN "Nil") []
        cons a b = PCon' mempty (ExpN "Cons") [a, b]

    pTuple [PatR _ x] = x
    pTuple xs = PTuple_ xs

-------------------------------------------------------------------------------- expressions

eTuple p [ExpR _ x] = ExpR p x
eTuple p xs = ExpR p $ ETuple_ xs
eRecord p xs = ExpR p $ ERecord_ xs
eNamedRecord p n xs = ExpR p $ ENamedRecord_ n xs
eVar p n = ExpR p $ EVar_ TWildcard n
eLam p e = ExpR (p <-> e) $ ELam_ Nothing p e
eApp a b = ExpR (a <-> b) $ EApp_ TWildcard a b
eTyping a b = ExpR (a <-> b) $ ETypeSig_ a b
eTyApp a b = ExpR (a <-> b) $ ETyApp_ TWildcard a b

application :: [ExpR] -> ExpR
application = foldl1 eApp

eLet :: DefinitionR -> ExpR -> ExpR
eLet (r, DValueDef False (ValueDef _{-TODO-} a b)) x = ExpR (r `mappend` getTag x) $ ELet_ a b x
eLet a b = error $ "eLet: " ++ P.ppShow a

eLets :: [DefinitionR] -> ExpR -> ExpR
eLets l a = foldr ($) a $ map eLet $ groupDefinitions l

desugarSwizzling :: [Char] -> ExpR -> ExpR
desugarSwizzling cs e = case map trC cs of
    [c] -> c
    cs -> application $ eVar mempty (vecName $ length cs): cs
  where
    trC c = eApp (expR $ EFieldProj_ TWildcard $ ExpN [tr c]) e
    vecName n = ExpN $ "V" ++ show n
    tr = \case
        'r' -> 'x'
        'g' -> 'y'
        'b' -> 'z'
        'a' -> 'w'
        c   -> c

---------------------

withTypeSig p = do
    e <- p 
    t <- optional $ operator "::" *> polytype
    return $ maybe e (eTyping e) t

expression :: P ExpR
expression = withTypeSig $
        ifthenelse
    <|> caseof
    <|> letin
    <|> lambda
    <|> eApp <$> addPos eVar (const (ExpN "negate") <$> operator "-") <*> expressionOpAtom -- TODO: precedence
    <|> expressionOpAtom
 where
    lambda :: P ExpR
    lambda = (\(ps, e) -> foldr eLam e ps) <$> (operator "\\" *> ((,) <$> many patternAtom <* operator "->" <*> expression))

    ifthenelse :: P ExpR
    ifthenelse = addPos (\r (a, b, c) -> eApp (eApp (eApp (eVar r (ExpN "PrimIfThenElse")) a) b) c) $
        (,,) <$ keyword "if" <*> expression <* keyword "then" <*> expression <* keyword "else" <*> expression

    caseof :: P ExpR
    caseof = addPos (uncurry . compileCases) $ (,)
        <$ keyword "case" <*> expression <* keyword "of"
        <*> localIndentation Ge (localAbsoluteIndentation $ some $ (,) <$> pattern' <*> localIndentation Gt (whereRHS $ operator "->"))

    letin :: P ExpR
    letin = eLets
        <$ keyword "let" <*> localIndentation Ge (localAbsoluteIndentation $ some valueDef)
        <* keyword "in" <*> expression

    expressionOpAtom = addEPos $ EPrec_ <$> exp <*> ((op >>= expression') <|> return [])
      where
        expression' o = do
                (e, o') <- try $ (,) <$> exp <*> op
                es <- expression' o'
                return $ (o, e): es
            <|> (:[]) . (,) o <$> expression

        exp = application <$> some expressionAtom

        op = addPos eVar operator'

generator :: P (ExpR -> ExpR)
generator = do
    pat <- try $ pattern' <* operator "<-"
    exp <- expression
    let v = ExpN "genVar"
        pv = pVar mempty v
        ev = eVar mempty v
    return $ \e -> application [ eVar mempty $ ExpN "concatMap"
                               , eLam pv $ funAlts0 $ toGuardTree [ev]
                                    [([toParPat pat], GuardExp e), ([mempty], GuardExp $ eVar mempty (ExpN "Nil"))]
                               , exp]

letdecl :: P (ExpR -> ExpR)
letdecl = keyword "let" *> (eLets . (:[]) <$> valueDef)

boolExpression :: P (ExpR -> ExpR)
boolExpression = do
    pred <- expression
    return $ \e -> application [eVar mempty $ ExpN "PrimIfThenElse", pred, e, eVar mempty (ExpN "Nil")]

listComprExp :: P ExpR
listComprExp = foldr ($) <$>
    try' "List comprehension" (operator "[" *> (eApp (eVar mempty $ ExpN "singleton") <$> expression) <* operator "|") <*>
    commaSep1 (generator <|> letdecl <|> boolExpression) <* operator "]"

listFromTo :: P ExpR
listFromTo = do
    e1 <- try $ do
      operator "["
      e1 <- expression
      operator ".."
      return e1
    e2 <- expression
    operator "]"
    return $ application [eVar mempty $ ExpN "fromTo", e1, e2]

expressionAtom :: P ExpR
expressionAtom = do
    e <- expressionAtom_
    sw <- optional $ char '%' *> some (satisfy (`elem` ("xyzwrgba" :: [Char]))) <* whiteSpace
    ts <- many $ do
        operator "@"
        typeAtom
    return $ foldl eTyApp (maybe id desugarSwizzling sw e) ts
  where
    expressionAtom_ :: P ExpR
    expressionAtom_ =
            listFromTo
        <|> listComprExp
        <|> listExp
        <|> addEPos (eLit <$> literal)
        <|> recordExp
        <|> recordExp'
        <|> recordFieldProjection
        <|> addPos eVar qIdent
        <|> addPos eTuple (parens $ commaSep expression)
     where
      recordExp :: P ExpR
      recordExp = addPos eRecord $ braces $ commaSep $ (,) <$> var <* colon <*> expression

      recordExp' :: P ExpR
      recordExp' = try $ addPos (uncurry . eNamedRecord) $ (,) <$> upperCaseIdent <*> braces (commaSep $ (,) <$> var <* keyword "=" <*> expression)

      recordFieldProjection :: P ExpR
      recordFieldProjection = try $ flip eApp <$> addPos eVar var <*>
            addEPos (EFieldProj_ TWildcard <$ {-runUnspaced $-} dot <*> {-Unspaced-} var)

      eLit l@LInt{} = EApp_ TWildcard (eVar mempty (ExpN "fromInt")) $ expR $ ELit_ l
      eLit l = ELit_ l

      listExp :: P ExpR
      listExp = addPos (\p -> foldr cons (nil p)) $ brackets $ commaSep expression
        where
          nil r = eVar (r{-TODO-}) $ ExpN "Nil"
          cons a b = eApp (eApp (eVar mempty{-TODO-} (ExpN "Cons")) a) b

-------------------------------------------------------------------------------- types

tArr t a = ExpR (t <-> a) $ Forall_ Visible Nothing t a
tArrH t a = ExpR (t <-> a) $ Forall_ Hidden Nothing t a
addContext :: [ExpR] -> ExpR -> ExpR
addContext cs e = foldr tArrH e cs

---------------------

typeVarKind :: P (Name, ExpR)
typeVarKind =
      parens ((,) <$> typeVar <* operator "::" <*> monotype)
  <|> (,) <$> typeVar <*> addEPos (pure Star_)

context :: P [ExpR]   -- TODO
context = try' "type context" $ ((:[]) <$> tyC <|> parens (commaSep tyC)) <* operator "=>"
  where
    tyC = 
        (   addEPos (CEq_ <$> try (monotype <* operator "~") <*> (mkTypeFun <$> monotype))
        <|> foldl1 eApp <$> ((:) <$> (addEPos $ TCon_ TWildcard <$> typeConstructor) <*> many typeAtom)
        )

    mkTypeFun e = case getArgs e of (n, reverse -> ts) -> TypeFun n ts
      where
        getArgs = \case
            ExpR _ (TCon_ _ n) -> (n, [])
            ExpR _ (EApp_ _ x y) -> id *** (y:) $ getArgs x
            x -> error $ "mkTypeFun: " ++ P.ppShow x

polytype :: P ExpR
polytype =
    do  vs <- keyword "forall" *> some (addDPos typeVarKind) <* dot
        t <- polytype
        return $ foldr (\(p, (v, k)) t -> ExpR (p <> getTag t) $ Forall_ Visible (Just v) k t) t vs
  <|> addContext <$> context <*> polytype
  <|> monotype

polytypeCtx :: P [(Maybe Name, ExpR)]
polytypeCtx =
    do  vs <- keyword "forall" *> some typeVarKind <* dot
        t <- polytypeCtx
        return $ map (Just *** id) vs ++ t
  <|> (++) <$> (map ((,) Nothing) <$> context) <*> polytypeCtx
  <|> return []

monotype :: P ExpR
monotype = do
    t <- foldl1 eApp <$> some typeAtom
    maybe t (tArr t) <$> optional (operator "->" *> polytype)

typeAtom :: P ExpR
typeAtom = addEPos $
        typeRecord
    <|> Star_ <$ operator "*"
    <|> EVar_ TWildcard <$> typeVar
    <|> ELit_ <$> (LNat . fromIntegral <$> natural <|> literal)
    <|> TCon_ TWildcard <$> typeConstructor
    <|> tTuple <$> parens (commaSep monotype)
    <|> EApp_ TWildcard (expR $ TCon_ TWildcard (TypeN' "List" "List")) <$> brackets monotype
  where
    tTuple [ExpR _ t] = t
    tTuple ts = TTuple_ ts

    typeRecord = undef "trec" $ do
        braces (commaSep1 typeSignature >> optional (operator "|" >> void typeVar))
      where
        undef msg = (const (error $ "not implemented: " ++ msg) <$>)

-------------------------------------------------------------------------------- function and value definitions

compileCasesOld :: Range -> ExpR -> [(PatR, Exp)] -> ExpR
compileCasesOld r e rs = eApp (alts 1 [eLam p r | (p, r) <- rs]) e
  where
    alts :: Int -> [ExpR] -> ExpR
    alts _ [e] = e
    alts i es = foldr eLam (ExpR (foldMap getTag es) $ EAlts_ [foldl eApp e vs | e <- es]) ps where
        ps = take i $ map (pVar mempty . ExpN . ("alt" ++) . show) [1..]
        vs = take i $ map (eVar mempty . ExpN . ("alt" ++) . show) [1..]

pVar r x = PatR r $ PVar_ TWildcard x

whereToBinds :: WhereBlock -> Binds Exp
whereToBinds = map eLet . groupDefinitions
  where
    eLet (r, DValueDef False (ValueDef _{-TODO-} a b)) = (a, b)
    eLet a = error $ "eLet: " ++ P.ppShow a

compileWhereRHS :: WhereRHS -> GuardTree Exp
compileWhereRHS (WhereRHS r md) = maybe x (\w -> GuardWhere (whereToBinds w) x) md where
    x = case r of
        NoGuards e -> GuardExp e
        Guards r{-TODO-} gs -> GuardAlts [GuardCon b (ConName $ ExpN "True") [] $ GuardExp e | (b, e) <- gs]

toParPat :: Pat -> ParPat Exp
toParPat (Pat p) = case p of
    PLit_ l ->  [PatLit l]
    PTuple_ ps -> [PatCon (TupleName $ length ps) $ map toParPat ps]
    PRecord_ rs -> error $ "toParPat: record " ++ P.ppShow rs --[(Name, b)]
    PVar_ t v -> [PatVar v]
    PCon_ t c ps -> [PatCon (ConName c) $ map toParPat ps]
    PAt_ v p -> PatVar v: toParPat p
    Wildcard_ _ -> []
    PPrec_ p ps -> [PatPrec (toParPat p) $ map (toParPat *** toParPat) ps]

funAlts0 :: GuardTree Exp -> Exp
funAlts0 t = FunAlts 0 [([], t)]

guardNodes :: [(Exp, ParPat Exp)] -> GuardTree Exp -> GuardTree Exp
guardNodes [] l = l
guardNodes ((v, ws): vs) e = GuardPat v ws $ guardNodes vs e

toGuardTree :: [Exp] -> [([ParPat Exp], GuardTree Exp)] -> GuardTree Exp
toGuardTree vs cs
    = GuardAlts [guardNodes (zip vs ps) rhs | (ps, rhs) <- cs]

compileCases :: Range -> ExpR -> [(PatR, WhereRHS)] -> ExpR
compileCases r{-TODO-} e rs = funAlts0 $ toGuardTree [e] [([toParPat p], compileWhereRHS r) | (p, r) <- rs]

groupDefinitions :: [DefinitionR] -> [DefinitionR]
groupDefinitions defs = concatMap mkDef . map compileRHS . groupBy (f `on` snd) $ defs
  where
    f (h -> Just x) (h -> Just y) = x == y
    f _ _ = False

    h ( (PreValueDef (_, n) _ _)) = Just n
    h ( (DValueDef _ (ValueDef _ p _))) = name p        -- TODO
    h ( (DTypeSig (TypeSig n _))) = Just n
    h _ = Nothing

    name (PVar' _ n) = Just n
    name _ = Nothing

    mkDef = \case
--         (r, PreInstanceDef c t ds) -> [(r, InstanceDef c t [v | (r, DValueDef v) <- groupDefinitions ds])]
         x -> [x]

    compileRHS :: [DefinitionR] -> DefinitionR
    compileRHS ds = case ds of
        ((r1, DTypeSig (TypeSig _ t)): ds@((r2, PreValueDef{}): _)) -> (r1 `mappend` r2, mkAlts (`eTyping` t) ds)
        ds@((r, PreValueDef{}): _) -> (r, mkAlts id ds)
        [x] -> x
      where
        mkAlts f ds@( (_, PreValueDef (r, n) _ _): _)
            = DValueDef False $ ValueDef True (PVar' r n) $ f $ FunAlts i als
          where
            i = allSame $ map (length . fst) als
            allSame (n:ns) | all (==n) ns = n
                           | otherwise = error $ "function alternatives have different arity: " ++ P.ppShow (n:ns)
            als = [(map toParPat pats, compileWhereRHS rhs) |  (_, PreValueDef _ pats rhs) <- ds]

---------------------

valueDef :: P DefinitionR
valueDef = addDPos $
   (do
    try' "function definition" $ do
      n <- addDPos varId
      localIndentation Gt $ do
        pats <- many patternAtom
        lookAhead $ operator "=" <|> operator "|"
        return $ PreValueDef n pats
   <|> do
    try' "value definition" $ do
      n <- pattern'
      n2 <- optional $ do
          op <- addDPos operator'
          n2 <- pattern'
          return (op, n2)
      localIndentation Gt $ do
        lookAhead $ operator "=" <|> operator "|"
        return $ case n2 of
            Nothing -> \e -> DValueDef False $ ValueDef True n $ funAlts0 $ compileWhereRHS e
            Just (op, n2) -> PreValueDef op [n, n2]
    )
 <*> localIndentation Gt (whereRHS $ operator "=")

whereRHS :: P () -> P WhereRHS
whereRHS delim =
    WhereRHS <$>
    (   NoGuards <$ delim <*> expression
    <|> addPos Guards (many $ (,) <$ operator "|" <*> expression <* delim <*> expression)
    ) <*>
    (   Just . concat <$> (keyword "where" *> localIndentation Ge (localAbsoluteIndentation $ some $ (:[]) <$> valueDef <|> typeSignature))
    <|> return Nothing
    )

-------------------------------------------------------------------------------- class and instance definitions

whereBlock p = fromMaybe [] <$> optional (keyword "where" *> localIndentation Ge (localAbsoluteIndentation $ many p))

classDef :: P DefinitionR
classDef = addDPos $ do
  keyword "class"
  localIndentation Gt $ ClassDef
    <$> (fromMaybe [] <$> optional context)
    <*> typeConstructor
    <*> many typeVarKind
    <*> (whereBlock typeSignature <&> \ds -> [d | (_, DTypeSig d) <- concat ds])

instanceDef :: P DefinitionR
instanceDef = addDPos $ do
  keyword "instance"
  localIndentation Gt $ InstanceDef
    <$> (fromMaybe [] <$> optional context)
    <*> typeConstructor
    <*> many typeAtom
    <*> (whereBlock valueDef <&> \ds -> [v | (r, DValueDef False v) <- groupDefinitions ds])

-------------------------------------------------------------------------------- data definition

fields =  braces (commaSep $ FieldTy <$> (Just <$> ((,) <$> varId <*> pure False)) <* keyword "::" <* optional (operator "!") <*> polytype)
      <|> many (FieldTy Nothing <$ optional (operator "!") <*> typeAtom)

fields' =  braces (commaSep $ FieldTy <$> (Just <$> ((,) <$> varId <*> pure False)) <* keyword "::" <* optional (operator "!") <*> polytype)
      <|> many (try $ FieldTy Nothing <$ optional (operator "!") <*> ty <* operator "->")
 where
    ty = foldl1 eApp <$> some typeAtom

dataDef :: P DefinitionR
dataDef = addDPos $ do
 keyword "data"
 localIndentation Gt $ do
  tc <- typeConstructor
  tvs <- many typeVarKind
  do
    do
      keyword "where"
      ds <- localIndentation Ge $ localAbsoluteIndentation $ many $ do
        cs <- commaSep1 (addDPos upperCaseIdent)
        localIndentation Gt $ do
            t <- ConDef' <$ operator "::" <*> polytypeCtx <*> fields' <*> monotype
            return [(p, (c, t)) | (p, c) <- cs]
      return $ GADT tc tvs $ concat ds
   <|>
    do
      operator "="
      ds <- sepBy (addDPos $ ConDef <$> upperCaseIdent <*> fields) $ operator "|"
      derivingStm
      return $ DDataDef tc tvs ds
  where
    derivingStm = optional $ keyword "deriving" <* (void typeConstructor <|> void (parens $ commaSep typeConstructor))

-------------------------------------------------------------------------------- type synonym

typeSynonym :: P ()
typeSynonym = void $ do
  keyword "type"
  localIndentation Gt $ do
    typeConstructor
    many typeVar
    operator "="
    void polytype

-------------------------------------------------------------------------------- type family

typeFamily :: P DefinitionR
typeFamily = addDPos $ do
    try $ keyword "type" >> keyword "family"
    tc <- typeConstructor
    tvs <- many typeVarKind
    res <- optional $ do
        operator "::"
        monotype
    return $ TypeFamilyDef tc tvs $ fromMaybe (expR Star_) res

-------------------------------------------------------------------------------- type signature

typeSignature :: P [DefinitionR]
typeSignature = do
  ns <- try' "type signature" $ do
    ns <- commaSep1 varId
    localIndentation Gt $ operator "::"
    return ns
  t <- localIndentation Gt $ do
    optional (operator "!") *> polytype
  return [(mempty, DTypeSig $ TypeSig n t) | n <- ns]

axiom :: P [DefinitionR]
axiom = do
  ns <- try' "axiom" $ do
    ns <- commaSep1 (varId <|> upperCaseIdent)
    localIndentation Gt $ operator "::"
    return ns
  t <- localIndentation Gt $ do
    optional (operator "!") *> polytype
  return [(mempty, DAxiom $ TypeSig n t) | n <- ns]

-------------------------------------------------------------------------------- fixity declarations

fixityDef :: P [DefinitionR]
fixityDef = do
  dir <-    Nothing      <$ keyword "infix" 
        <|> Just FDLeft  <$ keyword "infixl"
        <|> Just FDRight <$ keyword "infixr"
  localIndentation Gt $ do
    i <- natural
    ns <- commaSep1 (addDPos operator')
    return [(p, PrecDef n (dir, fromIntegral i)) | (p, n) <- ns]

-------------------------------------------------------------------------------- modules

importDef :: P Name
importDef = do
  keyword "import"
  optional $ keyword "qualified"
  n <- moduleName
  let importlist = parens (commaSep (varId <|> upperCaseIdent))
  optional $
        (keyword "hiding" >> importlist)
    <|> importlist
  optional $ do
    keyword "as"
    moduleName
  return n

parseExtensions :: P [Extension]
parseExtensions = do
    try (string "{-#")
    simpleSpace
    string "LANGUAGE"
    simpleSpace
    s <- commaSep ext
    simpleSpace
    string "#-}"
    simpleSpace
    return s
  where
    simpleSpace = skipMany (satisfy isSpace)

    ext = do
        s <- some $ satisfy isAlphaNum
        case s of
            "NoImplicitPrelude" -> return NoImplicitPrelude
            _ -> fail $ "language extension expected instead of " ++ s

export :: P Export
export =
        ExportModule <$ keyword "module" <*> moduleName
    <|> ExportId <$> varId

moduleDef :: FilePath -> P ModuleR
moduleDef fname = do
  exts <- concat <$> many parseExtensions
  whiteSpace
  header <- optional $ do
    modn <- keyword "module" *> moduleName
    exps <- optional (parens $ commaSep export)
    keyword "where"
    return (modn, exps)
  -- localAbsoluteIndentation $ do
  do
    idefs <- many importDef
    -- TODO: unordered definitions
    defs <- groupDefinitions . concat <$> many
        (   (:[]) <$> dataDef
        <|> concat <$ keyword "builtins" <*> localIndentation Gt (localAbsoluteIndentation $ many axiom)
        <|> typeSignature
        <|> (:[]) <$> typeFamily
        <|> const [] <$> typeSynonym
        <|> (:[]) <$> classDef
        <|> (:[]) <$> valueDef
        <|> fixityDef
        <|> (:[]) <$> instanceDef
        )
    return $ Module
      { extensions = exts
      , moduleImports = if NoImplicitPrelude `elem` exts
            then idefs
            else ExpN "Prelude": idefs
      , moduleExports = join $ snd <$> header
      , definitions   = defs
      }

--------------------------------------------------------------------------------

parseLC :: MonadError ErrorMsg m => FilePath -> String -> m ModuleR
parseLC fname src = either throwParseError return . runParser' fname (moduleDef fname) $ src

