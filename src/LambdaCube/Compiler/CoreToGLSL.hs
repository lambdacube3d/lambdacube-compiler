{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
module LambdaCube.Compiler.CoreToGLSL
    ( genVertexGLSL
    , genFragmentGLSL
    ) where

import Debug.Trace

import Data.Char
import Data.List
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

import Control.Arrow hiding ((<+>))
import Control.Monad.Writer

import LambdaCube.Compiler.Pretty hiding (parens)
import LambdaCube.Compiler.CGExp
import IR(Backend(..))
{-
mangleIdent :: String -> String
mangleIdent n = '_': concatMap encodeChar n
  where
    encodeChar = \case
        c | isAlphaNum c -> [c]
        '_'  -> "__"
        '.'  -> "_dot"
        '$'  -> "_dollar"
        '~'  -> "_tilde"
        '='  -> "_eq"
        '<'  -> "_less"
        '>'  -> "_greater"
        '!'  -> "_bang"
        '#'  -> "_hash"
        '%'  -> "_percent"
        '^'  -> "_up"
        '&'  -> "_amp"
        '|'  -> "_bar"
        '*'  -> "_times"
        '/'  -> "_div"
        '+'  -> "_plus"
        '-'  -> "_minus"
        ':'  -> "_colon"
        '\\' -> "_bslash"
        '?'  -> "_qmark"
        '@'  -> "_at"
        '\'' -> "_prime"
        c    -> '$' : show (ord c)
-}

genUniforms :: Exp -> Set [String]
genUniforms e = case e of
  Uniform (EString s) -> Set.singleton [unwords ["uniform",toGLSLType "1" $ tyOf e,s,";"]]
  ELet (PVar _ _) (A3 "Sampler" _ _ (A1 "Texture2DSlot" (EString n))) _ -> Set.singleton [unwords ["uniform","sampler2D",n,";"]]
  ELet (PVar _ n) (A3 "Sampler" _ _ (A2 "Texture2D" _ _)) _ -> Set.singleton [unwords ["uniform","sampler2D",n,";"]]
  Exp e -> foldMap genUniforms e

type GLSL = Writer [String]

genStreamInput :: Backend -> Pat -> GLSL [String]
genStreamInput backend i = fmap concat $ mapM input $ case i of
    PTuple l -> l
    x -> [x]
  where
    input (PVar t n) = tell [unwords [inputDef,toGLSLType (n ++ "\n") t,n,";"]] >> return [n]
    input a = error $ "genStreamInput " ++ ppShow a
    inputDef = case backend of
        OpenGL33  -> "in"
        WebGL1    -> "attribute"

genStreamOutput :: Backend -> Exp -> GLSL [(String, String, String)]
genStreamOutput backend (eTuple -> l) = fmap concat $ zipWithM go (map (("v" ++) . show) [0..]) l
  where
    go var (A1 (f -> i) (toGLSLType "3" . tyOf -> t)) = do
        tell $ case backend of
          WebGL1    -> [unwords ["varying",t,var,";"]]
          OpenGL33  -> [unwords [i,"out",t,var,";"]]
        return [(i,t,var)]
    f "Smooth" = "smooth"
    f "Flat" = "flat"
    f "NoPerspective" = "noperspective"

eTuple (ETuple l) = l
eTuple x = [x]

genFragmentInput :: Backend -> [(String, String, String)] -> GLSL ()
genFragmentInput OpenGL33 s = tell [unwords [i,"in",t,n,";"] | (i,t,n) <- s]
genFragmentInput WebGL1 s = tell [unwords ["varying",t,n,";"] | (i,t,n) <- s]
genFragmentOutput backend (tyOf -> a@(toGLSLType "4" -> t)) = case a of
  TUnit -> return False
  _ -> case backend of
    OpenGL33  -> tell [unwords ["out",t,"f0",";"]] >> return True
    WebGL1    -> return True

genVertexGLSL :: Backend -> Exp -> (([String],[(String,String,String)]),String)
genVertexGLSL backend e@(etaRed -> ELam i (A4 "VertexOut" p s c o)) = id *** unlines $ runWriter $ do
  case backend of
    OpenGL33 -> do
      tell ["#version 330 core"]
      tell ["vec4 texture2D(sampler2D s, vec2 uv){return texture(s,uv);}"]
    WebGL1 -> do
      tell ["#version 100"]
      tell ["precision highp float;"]
      tell ["precision highp int;"]
  mapM_ tell $ genUniforms e
  input <- genStreamInput backend i
  out <- genStreamOutput backend o
  tell ["void main() {"]
  unless (null out) $ sequence_ [tell $ [var <> " = " <> genGLSL x <> ";"] | ((_,_,var),x) <- zip out $ eTuple o]
  tell ["gl_Position = "  <> genGLSL p <> ";"]
  tell ["gl_PointSize = " <> genGLSL s <> ";"]
  tell ["}"]
  return (input,out)
genVertexGLSL _ e = error $ "genVertexGLSL: " ++ ppShow e

genGLSL :: Exp -> String
genGLSL e = show $ genGLSLSubst mempty e

genFragmentGLSL :: Backend -> [(String,String,String)] -> Exp -> Exp -> String
genFragmentGLSL backend s e@(etaRed -> ELam i fragOut) ffilter{-TODO-} = unlines $ execWriter $ do
  case backend of
    OpenGL33 -> do
      tell ["#version 330 core"]
      tell ["vec4 texture2D(sampler2D s, vec2 uv){return texture(s,uv);}"]
    WebGL1 -> do
      tell ["#version 100"]
      tell ["precision highp float;"]
      tell ["precision highp int;"]
  mapM_ tell $ genUniforms e
  genFragmentInput backend s
  let o = case fragOut of
        A1 "FragmentOutRastDepth" o -> o
        A1 "FragmentOut" o -> o
        _ -> error $ "genFragmentGLSL fragOut " ++ ppShow fragOut
  hasOutput <- genFragmentOutput backend o
  tell ["void main() {"]
  case ffilter of
    A0 "PassAll" -> return ()
    A1 "Filter" (etaRed -> ELam i o) -> tell ["if (!(" <> show (genGLSLSubst (makeSubst i s) o) <> ")) discard;"]
  when hasOutput $ case backend of
    OpenGL33  -> tell ["f0 = " <> show (genGLSLSubst (makeSubst i s) o) <> ";"]
    WebGL1    -> tell ["gl_FragColor = " <> show (genGLSLSubst (makeSubst i s) o) <> ";"]
  tell ["}"]
genFragmentGLSL _ _ e ff = error $ "genFragmentGLSL: " ++ ppShow e ++ ppShow ff

makeSubst (PVar _ x) [(_,_,n)] = Map.singleton x n
makeSubst (PTuple l) x = Map.fromList $ go l x where
    go [] [] = []
    go (PVar _ x: al) ((_,_,n):bl) = (x,n) : go al bl
    go i s = error $ "genFragmentGLSL illegal input " ++ ppShow i ++ " " ++ show s

parens a = "(" <+> a <+> ")"

-- todo: (on hold) name mangling to prevent name collisions
-- todo: reader monad
genGLSLSubst :: Map String String -> Exp -> Doc
genGLSLSubst s e = case e of
  ELit a -> text $ show a
  EVar a -> text $ Map.findWithDefault a a s
  Uniform (EString s) -> text s
  -- texturing
  A3 "Sampler" _ _ _ -> error $ "sampler GLSL codegen is not supported"
  PrimN "texture2D" xs -> functionCall "texture2D" xs
  -- interpolation
  A1 "Smooth" a -> gen a
  A1 "Flat" a -> gen a
  A1 "NoPerspecitve" a -> gen a

  -- temp builtins FIXME: get rid of these
  Prim1 "primIntToWord" a -> error $ "WebGL 1 does not support uint types: " ++ ppShow e
  Prim1 "primIntToFloat" a -> gen a -- FIXME: does GLSL support implicit int to float cast???
  Prim2 "primCompareInt" a b -> error $ "GLSL codegen does not support: " ++ ppShow e
  Prim2 "primCompareWord" a b -> error $ "GLSL codegen does not support: " ++ ppShow e
  Prim2 "primCompareFloat" a b -> error $ "GLSL codegen does not support: " ++ ppShow e
  Prim1 "primNegateInt" a -> text "-" <+> parens (gen a)
  Prim1 "primNegateWord" a -> error $ "WebGL 1 does not support uint types: " ++ ppShow e
  Prim1 "primNegateFloat" a -> text "-" <+> parens (gen a)

  -- vectors
  AN n xs | n `elem` ["V2", "V3", "V4"], Just s <- vecConName $ tyOf e -> functionCall s xs
  -- bool
  A0 "True"  -> text "true"
  A0 "False" -> text "false"
  -- matrices
  AN "M22F" xs -> functionCall "mat2" xs
  AN "M23F" xs -> error "WebGL 1 does not support matrices with this dimension"
  AN "M24F" xs -> error "WebGL 1 does not support matrices with this dimension"
  AN "M32F" xs -> error "WebGL 1 does not support matrices with this dimension"
  AN "M33F" xs -> functionCall "mat3" xs
  AN "M34F" xs -> error "WebGL 1 does not support matrices with this dimension"
  AN "M42F" xs -> error "WebGL 1 does not support matrices with this dimension"
  AN "M43F" xs -> error "WebGL 1 does not support matrices with this dimension"
  AN "M44F" xs -> functionCall "mat4" xs -- where gen = gen

  Prim3 "primIfThenElse" a b c -> gen a <+> "?" <+> gen b <+> ":" <+> gen c
  -- TODO: Texture Lookup Functions
  SwizzProj a x -> "(" <+> gen a <+> (")." <> text x)
  ELam _ _ -> error "GLSL codegen for lambda function is not supported yet"
  ELet (PVar _ _) (A3 "Sampler" _ _ (A1 "Texture2DSlot" (EString n))) _ -> text n
  ELet (PVar _ n) (A3 "Sampler" _ _ (A2 "Texture2D" _ _)) _ -> text n
  ELet _ _ _ -> error "GLSL codegen for let is not supported yet"
  ETuple _ -> error "GLSL codegen for tuple is not supported yet"

  -- Primitive Functions
  PrimN ('P':'r':'i':'m':n) xs | n'@(_:_) <- trName (dropS n) -> case n' of
      (c:_) | isAlpha c -> functionCall n' xs
      [op, '_']         -> prefixOp [op] xs
      n'                -> binOp n' xs
    where
      ifType p a b = if all (p . tyOf) xs then a else b

      dropS n
        | last n == 'S' && init n `elem` ["Add", "Sub", "Div", "Mod", "BAnd", "BOr", "BXor", "BShiftL", "BShiftR", "Min", "Max", "Clamp", "Mix", "Step", "SmoothStep"] = init n
        | otherwise = n

      trName = \case

        -- Arithmetic Functions
        "Add"               -> "+"
        "Sub"               -> "-"
        "Neg"               -> "-_"
        "Mul"               -> ifType isMatrix "matrixCompMult" "*"
        "MulS"              -> "*"
        "Div"               -> "/"
        "Mod"               -> ifType isIntegral "%" "mod"

        -- Bit-wise Functions
        "BAnd"              -> "&"
        "BOr"               -> "|"
        "BXor"              -> "^"
        "BNot"              -> "~_"
        "BShiftL"           -> "<<"
        "BShiftR"           -> ">>"

        -- Logic Functions
        "And"               -> "&&"
        "Or"                -> "||"
        "Xor"               -> "^"
        "Not"               -> ifType isScalar "!_" "not"

        -- Integer/Float Conversion Functions
        "FloatBitsToInt"    -> "floatBitsToInt"
        "FloatBitsToUInt"   -> "floatBitsToUint"
        "IntBitsToFloat"    -> "intBitsToFloat"
        "UIntBitsToFloat"   -> "uintBitsToFloat"

        -- Matrix Functions
        "OuterProduct"      -> "outerProduct"
        "MulMatVec"         -> "*"
        "MulVecMat"         -> "*"
        "MulMatMat"         -> "*"

        -- Fragment Processing Functions
        "DFdx"              -> "dFdx"
        "DFdy"              -> "dFdy"

        -- Vector and Scalar Relational Functions
        "LessThan"          -> ifType isScalarNum "<"  "lessThan"
        "LessThanEqual"     -> ifType isScalarNum "<=" "lessThanEqual"
        "GreaterThan"       -> ifType isScalarNum ">"  "greaterThan"
        "GreaterThanEqual"  -> ifType isScalarNum ">=" "greaterThanEqual"
        "Equal"             -> "=="
        "EqualV"            -> ifType isScalar "==" "equal"
        "NotEqual"          -> "!="
        "NotEqualV"         -> ifType isScalar "!=" "notEqual"

        -- Angle and Trigonometry Functions
        "ATan2"             -> "atan"
        -- Exponential Functions
        "InvSqrt"           -> "inversesqrt"
        -- Common Functions
        "RoundEven"         -> "roundEven"
        "ModF"              -> error "PrimModF is not implemented yet!" -- TODO
        "MixB"              -> "mix"

        n | n `elem`
            -- Logic Functions
            [ "Any", "All"
            -- Angle and Trigonometry Functions
            , "ACos", "ACosH", "ASin", "ASinH", "ATan", "ATanH", "Cos", "CosH", "Degrees", "Radians", "Sin", "SinH", "Tan", "TanH"
            -- Exponential Functions
            , "Pow", "Exp", "Exp2", "Log2", "Sqrt"
            -- Common Functions
            , "IsNan", "IsInf", "Abs", "Sign", "Floor", "Trunc", "Round", "Ceil", "Fract", "Min", "Max", "Mix", "Step", "SmoothStep"
            -- Geometric Functions
            , "Length", "Distance", "Dot", "Cross", "Normalize", "FaceForward", "Reflect", "Refract"
            -- Matrix Functions
            , "Transpose", "Determinant", "Inverse"
            -- Fragment Processing Functions
            , "FWidth"
            -- Noise Functions
            , "Noise1", "Noise2", "Noise3", "Noise4"
            ] -> map toLower n

        _ -> ""

  x -> error $ "GLSL codegen - unsupported expression: " ++ ppShow x
  where
    prefixOp o [a] = text o <+> parens (gen a)
    binOp o [a, b] = parens (gen a) <+> text o <+> parens (gen b)
    functionCall f a = text f <+> parens (hcat $ intersperse "," $ map gen a)

    gen = genGLSLSubst s

isMatrix :: Ty -> Bool
isMatrix (TMat{}) = True
isMatrix _ = False

isIntegral :: Ty -> Bool
isIntegral TWord = True
isIntegral TInt = True
isIntegral (TVec _ TWord) = True
isIntegral (TVec _ TInt) = True
isIntegral _ = False

isScalarNum :: Ty -> Bool
isScalarNum = \case
    TInt -> True
    TWord -> True
    TFloat -> True
    _ -> False

isScalar :: Ty -> Bool
isScalar = isJust . scalarType

scalarType = \case
    TBool  -> Just "b"
    TWord  -> Just "u"
    TInt   -> Just "i"
    TFloat -> Just ""
    _ -> Nothing

vecConName = \case
    TVec n t | is234 n, Just s <- scalarType t -> Just $ s ++ "vec" ++ show n
    t -> Nothing

toGLSLType msg = \case
    TBool  -> "bool"
    TWord  -> "uint"
    TInt   -> "int"
    TFloat -> "float"
    x@(TVec n t) | Just s <- vecConName x -> s
    TMat i j TFloat | is234 i && is234 j -> "mat" ++ if i == j then show i else show i ++ "x" ++ show j
    TTuple []         -> "void"
    t -> error $ "toGLSLType: " ++ msg ++ " " ++ ppShow t

is234 = (`elem` [2,3,4])


