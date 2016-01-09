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

import Control.Arrow
import Control.Monad.Writer

import LambdaCube.Compiler.Pretty
import LambdaCube.Compiler.CGExp
import IR(Backend(..))

encodeChar :: Char -> String
encodeChar c | isAlphaNum c = [c]
encodeChar '_' = "__"
encodeChar '.' = "_dot"
encodeChar '$' = "_dollar"
encodeChar '~' = "_tilde"
encodeChar '=' = "_eq"
encodeChar '<' = "_less"
encodeChar '>' = "_greater"
encodeChar '!' = "_bang"
encodeChar '#' = "_hash"
encodeChar '%' = "_percent"
encodeChar '^' = "_up"
encodeChar '&' = "_amp"
encodeChar '|' = "_bar"
encodeChar '*' = "_times"
encodeChar '/' = "_div"
encodeChar '+' = "_plus"
encodeChar '-' = "_minus"
encodeChar ':' = "_colon"
encodeChar '\\' = "_bslash"
encodeChar '?' = "_qmark"
encodeChar '@' = "_at"
encodeChar '\'' = "_prime"
encodeChar c = '$' : show (ord c)

mangleIdent :: String -> String
mangleIdent n = '_':concatMap encodeChar n

genUniforms :: Exp -> Set [String]
genUniforms e = case e of
  Uniform (ELString s) -> Set.singleton [unwords ["uniform",toGLSLType "1" $ tyOf e,s,";"]]
  ELet (PVar _ _) (A3 "Sampler" _ _ (A1 "Texture2DSlot" (ELString n))) _ -> Set.singleton [unwords ["uniform","sampler2D",showN n,";"]]
  ELet (PVar _ n) (A3 "Sampler" _ _ (A2 "Texture2D" _ _)) _ -> Set.singleton [unwords ["uniform","sampler2D",showN n,";"]]
  Exp e -> foldMap genUniforms e

type GLSL = Writer [String]

genStreamInput :: Backend -> Pat -> GLSL [String]
genStreamInput backend i = do
  let inputDef = case backend of
        OpenGL33  -> "in"
        WebGL1    -> "attribute"
      input (PVar t x@(showN -> n)) = tell [unwords [inputDef,toGLSLType (ppShow x ++ "\n") t,n,";"]] >> return [n]
      input a = error $ "genStreamInput " ++ ppShow a
  case i of
    PTuple l -> foldM (\a b -> (a ++) <$> input b) [] l
    x -> input x

genStreamOutput :: Backend -> Exp -> GLSL [(String, String, String)]
genStreamOutput backend a = do
  let f "Smooth" = "smooth"
      f "Flat" = "flat"
      f "NoPerspective" = "noperspective"
      go n (A1 i (toGLSLType "3" . tyOf -> t)) = do
        let var = "v" <> show n
        case backend of
          WebGL1    -> tell [unwords ["varying",t,var,";"]]
          OpenGL33  -> tell [unwords [f i,"out",t,var,";"]]
        return [(f i,t,var)]
  case a of
    ETuple l -> concat <$> sequence (map (uncurry go) $ zip [0..] l)
    x -> go 0 x

genFragmentInput :: Backend -> [(String, String, String)] -> GLSL ()
genFragmentInput OpenGL33 s = tell [unwords [i,"in",t,n,";"] | (i,t,n) <- s]
genFragmentInput WebGL1 s = tell [unwords ["varying",t,n,";"] | (i,t,n) <- s]
genFragmentOutput backend a@(toGLSLType "4" . tyOf -> t) = case tyOf a of
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
  unless (null out) $ do
    let go ((_,_,var),x) = tell $ [var <> " = " <> unwords (genGLSL x) <> ";"]
    case o of
      ETuple l -> mapM_ go $ zip out l
      x -> let [out1] = out in go (out1,x)
  tell $ ["gl_Position = " <> unwords (genGLSL p) <> ";"]
  tell $ ["gl_PointSize = " <> unwords (genGLSL s) <> ";"]
  tell ["}"]
  return (input,out)
genVertexGLSL _ e = error $ "genVertexGLSL: " ++ ppShow e

genFragmentGLSL :: Backend -> [(String,String,String)] -> Exp -> Exp -> String
genFragmentGLSL backend s e@(etaRed -> ELam i fragOut) ffilter{-TODO-} = unlines $ execWriter $ do
  let o = case fragOut of
        A1 "FragmentOutRastDepth" o -> o
        A1 "FragmentOut" o -> o
        _ -> error $ "genFragmentGLSL fragOut " ++ ppShow fragOut
      makeSubst (PVar _ (showN -> x)) [(_,_,n)] = Map.singleton x n
      makeSubst (PTuple l) x = Map.fromList $ go l x where
        go [] [] = []
        go (PVar _ (showN -> x):al) ((_,_,n):bl) = (x,n) : go al bl
        go _ _ = error $ "genFragmentGLSL illegal input " ++ ppShow i ++ " " ++ show s
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
  hasOutput <- genFragmentOutput backend o
  tell ["void main() {"]
  case ffilter of
    A0 "PassAll" -> return ()
    A1 "Filter" (etaRed -> ELam i o) -> tell ["if (!(" <> unwords (genGLSLSubst (makeSubst i s) o) <> ")) discard;"]
  when hasOutput $ case backend of
    OpenGL33  -> tell $ ["f0 = " <> unwords (genGLSLSubst (makeSubst i s) o) <> ";"]
    WebGL1    -> tell $ ["gl_FragColor = " <> unwords (genGLSLSubst (makeSubst i s) o) <> ";"]
  tell ["}"]
genFragmentGLSL _ _ e ff = error $ "genFragmentGLSL: " ++ ppShow e ++ ppShow ff


genGLSL :: Exp -> [String]
genGLSL = genGLSLSubst mempty

parens a = ["("] <> a <> [")"]

-- todo: (on hold) name mangling to prevent name collisions
-- todo: reader monad
genGLSLSubst :: Map String String -> Exp -> [String]
genGLSLSubst s e = case e of
  ELit a -> [show a]
  EVar (showN -> a) -> [Map.findWithDefault a a s]
  Uniform (ELString s) -> [s]
  -- texturing
  A3 "Sampler" _ _ _ -> error $ "sampler GLSL codegen is not supported"
  Prim2 "texture2D" a b -> functionCall "texture2D" [a,b]
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
  Prim1 "primNegateInt" a -> ["-"] <> parens (gen a)
  Prim1 "primNegateWord" a -> error $ "WebGL 1 does not support uint types: " ++ ppShow e
  Prim1 "primNegateFloat" a -> ["-"] <> parens (gen a)

  -- vectors
  AN n xs | n `elem` ["V2", "V3", "V4"], Just s <- vecConName $ tyOf e -> functionCall s xs
  -- bool
  A0 "True" -> ["true"]
  A0 "False" -> ["false"]
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

  Prim3 "primIfThenElse" a b c -> gen a <> ["?"] <> gen b <> [":"] <> gen c
  -- TODO: Texture Lookup Functions
  SwizzProj a x -> ["("] <> gen a <> [")." ++ x]
  ELam _ _ -> error "GLSL codegen for lambda function is not supported yet"
  ELet (PVar _ _) (A3 "Sampler" _ _ (A1 "Texture2DSlot" (ELString n))) _ -> [n]
  ELet (PVar _ n) (A3 "Sampler" _ _ (A2 "Texture2D" _ _)) _ -> [n]
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
    prefixOp o [a] = [o] <> parens (gen a)
    binOp o [a, b] = parens (gen a) <> [o] <> parens (gen b)
    functionCall f a = [f,"(",intercalate "," (map (unwords . gen) a),")"]

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


