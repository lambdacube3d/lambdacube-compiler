{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
module CoreToGLSL where

import Debug.Trace

import Data.Char
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

import Control.Arrow
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Foldable (Foldable)
import qualified Data.Foldable as F

import Pretty
import Type
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

toGLSLType msg t = case t of
  TBool  -> "bool"
  TWord  -> "uint"
  TInt   -> "int"
  TFloat -> "float"
  TVec 2 (TBool) -> "bvec2"
  TVec 3 (TBool) -> "bvec3"
  TVec 4 (TBool) -> "bvec4"
  TVec 2 (TWord) -> "uvec2"
  TVec 3 (TWord) -> "uvec3"
  TVec 4 (TWord) -> "uvec4"
  TVec 2 (TInt) -> "ivec2"
  TVec 3 (TInt) -> "ivec3"
  TVec 4 (TInt) -> "ivec4"
  TVec 2 (TFloat) -> "vec2"
  TVec 3 (TFloat) -> "vec3"
  TVec 4 (TFloat) -> "vec4"
  TMat 2 2 (TFloat) -> "mat2"
  TMat 2 3 (TFloat) -> "mat2x3"
  TMat 2 4 (TFloat) -> "mat2x4"
  TMat 3 2 (TFloat) -> "mat3x2"
  TMat 3 3 (TFloat) -> "mat3"
  TMat 3 4 (TFloat) -> "mat3x4"
  TMat 4 2 (TFloat) -> "mat4x2"
  TMat 4 3 (TFloat) -> "mat4x3"
  TMat 4 4 (TFloat) -> "mat4"
  TTuple []         -> "void"
  t -> error $ "toGLSLType: " ++ msg ++ " " ++ ppShow t

pattern ELString s = ELit (LString s)

genUniforms :: Exp -> Set [String]
genUniforms e = case e of
  A1 "Uniform" (ELString s) -> Set.singleton [unwords ["uniform",toGLSLType "1" $ tyOf e,s,";"]]
  Exp e -> F.foldMap genUniforms e

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
genVertexGLSL backend e@(ELam i (A4 "VertexOut" p s c o)) = id *** unlines $ runWriter $ do
  case backend of
    OpenGL33 -> do
      tell ["#version 330 core"]
    WebGL1 -> do
      tell ["#version 100"]
      tell ["precision highp float;"]
      tell ["precision highp int;"]
  F.mapM_ tell $ genUniforms e
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

genFragmentGLSL :: Backend -> [(String,String,String)] -> Exp -> String
genFragmentGLSL backend s e@(ELam i fragOut) = unlines $ execWriter $ do
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
    WebGL1 -> do
      tell ["#version 100"]
      tell ["precision highp float;"]
      tell ["precision highp int;"]
  F.mapM_ tell $ genUniforms e
  genFragmentInput backend s
  hasOutput <- genFragmentOutput backend o
  tell ["void main() {"]
  when hasOutput $ case backend of
    OpenGL33  -> tell $ ["f0 = " <> unwords (genGLSLSubst (makeSubst i s) o) <> ";"]
    WebGL1    -> tell $ ["gl_FragColor = " <> unwords (genGLSLSubst (makeSubst i s) o) <> ";"]
  tell ["}"]
genFragmentGLSL _ _ e = error $ "genFragmentGLSL: " ++ ppShow e


genGLSL :: Exp -> [String]
genGLSL = genGLSLSubst mempty

parens a = ["("] <> a <> [")"]
binOp s o a b = parens (genGLSLSubst s a) <> [o] <> parens (genGLSLSubst s b)
functionCall s f a = [f,"(",intercalate "," (map (unwords . genGLSLSubst s) a),")"]

-- todo: (on hold) name mangling to prevent name collisions
-- todo: reader monad
genGLSLSubst :: Map String String -> Exp -> [String]
genGLSLSubst s e = case e of
  ELit (LInt a) -> [show a]
  ELit (LFloat a) -> [show a]
  ELit (LChar a) -> [show a]
  ELit (LString a) -> [show a]
  EVar (showN -> a) -> [Map.findWithDefault a a s]
  A1 "Uniform" (ELString s) -> [s]
  -- texturing
  A3 "Sampler" _ _ _ -> error $ "sampler GLSL codegen is not supported" -- TODO
  A2 "texture2D" a b -> functionCall s "texture2D" [a,b]
  -- interpolation
  A1 "Smooth" a -> genGLSLSubst s a
  A1 "Flat" a -> genGLSLSubst s a
  A1 "NoPerspecitve" a -> genGLSLSubst s a

  -- temp builtins FIXME: get rid of these
  Prim1 "primIntToWord" a -> error $ "WebGL 1 does not support uint types: " ++ ppShow e
  Prim1 "primIntToFloat" a -> genGLSLSubst s a -- FIXME: does GLSL support implicit int to float cast???
  Prim2 "primCompareInt" a b -> error $ "GLSL codegen does not support: " ++ ppShow e
  Prim2 "primCompareWord" a b -> error $ "GLSL codegen does not support: " ++ ppShow e
  Prim2 "primCompareFloat" a b -> error $ "GLSL codegen does not support: " ++ ppShow e
  Prim1 "primNegateInt" a -> ["-"] <> parens (genGLSLSubst s a)
  Prim1 "primNegateWord" a -> error $ "WebGL 1 does not support uint types: " ++ ppShow e
  Prim1 "primNegateFloat" a -> ["-"] <> parens (genGLSLSubst s a)

  -- vectors
  A2 "V2" a b -> case tyOf e of
    TVec 2 TFloat -> functionCall s "vec2" [a,b]
    TVec 2 TInt   -> functionCall s "ivec2" [a,b]
    TVec 2 TBool  -> functionCall s "bvec2" [a,b]
    t -> error $ "GLSL codegen does not support type: " ++ ppShow t
  A3 "V3" a b c -> case tyOf e of
    TVec 3 TFloat -> functionCall s "vec3" [a,b,c]
    TVec 3 TInt   -> functionCall s "ivec3" [a,b,c]
    TVec 3 TBool  -> functionCall s "bvec3" [a,b,c]
    t -> error $ "GLSL codegen does not support type: " ++ ppShow t
  A4 "V4" a b c d -> case tyOf e of
    TVec 4 TFloat -> functionCall s "vec4" [a,b,c,d]
    TVec 4 TInt   -> functionCall s "ivec4" [a,b,c,d]
    TVec 4 TBool  -> functionCall s "bvec4" [a,b,c,d]
    t -> error $ "GLSL codegen does not support type: " ++ ppShow t

  -- bool
  A0 "True" -> ["true"]
  A0 "False" -> ["false"]
  -- matrices
  A2 "M22F" a b -> functionCall s "mat2" [a, b]
  A3 "M23F" a b c -> error "WebGL 1 does not support matrices with this dimension"
  A4 "M24F" a b c d -> error "WebGL 1 does not support matrices with this dimension"
  A2 "M32F" a b -> error "WebGL 1 does not support matrices with this dimension"
  A3 "M33F" a b c -> functionCall s "mat3" [a, b, c]
  A4 "M34F" a b c d -> error "WebGL 1 does not support matrices with this dimension"
  A2 "M42F" a b -> error "WebGL 1 does not support matrices with this dimension"
  A3 "M43F" a b c -> error "WebGL 1 does not support matrices with this dimension"
  A4 "M44F" a b c d -> functionCall s "mat4" [a, b, c, d] -- where gen = genGLSLSubst s

  -- Primitive Functions

  -- Arithmetic Functions
  Prim2 "PrimAdd" a b -> binOp s "+" a b
  Prim2 "PrimAddS" a b -> binOp s "+" a b
  Prim2 "PrimSub" a b -> binOp s "-" a b
  Prim2 "PrimSubS" a b -> binOp s "-" a b
  Prim2 "PrimMul" a b
    | all (isMatrix . tyOf) [a,b] -> functionCall s "matrixCompMult" [a,b]
    | otherwise -> binOp s "*" a b
  Prim2 "PrimMulS" a b -> binOp s "*" a b
  Prim2 "PrimDiv" a b -> binOp s "/" a b
  Prim2 "PrimDivS" a b -> binOp s "/" a b
  Prim1 "PrimNeg" a -> ["-"] <> parens (genGLSLSubst s a)
  Prim2 "PrimMod" a b
    | all (isIntegral . tyOf) [a,b] -> binOp s "%" a b
    | otherwise -> functionCall s "mod" [a,b]
  Prim2 "PrimModS" a b
    | all (isIntegral . tyOf) [a,b] -> binOp s "%" a b
    | otherwise -> functionCall s "mod" [a,b]

  -- Bit-wise Functions
  Prim2 "PrimBAnd" a b -> binOp s "&" a b
  Prim2 "PrimBAndS" a b -> binOp s "&" a b
  Prim2 "PrimBOr" a b -> binOp s "|" a b
  Prim2 "PrimBOrS" a b -> binOp s "|" a b
  Prim2 "PrimBXor" a b -> binOp s "^" a b
  Prim2 "PrimBXorS" a b -> binOp s "^" a b
  Prim1 "PrimBNot" a -> ["~"] <> parens (genGLSLSubst s a)
  Prim2 "PrimBShiftL" a b -> binOp s "<<" a b
  Prim2 "PrimBShiftLS" a b -> binOp s "<<" a b
  Prim2 "PrimBShiftR" a b -> binOp s ">>" a b
  Prim2 "PrimBShiftRS" a b -> binOp s ">>" a b

  -- Logic Functions
  Prim2 "PrimAnd" a b -> binOp s "&&" a b
  Prim2 "PrimOr" a b -> binOp s "||" a b
  Prim2 "PrimXor" a b -> binOp s "^" a b
  Prim1 "PrimNot" a
    | all (isScalar . tyOf) [a] -> ["!"] <> parens (genGLSLSubst s a)
    | otherwise -> functionCall s "not" [a]
  Prim1 "PrimAny" a -> functionCall s "any" [a]
  Prim1 "PrimAll" a -> functionCall s "all" [a]

  -- Angle and Trigonometry Functions
  Prim1 "PrimACos" a -> functionCall s "acos" [a]
  Prim1 "PrimACos" a -> functionCall s "acos" [a]
  Prim1 "PrimACosH" a -> functionCall s "acosh" [a]
  Prim1 "PrimASin" a -> functionCall s "asin" [a]
  Prim1 "PrimASinH" a -> functionCall s "asinh" [a]
  Prim1 "PrimATan" a -> functionCall s "atan" [a]
  Prim2 "PrimATan2" a b -> functionCall s "atan" [a,b]
  Prim1 "PrimATanH" a -> functionCall s "atanh" [a]
  Prim1 "PrimCos" a -> functionCall s "cos" [a]
  Prim1 "PrimCosH" a -> functionCall s "cosh" [a]
  Prim1 "PrimDegrees" a -> functionCall s "degrees" [a]
  Prim1 "PrimRadians" a -> functionCall s "radians" [a]
  Prim1 "PrimSin" a -> functionCall s "sin" [a]
  Prim1 "PrimSinH" a -> functionCall s "sinh" [a]
  Prim1 "PrimTan" a -> functionCall s "tan" [a]
  Prim1 "PrimTanH" a -> functionCall s "tanh" [a]

  -- Exponential Functions
  Prim2 "PrimPow" a b -> functionCall s "pow" [a,b]
  Prim1 "PrimExp" a -> functionCall s "exp" [a]
  Prim1 "PrimLog" a -> functionCall s "log" [a]
  Prim1 "PrimExp2" a -> functionCall s "exp2" [a]
  Prim1 "PrimLog2" a -> functionCall s "log2" [a]
  Prim1 "PrimSqrt" a -> functionCall s "sqrt" [a]
  Prim1 "PrimInvSqrt" a -> functionCall s "inversesqrt" [a]

  -- Common Functions
  Prim1 "PrimIsNan" a -> functionCall s "isnan" [a]
  Prim1 "PrimIsInf" a -> functionCall s "isinf" [a]
  Prim1 "PrimAbs" a -> functionCall s "abs" [a]
  Prim1 "PrimSign" a -> functionCall s "sign" [a]
  Prim1 "PrimFloor" a -> functionCall s "floor" [a]
  Prim1 "PrimTrunc" a -> functionCall s "trunc" [a]
  Prim1 "PrimRound" a -> functionCall s "round" [a]
  Prim1 "PrimRoundEven" a -> functionCall s "roundEven" [a]
  Prim1 "PrimCeil" a -> functionCall s "ceil" [a]
  Prim1 "PrimFract" a -> functionCall s "fract" [a]
  Prim1 "PrimModF" a -> error "PrimModF is not implemented yet!" -- TODO
  Prim2 "PrimMin" a b -> functionCall s "min" [a,b]
  Prim2 "PrimMinS" a b -> functionCall s "min" [a,b]
  Prim2 "PrimMax" a b -> functionCall s "max" [a,b]
  Prim2 "PrimMaxS" a b -> functionCall s "max" [a,b]
  Prim3 "PrimClamp" a b c -> functionCall s "clamp" [a,b,c]
  Prim3 "PrimClampS" a b c -> functionCall s "clamp" [a,b,c]
  Prim3 "PrimMix" a b c -> functionCall s "mix" [a,b,c]
  Prim3 "PrimMixS" a b c -> functionCall s "mix" [a,b,c]
  Prim3 "PrimMixB" a b c -> functionCall s "mix" [a,b,c]
  Prim2 "PrimStep" a b -> functionCall s "step" [a,b]
  Prim2 "PrimStepS" a b -> functionCall s "step" [a,b]
  Prim3 "PrimSmoothStep" a b c -> functionCall s "smoothstep" [a,b,c]
  Prim3 "PrimSmoothStepS" a b c -> functionCall s "smoothstep" [a,b,c]

  -- Integer/Float Conversion Functions
  Prim1 "PrimFloatBitsToInt" a -> functionCall s "floatBitsToInt" [a]
  Prim1 "PrimFloatBitsToUInt" a -> functionCall s "floatBitsToUint" [a]
  Prim1 "PrimIntBitsToFloat" a -> functionCall s "intBitsToFloat" [a]
  Prim1 "PrimUIntBitsToFloat" a -> functionCall s "uintBitsToFloat" [a]

  -- Geometric Functions
  Prim1 "PrimLength" a -> functionCall s "length" [a]
  Prim2 "PrimDistance" a b -> functionCall s "distance" [a,b]
  Prim2 "PrimDot" a b -> functionCall s "dot" [a,b]
  Prim2 "PrimCross" a b -> functionCall s "cross" [a,b]
  Prim1 "PrimNormalize" a -> functionCall s "normalize" [a]
  Prim3 "PrimFaceForward" a b c -> functionCall s "faceforward" [a,b,c]
  Prim2 "PrimReflect" a b -> functionCall s "reflect" [a,b]
  Prim3 "PrimRefract" a b c -> functionCall s "refract" [a,b,c]

  -- Matrix Functions
  Prim1 "PrimTranspose" a -> functionCall s "transpose" [a]
  Prim1 "PrimDeterminant" a -> functionCall s "determinant" [a]
  Prim1 "PrimInverse" a -> functionCall s "inverse" [a]
  Prim2 "PrimOuterProduct" a b -> functionCall s "outerProduct" [a,b]
  Prim2 "PrimMulMatVec" a b -> binOp s "*" a b
  Prim2 "PrimMulVecMat" a b -> binOp s "*" a b
  Prim2 "PrimMulMatMat" a b -> binOp s "*" a b

  -- Vector and Scalar Relational Functions
  Prim2 "PrimLessThan" a b
    | all (isScalarNum . tyOf) [a,b] -> binOp s "<" a b
    | otherwise -> functionCall s "lessThan" [a,b]
  Prim2 "PrimLessThanEqual" a b
    | all (isScalarNum . tyOf) [a,b] -> binOp s "<=" a b
    | otherwise -> functionCall s "lessThanEqual" [a,b]
  Prim2 "PrimGreaterThan" a b
    | all (isScalarNum . tyOf) [a,b] -> binOp s ">" a b
    | otherwise -> functionCall s "greaterThan" [a,b]
  Prim2 "PrimGreaterThanEqual" a b
    | all (isScalarNum . tyOf) [a,b] -> binOp s ">=" a b
    | otherwise -> functionCall s "greaterThanEqual"   [a,b]
  Prim2 "PrimEqualV" a b
    | all (isScalar . tyOf) [a,b] -> binOp s "==" a b
    | otherwise -> functionCall s "equal" [a,b]
  Prim2 "PrimEqual" a b -> binOp s "==" a b
  Prim2 "PrimNotEqualV" a b
    | all (isScalar . tyOf) [a,b] -> binOp s "!=" a b
    | otherwise -> functionCall s "notEqual" [a,b]
  Prim2 "PrimNotEqual" a b -> binOp s "!=" a b

  -- Fragment Processing Functions
  Prim1 "PrimDFdx" a -> functionCall s "dFdx" [a]
  Prim1 "PrimDFdy" a -> functionCall s "dFdy" [a]
  Prim1 "PrimFWidth" a -> functionCall s "fwidth" [a]

  -- Noise Functions
  Prim1 "PrimNoise1" a -> functionCall s "noise1" [a]
  Prim1 "PrimNoise2" a -> functionCall s "noise2" [a]
  Prim1 "PrimNoise3" a -> functionCall s "noise3" [a]
  Prim1 "PrimNoise4" a -> functionCall s "noise4" [a]

  A3 "ifThenElse" a b c -> genGLSLSubst s a <> ["?"] <> genGLSLSubst s b <> [":"] <> genGLSLSubst s c
  -- TODO: Texture Lookup Functions
  EApp (EFieldProj _ x) a -> ["("] <> genGLSLSubst s a <> [")." ++ ppShow x]
  ELam _ _ -> error "GLSL codegen for lambda function is not supported yet"
  ELet _ _ _ -> error "GLSL codegen for let is not supported yet"
  ETuple _ -> error "GLSL codegen for tuple is not supported yet"
  ERecord _ -> error "GLSL codegen for record is not supported yet"
  x -> error $ "GLSL codegen - unsupported expression: " ++ ppShow x

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
isScalar = \case
    TBool -> True
    t -> isScalarNum t


