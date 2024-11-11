module Compile.Program

import Control.Monad.State

import Data.SortedMap

import Data.DList
import Data.DMap
import Data.Singleton
import LNG.BuiltIns
import LNG.TypeChecked as LNG
import LLVM
import Compile.FunDef
import Compile.Data.CompM
import Compile.Data.Context
import Compile.Data.Error
import Compile.Utils

||| Given a list of function definitions, construct a fuinction context
||| @ defs the function dfefinitions
mkFunMap : (def : List LNG.FunDef) -> FunCTX
mkFunMap l = foldr insertFun empty l where

  ||| Make a Function pointer representing the given function
  ||| @ fun the function
  mkFunPtr
     : (fun : Fun t ts)
    -> LLValue (Ptr $ FunType (GetLLType t) (map GetLLType ts))
  -- TODO: was there any requirement about how to name functions in LLVM?
  mkFunPtr (MkFun t ts (MkFunId funId))
    = ConstPtr
    $ MkConst (Val $ FunType (GetLLType t) (map GetLLType ts)) (MkConstId funId)

  ||| Insert the identifier of the function and the function pointer representing
  ||| it to the function context.
  ||| @ def the definition of the function
  ||| @ the function context
  insertFun : (def : LNG.FunDef) -> (ctx : FunCTX) -> FunCTX
  insertFun def = insert def.funId (mkFunPtr def.funId)

||| Given a mapping of string literals to constants, create a list of the
||| definitions of these constants that reflects the mapoping.
||| @ m the mapping
mkConstDefs
   : (m : SortedMap String (n ** (Const (Array I8 n), LLValue (Array I8 n))))
  -> List ConstDef
mkConstDefs m = foldl (flip $ (::) . mkConstDef) Nil (SortedMap.toList m) where
  mkConstDef : (String, (n ** (Const (Array I8 n), LLValue (Array I8 n)))) -> ConstDef
  mkConstDef (str, (n ** (cst, arr))) = DefineConst (Array I8 n) cst arr

||| Compile a semantically correct LNG program
||| @ prog the LNG program
export
compileProgram : (prog : LNG.Program) -> CompM LLVM.Program
compileProgram (MkProgram { funcs }) = do

  -- Create the function context and append it to the context of built-in
  -- functions
  let funMap = mkFunMap funcs
  modify { funcs $= (`union` funMap) }

  -- compile each function definition in the program
  funDefs <- traverse compileFunDef funcs

  -- Compute the definitions of constants representing the string literals
  -- mentioned in the program.
  constDefs <- mkConstDefs <$> gets strLits

  pure (LLVM.MkProgram { funDecls = builtInDecls, constDefs, funcs = funDefs })
