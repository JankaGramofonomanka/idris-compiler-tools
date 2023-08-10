module Compile.Program

import Control.Monad.State

import Data.SortedMap

import Data.DList
import Data.DMap
import Data.GCompare
import LNG.BuiltIns
import LNG.TypeChecked as LNG
import LLVM
import Compile.FunDef
import Compile.Data.CompM
import Compile.Data.Context
import Compile.Data.Error
import Compile.Utils


mkFunMap : List LNG.FunDef -> FunCTX
mkFunMap l = foldr insertFun empty l where

  mkFunPtr : Fun t ts -> LLValue (Ptr $ FunType (GetLLType t) (map GetLLType ts))
  -- TODO: was there any requirement about how to name functions in LLVM?
  mkFunPtr (MkFun t ts (MkFunId funId)) = ConstPtr (MkConst (FunType (GetLLType t) (map GetLLType ts)) (MkConstId funId))

  insertFun : LNG.FunDef -> FunCTX -> FunCTX
  insertFun def = insert def.funId (mkFunPtr def.funId)

mkConstDefs : SortedMap String (n ** (Const (Array I8 n), LLValue (Array I8 n))) -> List ConstDef
mkConstDefs m = foldl (flip $ (::) . mkConstDef) Nil (SortedMap.toList m) where
  mkConstDef : (String, (n ** (Const (Array I8 n), LLValue (Array I8 n)))) -> ConstDef
  mkConstDef (str, (n ** (cst, arr))) = DefineConst (Array I8 n) cst arr

export
compileProgram : LNG.Program -> CompM LLVM.Program
compileProgram (MkProgram { funcs }) = do

  let funMap = mkFunMap funcs
  modify { funcs $= (`union` funMap) }

  funDecls <- traverse compileFunDecl funcs
  
  constDefs <- mkConstDefs <$> gets strLits

  pure (LLVM.MkProgram { funDecls = builtInDecls, constDefs, funcs = funDecls })
