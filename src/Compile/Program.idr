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


mkFunMap : List (t ** ts ** fun ** FunDef t ts fun) -> FunCTX
mkFunMap l = foldr insertFun empty l where

  mkFunPtr : Fun t ts -> LLValue (Ptr $ FunType (GetLLType t) (map GetLLType ts))
  -- TODO: was there any requirement about how to name functions in LLVM?
  mkFunPtr (MkFun t ts (MkFunId funId)) = ConstPtr (MkConst (FunType (GetLLType t) (map GetLLType ts)) (MkConstId funId))

  insertFun : (t ** ts ** fun ** FunDef t ts fun) -> FunCTX -> FunCTX
  insertFun (t ** ts ** funId ** _) = insert (MkFun t ts funId) (mkFunPtr (MkFun t ts funId))

  

compileFunDecl' : (t ** ts ** fun ** FunDef t ts fun)
               -> CompM FunDef
compileFunDecl' (t ** ts ** fun ** decl) = compileFunDecl decl

mkConstDefs : SortedMap String (n ** (Const (Array I8 n), LLValue (Array I8 n))) -> List ConstDef
mkConstDefs m = foldl (flip $ (::) . mkConstDef) Nil (SortedMap.toList m) where
  mkConstDef : (String, (n ** (Const (Array I8 n), LLValue (Array I8 n)))) -> ConstDef
  mkConstDef (str, (n ** (cst, arr))) = DefineConst (Array I8 n) cst arr

export
compileProgram : LNG.Program -> CompM LLVM.Program
compileProgram (MkProgram { main, funcs }) = do

  let funMap = mkFunMap ((TInt ** [] ** MkFunId "main" ** main) :: funcs)
  modify { funcs $= (`union` funMap) }

  mainDecl <- compileFunDecl main
  funDecls <- traverse compileFunDecl' funcs
  
  constDefs <- mkConstDefs <$> gets strLits

  pure (LLVM.MkProgram { funDecls = builtInDecls, constDefs, funcs = (mainDecl :: funDecls) })
