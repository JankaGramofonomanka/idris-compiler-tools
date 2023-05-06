module TypeCheck

import Control.Monad.Either
import Control.Monad.State

import LNG.BuiltIns
import LNG.Parsed                 as LNG
import LNG.TypeChecked            as TC
import TypeCheck.Data.Context
import TypeCheck.Data.TypeCheckM
import TypeCheck.Program

import Utils

export
typeCheck : LNG.Program -> Either Error TC.Program
typeCheck = evalStateT initState . typeCheckProgram where

  builtIns : FunCTX
  builtIns = foldr3 FunCTX.declareBuiltIn FunCTX.empty BuiltIns.TypeCheck.builtIns
  
  initState = MkTCST { funcs = builtIns }

