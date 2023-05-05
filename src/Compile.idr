module Compile

import Control.Monad.Either
import Control.Monad.State

import Data.DList
import LLVM
import LNG.BuiltIns
import LNG.TypeChecked as LNG
import Compile.Program
import Compile.Data.CompM
import Compile.Data.Context
import Compile.Utils

import Utils

compile : LNG.Program -> Either Error LLVM.Program
compile = evalStateT initState . compileProgram where
  
  insert' : (t ** ts ** (Fun t ts, FunVal t ts)) -> FunCTX -> FunCTX
  insert' (t ** ts ** (key, val)) = FunCTX.insert key val

  builtIns : FunCTX
  builtIns = foldr insert' empty Compile.builtIns
  
  initState : CompState
  initState = { funcs := builtIns } emptyState
      

