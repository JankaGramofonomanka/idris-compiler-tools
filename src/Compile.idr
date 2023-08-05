module Compile

import Control.Monad.Either
import Control.Monad.State

import Data.DList
import LLVM
import LLVM.Generalized
import LNG.BuiltIns
import LNG.TypeChecked as LNG
import Compile.Phase3.Program
import Compile.Data.CompM
import Compile.Data.FunContext
import Compile.Data.Error
import Compile.Utils

import Utils

export
compile : LNG.Program -> Either Error LLVM.Program
compile = evalStateT initState . compileProgram where
  
  insert' : (t ** ts ** (Fun t ts, FunVal Reg t ts)) -> FunCTX -> FunCTX
  insert' (t ** ts ** (key, val)) = FunContext.insert key val

  builtIns : FunCTX
  builtIns = foldr insert' empty Compile.builtIns
  
  initState : CompState
  initState = { funcs := builtIns } emptyState
      

