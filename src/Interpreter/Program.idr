module Interpreter.Program

import Control.Monad.Either
import Control.Monad.State

import Data.SortedMap

import Data.DList
import Interpreter.InterpreterT
import Interpreter.Semantics
import Interpreter.FunDecl
import LNG.Data.Position
import LNG.Parsed

addFunDecl : Monad m => ^FunDecl -> InterpreterT m ()
addFunDecl (p |^ decl)
  = modify
  $ the (InterpreterState m -> InterpreterState m)
  $ { funcs $= insert (^^decl.funId) (funInterpreter decl) }
    

makeFunMap : Monad m => PosList FunDecl -> InterpreterT m ()
makeFunMap (Nil p) = pure ()
makeFunMap (decl :: decls) = addFunDecl decl >> makeFunMap decls

findMainAndMakeFunMap : Monad m => PosList FunDecl -> InterpreterT m FunDecl
findMainAndMakeFunMap (Nil p) = throwError $ noMainFunction p
findMainAndMakeFunMap (decl :: decls) = case (^^decl).funId of
  (_ |^ MkId "main") => makeFunMap (decl :: decls) >> pure (^^decl)
  _ => addFunDecl decl >> findMainAndMakeFunMap decls
  


export
interpretProgram : Monad m => Program -> InterpreterT m ()
interpretProgram prog = do
  
  mainFunc <- findMainAndMakeFunMap prog.funcs

  let (t ** ts ** main) = funInterpreter mainFunc {m}
  case t of
    TVoid => case ts of
      Nil => main []

      ts => throwError $ numParamsMismatch (pos mainFunc.params) 0 (length ts)
    _ => throwError $ typeError (pos mainFunc.retType) TVoid t
  
  