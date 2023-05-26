module Interpreter.Program

import Control.Monad.Either
import Control.Monad.State

import Data.SortedMap

import Data.DList
import Interpreter.Data.Error
import Interpreter.Data.InterpreterT
import Interpreter.Semantics
import Interpreter.FunDecl
import LNG.Parsed
import Parse.Data.Position

addFunDecl : Monad m => ^FunDecl -> InterpreterT m ()
addFunDecl (p |^ decl)
  = modify
  $ the (InterpreterState m -> InterpreterState m)
  $ { funcs $= insert (^^decl.funId) (funInterpreter decl) }
    

makeFunMap : Monad m => List (^FunDecl) -> InterpreterT m ()
makeFunMap Nil = pure ()
makeFunMap (decl :: decls) = addFunDecl decl >> makeFunMap decls

findMainAndMakeFunMap : Monad m => ^(List $ ^FunDecl) -> InterpreterT m FunDecl
findMainAndMakeFunMap (p |^ funcs) = findMainAndMakeFunMap' p funcs where

  findMainAndMakeFunMap' : Pos -> List (^FunDecl) -> InterpreterT m FunDecl
  findMainAndMakeFunMap' p Nil = throwError $ noMainFunction p
  findMainAndMakeFunMap' p (decl :: decls) = case (^^decl).funId of
    (_ |^ MkId "main") => makeFunMap (decl :: decls) >> pure (^^decl)
    _ => addFunDecl decl >> findMainAndMakeFunMap' p decls
  


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
  
  