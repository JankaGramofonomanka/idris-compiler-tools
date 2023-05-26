module Interpreter.FunDecl

import Control.Monad.Either
import Control.Monad.State

import Data.SortedMap

import Data.DList
import Interpreter.Data.Error
import Interpreter.Data.InterpreterT
import Interpreter.Semantics
import Interpreter.Instr
import LNG.Parsed
import Parse.Data.Position

ParamTypes : List (^LNGType, ^Ident) -> List LNGType
ParamTypes = map ((^^) . Builtin.fst)

initCTX : Monad m
       => (params : List (^LNGType, ^Ident))
       -> (args : DList Value $ ParamTypes params)
       -> InterpreterT m ()
initCTX Nil Nil = pure ()
initCTX ((t, param) :: params) (arg :: args) = do
  modify $ the (InterpreterState m -> InterpreterState m) { ctx $= insert (^^param) (pos param, ((^^t) ** arg)) }
  initCTX params args




interpretFunBody : Monad m
                => (retT : LNGType)
                -> (params : List (^LNGType, ^Ident))
                -> (args : DList Value $ ParamTypes params)
                -> (body : ^Instr)
                -> InterpreterT m (Value retT)
interpretFunBody retT params args body = do
  initCTX params args

  interpretInstrRet retT body

export
interpretFun : Monad m
            => (decl : FunDecl)
            -> DList Value (ParamTypes $ ^^decl.params)
            -> InterpreterT m $ Value (^^decl.retType)
interpretFun decl args = interpretFunBody (^^decl.retType) (^^decl.params) args decl.body


export
funInterpreter : Monad m => FunDecl -> (t : LNGType ** ts : List LNGType ** Fun t ts (InterpreterT m))
funInterpreter decl = (^^decl.retType ** ParamTypes (^^decl.params) ** interpretFun decl)
