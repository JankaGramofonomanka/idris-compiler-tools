module Interpreter.Instr

import Control.Monad.Either
import Control.Monad.State

import Data.SortedMap

import Interpreter.Expr
import Interpreter.InterpreterT
import Interpreter.Semantics
import LNG.Parsed
import Parse.Data.Position

export
interpretInstr : Monad m => ^Instr -> InterpreterT m ()

interpretInstr (p |^ Block instrs) = interpret (^^instrs) where
  
  interpret : List (^Instr) -> InterpreterT m ()
  interpret Nil = throwError $ missingReturnInstr (pos instrs)
  interpret (instr :: Nil) = interpretInstr instr
  interpret (instr :: instrs) = do
    interpretInstr instr
    interpret instrs

interpretInstr (p |^ Declare ty var expr) = do

  Nothing <- gets $ lookup (^^var) . ctx
          | Just (p', _) => throwError $ variableAlreadyDeclared var p'

  val <- interpretExprOfType (^^ty) expr
  modify $ the (InterpreterState m -> InterpreterState m) { ctx $= insert (^^var) (p, (^^ty ** val)) }

  pure ()

interpretInstr (p |^ Assign var expr) = do
  Just (_, (ty ** _)) <- gets $ lookup (^^var) . ctx
                       | Nothing => throwError $ noSuchVariable var

  val <- interpretExprOfType ty expr
  modify $ the (InterpreterState m -> InterpreterState m) { ctx $= insert (^^var) (p, (ty ** val)) }
  
  pure ()

interpretInstr (p |^ If cond thn) = do
  cond' <- interpretExprOfType TBool cond
  
  if cond' then interpretInstr thn
           else pure ()

interpretInstr (p |^ IfElse cond thn els) = do
  cond' <- interpretExprOfType TBool cond
  
  if cond' then interpretInstr thn
           else interpretInstr els

interpretInstr (p |^ While cond body) = do
  cond' <- interpretExprOfType TBool cond
  if cond'
    then do
      interpretInstr body
      interpretInstr (p |^ While cond body)
    else
      pure ()

interpretInstr (p |^ Return expr) = throwError $ returnPrecedingInstructions p
interpretInstr (p |^ RetVoid) = throwError $ returnPrecedingInstructions p


export
interpretInstrRet : Monad m => (t : LNGType) -> ^Instr -> InterpreterT m (Value t)

interpretInstrRet t (p |^ Declare ty var expr)  = throwError $ missingReturnInstr p
interpretInstrRet t (p |^ Assign var expr)      = throwError $ missingReturnInstr p
interpretInstrRet t (p |^ If cond thn)          = throwError $ missingReturnInstr p
interpretInstrRet t (p |^ While cond body)      = throwError $ missingReturnInstr p

interpretInstrRet t (p |^ Block instrs) = interpret (^^instrs) where
  
  interpret : List (^Instr) -> InterpreterT m (Value t)
  interpret Nil = throwError $ missingReturnInstr (pos instrs)
  interpret (instr :: Nil) = interpretInstrRet t instr
  interpret (instr :: instrs) = do
    interpretInstr instr
    interpret instrs

interpretInstrRet t (p |^ IfElse cond thn els) = do
  cond' <- interpretExprOfType TBool cond
  
  if cond' then interpretInstrRet t thn
           else interpretInstrRet t els

interpretInstrRet t (p |^ Return expr) = interpretExprOfType t expr

interpretInstrRet TVoid (p |^ RetVoid) = pure ()

interpretInstrRet t (p |^ RetVoid) = throwError $ typeError p t TVoid
