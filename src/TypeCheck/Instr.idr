module TypeCheck.Instr

import Control.Monad.State
import Control.Monad.Either

import Data.SortedMap

import LNG.Parsed                   as LNG
import LNG.TypeChecked              as TC
import TypeCheck.Data.Context
import TypeCheck.Data.TypeCheckM
import TypeCheck.Expr
import TypeCheck.Utils

typeCheckExpr' : VarCTX -> Expr -> TypeCheckM (t ** TC.Expr t)
typeCheckExpr' ctx expr = evalStateT ctx $ typeCheckExpr expr

typeCheckExprOfType' : (t : TC.LNGType) -> VarCTX -> Expr -> TypeCheckM (TC.Expr t)
typeCheckExprOfType' t ctx expr = evalStateT ctx $ typeCheckExprOfType t expr

-- TODO: try `typeCheckInstrOfKind`
-- TODO: try linear context
export
typeCheckInstr : (t : TC.LNGType) -> VarCTX -> Instr -> TypeCheckM (VarCTX, (kind : InstrKind t ** TC.Instr kind))

typeCheckInstr t ctx (Block instrs) = do
  (ctx', (k ** instrs')) <- typeCheck' t ctx instrs
  pure (ctx', (k ** TC.Block instrs'))
  
  where
    
    typeCheck' : (t : TC.LNGType) -> VarCTX -> List Instr -> TypeCheckM (VarCTX, (kind : InstrKind t ** TC.Instrs kind))
    
    typeCheck' t ctx [] = pure (ctx, (Simple ** []))
    
    typeCheck' t ctx [instr] = do
      (ctx', (k ** instr')) <- typeCheckInstr t ctx instr
      case k of
        Simple => pure (ctx', (Simple ** [instr']))
        
        -- idris knows the `t` here is the same
        Returning t => pure (ctx', (Returning t ** TC.TermSingleton instr'))
    
    typeCheck' t ctx (instr :: instrs) = do
      (ctx', (k' ** instr')) <- typeCheckInstr t ctx instr
      case k' of
        Simple => do
          (ctx'', (k'' ** instrs')) <- typeCheck' t ctx' instrs
          pure (ctx'', (k'' ** (instr' :: instrs')))
        
        Returning t => throwError ReturnPrecedingInstructions

typeCheckInstr t ctx (Declare ty id expr) = do
  case lookup id ctx of
    Just t' => throwError (VariableAlreadyDeclared id)

    Nothing => do
      expr' <- typeCheckExprOfType' (tc ty) ctx expr
      let ctx' = declare (tc ty) id ctx
      pure (ctx', (Simple ** TC.Assign (mkVar (tc ty) id) expr'))

typeCheckInstr t ctx (Assign id expr) = do
  case lookup id ctx of
    Just t' => do
      expr' <- typeCheckExprOfType' t' ctx expr
      pure (ctx, (Simple ** TC.Assign (mkVar t' id) expr'))

    Nothing => throwError (NoSuchVariable id)

typeCheckInstr t ctx (If cond thn) = do
  cond' <- typeCheckExprOfType' TBool ctx cond
  (_, (_ ** thn')) <- typeCheckInstr t ctx thn
  pure (ctx, (Simple ** TC.If cond' thn'))

typeCheckInstr t ctx (IfElse cond thn els) = do
  cond' <- typeCheckExprOfType' TBool ctx cond
  (_, (thnk ** thn')) <- typeCheckInstr t ctx thn
  (_, (elsk ** els')) <- typeCheckInstr t ctx els
  pure (ctx, (TC.BrKind thnk elsk ** TC.IfElse cond' thn' els'))

typeCheckInstr t ctx (While cond body) = do
  cond' <- typeCheckExprOfType' TBool ctx cond
  (ctx', (kind ** body')) <- typeCheckInstr t ctx body
  pure (ctx', (TC.Simple ** TC.While cond' body'))

typeCheckInstr t ctx (Return expr) = do
  expr' <- typeCheckExprOfType' t ctx expr
  pure (ctx, (Returning t ** TC.Return expr'))

typeCheckInstr t ctx RetVoid = case t of
  TVoid => pure (ctx, (TC.Returning TC.TVoid ** TC.RetVoid))
  -- TODO: make the error contain more info
  _ => throwError TypeError


