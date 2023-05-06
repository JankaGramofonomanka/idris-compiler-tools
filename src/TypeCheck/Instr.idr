module TypeCheck.Instr

import Control.Monad.State
import Control.Monad.Either

import Data.SortedMap

import LNG.Data.Position
import LNG.Parsed                   as LNG
import LNG.TypeChecked              as TC
import TypeCheck.Data.Context
import TypeCheck.Data.TypeCheckM
import TypeCheck.Expr
import TypeCheck.Utils

typeCheckExpr' : VarCTX -> ^Expr -> TypeCheckM (t ** TC.Expr t)
typeCheckExpr' ctx expr = evalStateT ctx $ typeCheckExpr expr

typeCheckExprOfType' : (t : TC.LNGType) -> VarCTX -> ^Expr -> TypeCheckM (TC.Expr t)
typeCheckExprOfType' t ctx expr = evalStateT ctx $ typeCheckExprOfType t expr

-- TODO: try `typeCheckInstrOfKind`
-- TODO: try linear context
export
typeCheckInstr : (t : TC.LNGType) -> VarCTX -> ^Instr -> TypeCheckM (VarCTX, (kind : InstrKind t ** TC.Instr kind))

typeCheckInstr t ctx (_ |^ Block instrs) = do
  (ctx', (k ** instrs')) <- typeCheck' t ctx instrs
  pure (ctx', (k ** TC.Block instrs'))
  
  where
    
    typeCheck' : (t : TC.LNGType) -> VarCTX -> PosList Instr -> TypeCheckM (VarCTX, (kind : InstrKind t ** TC.Instrs kind))
    
    typeCheck' t ctx (Nil p) = pure (ctx, (Simple ** []))
    
    typeCheck' t ctx (instr :: Nil p) = do
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
        
        Returning t => throwError $ returnPrecedingInstructions (headOrNilpos instrs)

typeCheckInstr t ctx (_ |^ Declare ty id expr) = do
  case VarCTX.lookup (^^id) ctx of
    Just (p, t') => throwError (variableAlreadyDeclared id p)

    Nothing => do
      expr' <- typeCheckExprOfType' (tc' ty) ctx expr
      let ctx' = declare (tc' ty) id ctx
      pure (ctx', (Simple ** TC.Assign (mkVar (tc' ty) (^^id)) expr'))

typeCheckInstr t ctx (_ |^ Assign id expr) = do
  case VarCTX.lookup (^^id) ctx of
    Just (p, t') => do
      expr' <- typeCheckExprOfType' t' ctx expr
      pure (ctx, (Simple ** TC.Assign (mkVar t' $ ^^id) expr'))

    Nothing => throwError (noSuchVariable id)

typeCheckInstr t ctx (_ |^ If cond thn) = do
  cond' <- typeCheckExprOfType' TBool ctx cond
  (_, (_ ** thn')) <- typeCheckInstr t ctx thn
  pure (ctx, (Simple ** TC.If cond' thn'))

typeCheckInstr t ctx (_ |^ IfElse cond thn els) = do
  cond' <- typeCheckExprOfType' TBool ctx cond
  (_, (thnk ** thn')) <- typeCheckInstr t ctx thn
  (_, (elsk ** els')) <- typeCheckInstr t ctx els
  pure (ctx, (TC.BrKind thnk elsk ** TC.IfElse cond' thn' els'))

typeCheckInstr t ctx (_ |^ While cond body) = do
  cond' <- typeCheckExprOfType' TBool ctx cond
  (ctx', (kind ** body')) <- typeCheckInstr t ctx body
  pure (ctx', (TC.Simple ** TC.While cond' body'))

typeCheckInstr t ctx (_ |^ Return expr) = do
  expr' <- typeCheckExprOfType' t ctx expr
  pure (ctx, (Returning t ** TC.Return expr'))

typeCheckInstr t ctx (p |^ RetVoid) = case t of
  TVoid => pure (ctx, (TC.Returning TC.TVoid ** TC.RetVoid))
  t => throwError $ typeError p t TVoid


