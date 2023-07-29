module TypeCheck.Instr

import Control.Monad.State
import Control.Monad.Either

import Data.SortedMap

import LNG.Parsed                   as LNG
import LNG.TypeChecked              as TC
import Parse.Data.Position
import TypeCheck.Data.Context
import TypeCheck.Data.Error
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
typeCheckInstr : (rt : TC.LNGType) -> VarCTX -> ^Instr -> TypeCheckM (VarCTX, (kind : InstrKind ** TC.Instr rt kind))

typeCheckInstr t ctx (_ |^ Block instrs) = do
  (ctx', (k ** instrs')) <- typeCheck' t ctx (^^instrs)
  pure (ctx', (k ** TC.Block instrs'))
  
  where
    
    typeCheck' : (rt : TC.LNGType)
              -> VarCTX
              -> List (^Instr)
              -> TypeCheckM (VarCTX, (kind : InstrKind ** TC.Instrs rt kind))
    
    typeCheck' t ctx Nil = pure (ctx, (Simple ** []))
    
    typeCheck' t ctx (instr :: Nil) = do
      (ctx', (k ** instr')) <- typeCheckInstr t ctx instr
      case k of
        Simple => pure (ctx', (Simple ** [instr']))
        
        -- idris knows the `t` here is the same
        Returning => pure (ctx', (Returning ** TC.TermSingleton instr'))
    
    typeCheck' t ctx (instr1 :: instr2 :: instrs) = do
      (ctx', (k' ** instr1')) <- typeCheckInstr t ctx instr1
      case k' of
        Simple => do
          (ctx'', (k'' ** instrs')) <- typeCheck' t ctx' (instr2 :: instrs)
          pure (ctx'', (k'' ** (instr1' :: instrs')))
        
        Returning => throwError $ returnPrecedingInstructions (pos instr2)

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

typeCheckInstr t ctx (_ |^ Exec expr) = do
  expr' <- typeCheckExprOfType' TVoid ctx expr
  pure (ctx, (Simple ** TC.Exec expr'))

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
  pure (ctx, (Returning ** TC.Return expr'))

typeCheckInstr t ctx (p |^ RetVoid) = case t of
  TVoid => pure (ctx, (TC.Returning ** TC.RetVoid))
  t => throwError $ typeError p t TVoid


