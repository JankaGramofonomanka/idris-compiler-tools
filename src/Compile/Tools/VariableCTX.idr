module Compile.Tools.VariableCTX

import Control.Monad.State

import Data.DMap
import LNG
import LLVM
import Compile.Tools
import Compile.Tools.CompM




public export
VarCTX : Type
VarCTX = DMap Variable (LLValue . GetLLType)



export
lookup : Variable t -> VarCTX -> Maybe (LLValue (GetLLType t))
lookup var ctx = DMap.lookup var ctx

export
insert : Variable t -> LLValue (GetLLType t) -> VarCTX -> VarCTX
insert var val ctx = DMap.insert var val ctx



export
emptyCtx : VarCTX
emptyCtx = DMap.empty


public export
record Segregated (ins : Inputs) where
  constructor SG
  ctx : VarCTX
  phis : List (PhiInstr ins)

export
segregate : VarCTX
         -> VarCTX
         -> {lbl, lbl' : BlockLabel}
         -> CompM $ Segregated (MkInputs [lbl, lbl'])

-- TODO: enforce that `ctx`, `ctx'` and `ctx''` aren't mistaken for each other
segregate ctx ctx' {lbl, lbl'} = foldlM f (SG emptyCtx Nil) (toList ctx) where
  
  f : Segregated (MkInputs [lbl, lbl'])
   -> (t : LNGType ** (Variable t, LLValue (GetLLType t)))
   -> CompM (Segregated (MkInputs [lbl, lbl']))
  
  f (SG ctx'' phis) (x ** (key, val)) = case lookup key ctx' of
    Nothing => pure $ SG ctx'' phis
    
    Just val'
      => if val' == val then
          pure $ SG (insert key val ctx'') phis
        else do
          reg <- freshReg

          pure $ SG (insert key (Var reg) ctx'') (AssignPhi reg (Phi [(lbl, val), (lbl', val')]) :: phis)



