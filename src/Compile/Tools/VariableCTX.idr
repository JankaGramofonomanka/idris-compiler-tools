module Compile.Tools.VariableCTX

import Control.Monad.State

import Data.DMap
import Data.DList
import Data.Attached
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


-- TODO: rewrite `PhiExpr` so that it equals to this type or implement `toPhi`
data Phi' : Inputs -> LLType -> Type where
  MkPhi' : DList (\lbl => Attached lbl $ LLValue t) ins -> Phi' (MkInputs ins) t


toPhi : Phi' ins t -> PhiExpr ins t


ValueOrPhi : Inputs -> LNGType -> Type
ValueOrPhi ins t = Either (Phi' ins $ GetLLType t) (LLValue $ GetLLType t)

record Segregated' (ins : Inputs) where
  constructor SG'
  ctx : DMap Variable (ValueOrPhi ins)




addInput : (lbl : BlockLabel)
        -> LLValue t
        -> PhiExpr (MkInputs ins) t
        -> PhiExpr (MkInputs $ lbl :: ins) t

addInput lbl val (Phi kvs) = Phi $ (lbl, val) :: kvs

replicatePhi : (ins : List BlockLabel) -> LLValue t -> PhiExpr (MkInputs ins) t
replicatePhi Nil val = Phi Nil
replicatePhi (lbl :: lbls) val = addInput lbl val $ replicatePhi lbls val




addInput' : Attached lbl (LLValue t)
         -> Phi' (MkInputs ins) t
         -> Phi' (MkInputs $ lbl :: ins) t

addInput' val (MkPhi' kvs) = MkPhi' $ val :: kvs

replicatePhi' : (ins : List BlockLabel) -> LLValue t -> Phi' (MkInputs ins) t
replicatePhi' Nil val = MkPhi' Nil
replicatePhi' (lbl :: lbls) val = addInput' (attach lbl val) $ replicatePhi' lbls val



addValueOrPhi : Variable t
             -> Attached lbl (LLValue (GetLLType t))
             -> {ins : List BlockLabel}
             -> ValueOrPhi (MkInputs ins) t
             -> Segregated' (MkInputs $ lbl :: ins)
             -> Segregated' (MkInputs $ lbl :: ins)

addValueOrPhi key val (Right val') (SG' ctx)

  = if val' == detach val then
      SG' (DMap.insert key (Right val') ctx)

    else let
    
      phi = addInput' val $ replicatePhi' ins val'
      
      in SG' (DMap.insert key (Left phi) ctx)

addValueOrPhi key val (Left phi) (SG' ctx) = let

  phi' = addInput' val phi
  
  in SG' (DMap.insert key (Left phi') ctx)




addCTX : Attached lbl VarCTX
      -> {ins : List BlockLabel}
      -> Segregated' (MkInputs ins)
      -> Segregated' (MkInputs $ lbl :: ins)

addCTX ctx {ins} (SG' ctx')
  = foldl handleItem (SG' DMap.empty) (distribute $ map DMap.toList ctx)
  
  where

    handleItem : Segregated' (MkInputs $ lbl :: ins)
              -> Attached lbl (t : LNGType ** Item Variable (LLValue . GetLLType) t)
              -> Segregated' (MkInputs $ lbl :: ins)

    handleItem sg item = let

      item' = snd $ detachParam item
      
      key = detach $ map (.key) item'
      val = map (.val) item'
      
      in case DMap.lookup key ctx' of
        Nothing => sg
      
        Just vp => addValueOrPhi key val vp sg



finalize : Segregated' ins -> CompM (Segregated ins)
finalize (SG' ctx) = foldlM handleItem (SG emptyCtx Nil) (toList ctx) where
  
  handleItem : Segregated ins
   -> (t : LNGType ** Item Variable (ValueOrPhi ins) t)
   -> CompM (Segregated ins)
  
  handleItem (SG ctx' phis) (x ** MkItem key vp) = case vp of
    
    Right val => pure $ SG (insert key val ctx') phis

    Left phi => do
      reg <- freshReg
      let phi = AssignPhi reg (toPhi phi)
      
      pure $ SG (insert key (Var reg) ctx') (phi :: phis)
    
    
segregate' : {labels : List BlockLabel}
          -> DList (\lbl => Attached lbl VarCTX) labels
          -> Segregated' (MkInputs labels)
segregate' Nil = SG' DMap.empty
segregate' (ctx :: ctxs) = addCTX ctx (segregate' ctxs)




export
segregate : {labels : List BlockLabel}
          -> DList (\lbl => Attached lbl VarCTX) labels
          -> CompM $ Segregated (MkInputs labels)
segregate ctxs = finalize (segregate' ctxs)
