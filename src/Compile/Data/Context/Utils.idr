module Compile.Data.Context.Utils


import Control.Monad.State

import Data.Attached
import Data.DMap
import Data.DList
import Data.DSum
import Data.GCompare
import Data.Some
import Data.The
import Data.Typed
import LNG.TypeChecked
import LLVM
import Compile.Data.CompM
import Compile.Data.Context
import Compile.Utils
import CFG


public export
record Segregated (lbl : BlockLabel) (ins : Inputs) where
  constructor SG
  ctx : lbl :~: VarCTX
  phis : List (PhiInstr ins)


-- TODO: Consider rewriting `PhiExpr` so that it equals to this type
data Phi' : BlockLabel -> Inputs -> LLType -> Type where
  MkPhi' : (t : LLType) -> DList (:~: LLValue t) (ins ~~> lbl) -> Phi' lbl (MkInputs ins) t

implementation Typed (Phi' lbl ins) where
  typeOf (MkPhi' t _) = MkThe t

toPhi : {ins : Inputs} -> Phi' lbl ins t -> PhiExpr ins t
toPhi {ins = MkInputs Nil} (MkPhi' t Nil) = Phi t Nil
toPhi {ins = MkInputs (lbl :: lbls)} (MkPhi' t (val :: vals)) = let
    Phi t pairs = toPhi {ins = MkInputs lbls} (MkPhi' t vals)
  in Phi t ((lbl, detach val) :: pairs)


ValueOrPhi : BlockLabel -> Inputs -> LNGType -> Type
ValueOrPhi lbl ins t = Either (Phi' lbl ins $ GetLLType t) (LLValue $ GetLLType t)

record Segregated' (lbl : BlockLabel) (ins : Inputs) where
  constructor SG'
  ctx : DMap Variable (ValueOrPhi lbl ins)




replicatePhi : (ins : List BlockLabel) -> LLValue t -> PhiExpr (MkInputs ins) t
replicatePhi {t} Nil val = case the (The t) (typeOf val) of { MkThe t' => Phi t' Nil }
replicatePhi (lbl :: lbls) val = addInput lbl val $ replicatePhi lbls val



addInput' : (lbl ~> lbl') :~: (LLValue t)
         -> Phi' lbl' (MkInputs ins) t
         -> Phi' lbl' (MkInputs $ lbl :: ins) t

addInput' val (MkPhi' t kvs) = MkPhi' t $ val :: kvs

replicatePhi' : (ins : List BlockLabel) -> LLValue t -> Phi' lbl' (MkInputs ins) t
replicatePhi' {t} Nil val = case the (The t) (typeOf val) of { MkThe t' => MkPhi' t' Nil }
replicatePhi' {lbl'} (lbl :: lbls) val = addInput' (attach (lbl ~> lbl') val) $ replicatePhi' lbls val



addValueOrPhi : Variable t
             -> (lbl ~> lbl') :~: (LLValue (GetLLType t))
             -> {ins : List BlockLabel}
             -> ValueOrPhi lbl' (MkInputs ins) t
             -> Segregated' lbl' (MkInputs $ lbl :: ins)
             -> Segregated' lbl' (MkInputs $ lbl :: ins)

addValueOrPhi key val (Right val') (SG' ctx)

  = if val' == detach val then
      SG' (DMap.insert key (Right val') ctx)

    else let
    
      phi = addInput' val $ replicatePhi' ins val'
      
      in SG' (DMap.insert key (Left phi) ctx)

addValueOrPhi key val (Left phi) (SG' ctx) = let

  phi' = addInput' val phi
  
  in SG' (DMap.insert key (Left phi') ctx)




addCTX : (lbl ~> lbl') :~: VarCTX
      -> {ins : List BlockLabel}
      -> Segregated' lbl' (MkInputs ins)
      -> Segregated' lbl' (MkInputs $ lbl :: ins)

addCTX ctx {ins} (SG' ctx')
  = foldl handleItem (SG' DMap.empty) (distribute $ map VarCTX.toList ctx)
  
  where

    handleItem : Segregated' lbl' (MkInputs $ lbl :: ins)
              -> (lbl ~> lbl') :~: DSum Variable (LLValue . GetLLType)
              -> Segregated' lbl' (MkInputs $ lbl :: ins)

    handleItem sg item = let

      MkSome item' = inSome $ map toSome item
      
      key = detach $ map fst item'
      val = map snd item'
            
      in case DMap.lookup key ctx' of
        Nothing => sg
      
        Just vp => addValueOrPhi key val vp sg



finalize : {ins : Inputs} -> Segregated' lbl ins -> CompM (Segregated lbl ins)
finalize {ins, lbl} (SG' ctx) = foldlM handleItem (SG (attach lbl VarCTX.empty) Nil) (toList ctx) where
  
  handleItem : Segregated lbl ins
   -> DSum Variable (ValueOrPhi lbl ins)
   -> CompM (Segregated lbl ins)
  
  handleItem (SG ctx' phis) (key :=> vp) = case vp of
    
    Right val => pure $ SG (map (DMap.insert key val) ctx') phis

    Left phi => do
      reg <- freshRegister' (typeOf phi) 
      let phi = AssignPhi reg (toPhi phi)
      
      pure $ SG (map (DMap.insert key (Var reg)) ctx') (phi :: phis)
    
    
{-
TODO: add another case, the second parameter being [ctx]
currently `addCTX` drops values that were not found in the accumulator which is
empty at the beginning. Thus the entrie context will be empty
-}
segregate' : {lbls : List BlockLabel}
          -> DList (:~: VarCTX) (lbls ~~> lbl)
          -> Segregated' lbl (MkInputs lbls)
segregate' {lbls = Nil} Nil = SG' DMap.empty
segregate' {lbls = l :: ls} (ctx :: ctxs) = addCTX ctx (segregate' ctxs)



-- TODO: consider another name - `merge`
{-
Combine contexts from different branches by adding phi instructions in case of
conflicting values
-}
export
segregate : {lbls : List BlockLabel}
         -> DList (:~: VarCTX) (lbls ~~> lbl)
         -> CompM $ Segregated lbl (MkInputs lbls)
segregate ctxs = finalize (segregate' ctxs)


export
newRegForAll : List (t ** Variable t) -> CompM VarCTX'
newRegForAll vars = foldlM addNewReg DMap.empty vars

  where
    
    addNewReg : VarCTX'
             -> (t ** Variable t)
             -> CompM VarCTX'
    
    addNewReg ctx (t ** var) = pure (VarCTX'.insert var !(freshRegister $ GetLLType t) ctx)


export
commonKeys : DList (:~: VarCTX) lbls -> List (t ** Variable t)
commonKeys ctxs = VarCTX.keys (intersection' ctxs) where

  intersection' : DList (:~: VarCTX) lbls' -> VarCTX
  intersection' Nil = VarCTX.empty
  intersection' (ctx :: ctxs) = VarCTX.intersection (detach ctx) (intersection' ctxs)

  



