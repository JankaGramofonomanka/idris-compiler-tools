module Compile.Data.Context.Utils


import Control.Monad.State

import Data.Attached
import Data.DMap
import Data.DList
import Data.Doc
import Data.DSum
import Data.GCompare
import Data.Some
import Data.The
import Data.Typed
import LNG.TypeChecked
import LNG.TypeChecked.Render
import LLVM
import Compile.Data.CompM
import Compile.Data.Context
import Compile.Data.Error
import Compile.Utils
import CFG


public export
record Segregated (lbl : Label) (ins : List Label) where
  constructor SG
  ctx : lbl :~: VarCTX
  phis : List (PhiInstr ins, Maybe String)


-- TODO: Consider rewriting `PhiExpr` so that it equals to this type
data Phi' : Label -> List Label -> LLType -> Type where
  MkPhi' : (t : LLType) -> DList (:~: LLValue t) (ins ~~> lbl) -> Phi' lbl ins t

implementation Typed (Phi' lbl ins) where
  typeOf (MkPhi' t _) = MkThe t

toPhi : {ins : List Label} -> Phi' lbl ins t -> PhiExpr ins t
toPhi {ins = Nil} (MkPhi' t Nil) = Phi t Nil
toPhi {ins = lbl :: lbls} (MkPhi' t (val :: vals)) = let
    Phi t pairs = toPhi {ins = lbls} (MkPhi' t vals)
  in Phi t ((lbl, detach val) :: pairs)


ValueOrPhi : Label -> List Label -> LNGType -> Type
ValueOrPhi lbl ins t = Either (Phi' lbl ins $ GetLLType t) (LLValue $ GetLLType t)

record Segregated' (lbl : Label) (ins : List Label) where
  constructor SG'
  ctx : DMap Variable (ValueOrPhi lbl ins)




replicatePhi : (ins : List Label) -> LLValue t -> PhiExpr ins t
replicatePhi {t} Nil val = case the (The t) (typeOf val) of { MkThe t' => Phi t' Nil }
replicatePhi (lbl :: lbls) val = addInput lbl val $ replicatePhi lbls val



addInput' : (lbl ~> lbl') :~: (LLValue t)
         -> Phi' lbl' ins t
         -> Phi' lbl' (lbl :: ins) t

addInput' val (MkPhi' t kvs) = MkPhi' t $ val :: kvs

replicatePhi' : (ins : List Label) -> LLValue t -> Phi' lbl' ins t
replicatePhi' {t} Nil val = case the (The t) (typeOf val) of { MkThe t' => MkPhi' t' Nil }
replicatePhi' {lbl'} (lbl :: lbls) val = addInput' (attach (lbl ~> lbl') val) $ replicatePhi' lbls val



addValueOrPhi : Variable t
             -> (lbl ~> lbl') :~: (LLValue (GetLLType t))
             -> {ins : List Label}
             -> ValueOrPhi lbl' ins t
             -> Segregated' lbl' (lbl :: ins)
             -> Segregated' lbl' (lbl :: ins)

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
      -> {ins : List Label}
      -> Segregated' lbl' ins
      -> Segregated' lbl' (lbl :: ins)

addCTX ctx {ins} (SG' ctx')
  = foldl handleItem (SG' DMap.empty) (distribute $ map VarCTX.toList ctx)
  
  where

    handleItem : Segregated' lbl' (lbl :: ins)
              -> (lbl ~> lbl') :~: DSum Variable (LLValue . GetLLType)
              -> Segregated' lbl' (lbl :: ins)

    handleItem sg item = let

      MkSome item' = inSome $ map toSome item
      
      key = detach $ map fst item'
      val = map snd item'
            
      in case DMap.lookup key ctx' of
        Nothing => sg
      
        Just vp => addValueOrPhi key val vp sg



finalize : {ins : List Label} -> Segregated' lbl ins -> CompM (Segregated lbl ins)
finalize {ins, lbl} (SG' ctx) = foldlM handleItem (SG (attach lbl VarCTX.empty) Nil) (toList ctx) where
  
  handleItem : Segregated lbl ins
   -> DSum Variable (ValueOrPhi lbl ins)
   -> CompM (Segregated lbl ins)
  
  handleItem (SG ctx' phis) (key :=> vp) = case vp of
    
    Right val => pure $ SG (map (DMap.insert key val) ctx') phis

    Left phi => do
      reg <- freshRegister' (typeOf phi) 
      let phi = AssignPhi reg (toPhi phi)
      
      pure $ SG (map (DMap.insert key (Var reg)) ctx') ((phi, Just $ prt key) :: phis)
    
    
segregate' : {lbls : List Label}
          -> DList (:~: VarCTX) (lbls ~~> lbl)
          -> Segregated' lbl lbls
segregate' {lbls = Nil}       Nil           = SG' DMap.empty
segregate' {lbls = l :: Nil}  (ctx :: Nil)  = SG' { ctx = map Right (detach ctx) }
segregate' {lbls = l :: ls}   (ctx :: ctxs) = addCTX ctx (segregate' ctxs)



-- TODO: consider another name - `merge`
{-
Combine contexts from different branches by adding phi instructions in case of
conflicting values
-}
export
segregate : {lbls : List Label}
         -> DList (:~: VarCTX) (lbls ~~> lbl)
         -> CompM $ Segregated lbl lbls
segregate ctxs = finalize (segregate' ctxs)


newRegForAll' : List (t ** Variable t) -> CompM VarCTX'
newRegForAll' vars = foldlM addNewReg DMap.empty vars

  where
    
    addNewReg : VarCTX'
             -> (t ** Variable t)
             -> CompM VarCTX'
    
    addNewReg ctx (t ** var) = pure (VarCTX'.insert var !(freshRegister $ GetLLType t) ctx)


commonKeys : DList (:~: VarCTX) lbls -> List (t ** Variable t)
commonKeys ctxs = VarCTX.keys (intersection' ctxs) where

  intersection' : DList (:~: VarCTX) lbls' -> VarCTX
  intersection' Nil = VarCTX.empty
  intersection' (ctx :: Nil) = detach ctx
  intersection' (ctx :: ctxs) = VarCTX.intersection (detach ctx) (intersection' ctxs)

export
newRegForAll : DList (:~: VarCTX) (from ~~> to)
             -> CompM (to :~: VarCTX')
newRegForAll {to} ctxs = attach to <$> newRegForAll' (commonKeys ctxs)



