module Compile.Data.Effect

import Data.Attached
import Data.DList

import LLVM

import Compile.Data.Context
import Compile.Utils
import CFG

import Utils

data Incoming : Neighbors Label -> Label ->  Type where
  UIncoming : lbl :~: VarCTX                    -> Incoming Undefined   lbl
  DIncoming : DList (:~: VarCTX) (lbls ~~> lbl) -> Incoming (Just lbls) lbl

data Outgoing : Label -> Neighbors Label -> Type where
  UOutgoing : lbl :~: VarCTX                    -> Outgoing lbl Undefined
  DOutgoing : DList (:~: VarCTX) (lbl ~>> lbls) -> Outgoing lbl (Just lbls)

CBlockEffect
   : (lbl  : Label)
  -> (ins  : Neighbors Label)
  -> (outs : Neighbors Label)
  -> Type
CBlockEffect lbl ins outs = (lbl, ins, outs) :~: (VarCTX -> VarCTX)

combine : {lbl : Label} -> {ins, outs : Neighbors Label} -> CBlockEffect lbl ins Nothing -> CBlockEffect lbl Nothing outs -> CBlockEffect lbl ins outs
combine {lbl, ins, outs} eff eff' = attach (lbl, ins, outs) (detach eff' . detach eff)

CFGEffect
