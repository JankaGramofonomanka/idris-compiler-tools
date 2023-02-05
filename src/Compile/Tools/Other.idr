module Compile.Tools.Other

import Data.DList
import Data.Attached

import LLVM

export
addInput : (lbl : BlockLabel)
        -> LLValue t
        -> PhiExpr (MkInputs ins) t
        -> PhiExpr (MkInputs $ lbl :: ins) t

addInput lbl val (Phi kvs) = Phi $ (lbl, val) :: kvs

export
phiFromDList : (lbls : List BlockLabel)
            -> DList (\lbl => Attached lbl (LLValue t)) lbls
            -> PhiExpr (MkInputs lbls) t

phiFromDList Nil Nil = Phi Nil
phiFromDList (lbl :: lbls) (val :: vals)
  = addInput lbl (detach val) (phiFromDList lbls vals)



