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





