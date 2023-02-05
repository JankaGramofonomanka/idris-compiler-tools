module Compile.Tools.Other

import LLVM

export
addInput : (lbl : BlockLabel)
        -> LLValue t
        -> PhiExpr (MkInputs ins) t
        -> PhiExpr (MkInputs $ lbl :: ins) t

addInput lbl val (Phi kvs) = Phi $ (lbl, val) :: kvs
