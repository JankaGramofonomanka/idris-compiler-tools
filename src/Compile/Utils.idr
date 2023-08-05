module Compile.Utils

import LNG.TypeChecked
import LLVM.Generalized

public export
GetLLType : LNGType -> LLType
GetLLType TInt    = I32
GetLLType TBool   = I1
GetLLType TString = Ptr I8
GetLLType TVoid   = Void

export
addInput : (lbl : BlockLabel)
        -> LLValue var t
        -> PhiExpr var (MkInputs ins) t
        -> PhiExpr var (MkInputs $ lbl :: ins) t

addInput lbl val (Phi t kvs) = Phi t $ (lbl, val) :: kvs


public export
FunVal : (LLType -> Type) -> LNGType -> List LNGType -> Type
FunVal var t ts = LLFun var (GetLLType t) (map GetLLType ts)

public export
FunVal' : (LLType -> Type) -> (LNGType, List LNGType) -> Type
FunVal' var (t, ts) = FunVal var t ts

