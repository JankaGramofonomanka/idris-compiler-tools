module Compile.Utils

import Data.DList
import Data.Attached

import LNG.TypeChecked
import LLVM

public export
GetLLType : LNGType -> LLType
GetLLType TInt    = I32
GetLLType TBool   = I1
GetLLType TString = Ptr I8
GetLLType TVoid   = Void

public export
FunVal : LNGType -> List LNGType -> Type
FunVal t ts = LLFun (GetLLType t) (map GetLLType ts)

public export
FunVal' : (LNGType, List LNGType) -> Type
FunVal' (t, ts) = FunVal t ts



export
addInput : (lbl : Label)
        -> LLValue t
        -> PhiExpr ins t
        -> PhiExpr (lbl :: ins) t

addInput lbl val (Phi t kvs) = Phi t $ (lbl, val) :: kvs





