module Compile.Utils

import Data.DList
import Data.Attached

import LNG.TypeChecked
import LLVM

||| An LLVM representation of an LNG type
public export
GetLLType : LNGType -> LLType
GetLLType TInt    = I32
GetLLType TBool   = I1
GetLLType TString = Ptr I8
GetLLType TVoid   = Void

||| A type of LLVM function pointers representing a function of the given LNG
||| signature.
public export
FunVal : LNGType -> List LNGType -> Type
FunVal t ts = LLFun (GetLLType t) (map GetLLType ts)

||| An alias for `FunVal` (which is an alias for `LLFun` which is an alias for
||| `LLValue`) parametrized by a tuple instead of two separate parameters
public export
FunVal' : (LNGType, List LNGType) -> Type
FunVal' (t, ts) = FunVal t ts

||| Extend the inputs of a phi expression by adding a value to it
||| @ lbl the label of the extention
||| @ ins the inputs to be extended
||| @ val the value
||| @ phi the expression to be extended
export
addInput : (lbl : Label)
        -> (val : LLValue t)
        -> (phi : PhiExpr ins t)
        -> PhiExpr (lbl :: ins) t
addInput lbl val (Phi t kvs) = Phi t $ (lbl, val) :: kvs
