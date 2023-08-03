module Compile.Data.LLVM.Utils

import Data.DList
import Data.Attached

import LNG.TypeChecked
import LLVM.Generalized
import Compile.Data.LLVM as LLVM
import Compile.Utils

public export
FunVal : LNGType -> List LNGType -> Type
FunVal t ts = LLFun (GetLLType t) (map GetLLType ts)

public export
FunVal' : (LNGType, List LNGType) -> Type
FunVal' (t, ts) = FunVal t ts




