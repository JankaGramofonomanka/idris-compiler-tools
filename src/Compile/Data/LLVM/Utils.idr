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

export
liftReg : LLValue Reg t -> LLValue Reg' t
liftReg (Var reg) = Var (R reg)
liftReg (Lit lit) = Lit lit
liftReg (ConstPtr cst) = ConstPtr cst
liftReg (Null t) = Null t

