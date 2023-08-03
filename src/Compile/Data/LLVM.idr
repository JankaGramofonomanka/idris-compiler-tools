module Compile.Data.LLVM

import Data.The
import Data.Typed
import CFG
import Compile.Utils
import LLVM.Generalized as G
import LNG.TypeChecked

public export
data Reg' : LLType -> Type where
  Placeholder : Variable t -> Reg' (GetLLType t)
  R : Reg t -> Reg' t

export
implementation Typed Reg' where
  typeOf (Placeholder var) = map GetLLType (typeOf var)
  typeOf (R reg) = typeOf reg

-- LLValue --------------------------------------------------------------------
public export
LLValue : LLType -> Type
LLValue = G.LLValue Reg'

public export
LLFun : LLType -> List LLType -> Type
LLFun t ts = G.LLValue Reg' (Ptr $ FunType t ts)

public export
LLFun' : (LLType, List LLType) -> Type
LLFun' = G.LLFun' Reg'



-- Expr -----------------------------------------------------------------------
public export
LLExpr : LLType -> Type
LLExpr = G.LLExpr Reg'

public export
PhiExpr : Inputs -> LLType -> Type
PhiExpr = G.PhiExpr Reg'

-- Isntr ----------------------------------------------------------------------
public export
STInstr : Type
STInstr = G.STInstr Reg'

public export
CFInstr : (returnType : LLType) -> (kind : CFKind) -> Type
CFInstr = G.CFInstr Reg'

public export
PhiInstr : Inputs -> Type
PhiInstr = G.PhiInstr Reg'


-- SimpleBlock ----------------------------------------------------------------
public export
SimpleBlock : (retT : LLType)
           -> (label : BlockLabel)
           -> (inputs : Inputs)
           -> (cfkind : CFKind)
           -> Type
SimpleBlock = G.SimpleBlock Reg'



public export
BlockVertex : (returnType : LLType) -> Vertex BlockLabel
BlockVertex = G.BlockVertex Reg'

-- FunDef ---------------------------------------------------------------------
public export
FunDef : (retT : LLType) -> (paramTs : List LLType) -> Type
FunDef = G.FunDef Reg'

-- ConstDef -------------------------------------------------------------------
public export
ConstDef : Type
ConstDef = G.ConstDef Reg'

-- Program --------------------------------------------------------------------
public export
Program : Type
Program = G.Program Reg'

