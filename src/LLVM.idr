module LLVM

import Data.The
import Data.Typed
import LLVM.Generalized as G
import CFG

-- LLValue --------------------------------------------------------------------
public export
LLValue : LLType -> Type
LLValue = G.LLValue G.Reg

public export
LLFun : LLType -> List LLType -> Type
LLFun t ts = G.LLValue G.Reg (Ptr $ FunType t ts)

public export
LLFun' : (LLType, List LLType) -> Type
LLFun' = G.LLFun' G.Reg



-- Expr -----------------------------------------------------------------------
public export
LLExpr : LLType -> Type
LLExpr = G.LLExpr G.Reg

public export
PhiExpr : Inputs -> LLType -> Type
PhiExpr = G.PhiExpr Reg

-- Isntr ----------------------------------------------------------------------
public export
STInstr : Type
STInstr = G.STInstr G.Reg

public export
CFInstr : (returnType : LLType) -> (kind : CFKind) -> Type
CFInstr = G.CFInstr G.Reg

public export
PhiInstr : Inputs -> Type
PhiInstr = G.PhiInstr G.Reg


-- SimpleBlock ----------------------------------------------------------------
public export
SimpleBlock : (retT : LLType)
           -> (label : BlockLabel)
           -> (inputs : Inputs)
           -> (cfkind : CFKind)
           -> Type
SimpleBlock = G.SimpleBlock G.Reg



public export
BlockVertex : (returnType : LLType) -> Vertex BlockLabel
BlockVertex = G.BlockVertex G.Reg

-- FunDef ---------------------------------------------------------------------
public export
FunDef : (retT : LLType) -> (paramTs : List LLType) -> Type
FunDef = G.FunDef G.Reg

-- ConstDef -------------------------------------------------------------------
public export
ConstDef : Type
ConstDef = G.ConstDef G.Reg

-- Program --------------------------------------------------------------------
public export
Program : Type
Program = G.Program G.Reg

