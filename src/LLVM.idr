module LLVM

import Data.DList
import Data.Some


public export
data LLType
  = I Nat
  -- TODO: floats?, what else?
  -- | F ?
  | Void
  | Ptr LLType
  | Array LLType Nat

  {-
    TODO: how to parametrize structs?
    with struct name and then get the contents of the struct from a context
    or have the contents in the parameter?
    The latter aproach allows multiple structs with the same name
  -} 
  -- | Struct ?

  -- TODO: wasn't VTable a type of struct?
  -- | VTable ?
  | FunType LLType (List LLType)

public export
I1    : LLType
I1    = I 1

public export
I8    : LLType
I8    = I 8

public export
I16   : LLType
I16   = I 16

public export
I32   : LLType
I32   = I 32

public export
I64   : LLType
I64   = I 64

public export
I128  : LLType
I128  = I 128

public export
data Reg : LLType -> Type where
  MkReg : String -> Reg t

public export
data Const : LLType -> Type where
  MkConst : String -> Const t

public export
data LLValue : LLType -> Type where
  Var : Reg t -> LLValue t
  ILit : Integer -> LLValue (I n)
  ConstPtr : Const t -> LLValue (Ptr t)
  Null : LLValue (Ptr t)

public export
data BinOperator : LLType -> LLType -> LLType -> Type where
  ADD   : BinOperator (I n) (I n) (I n)
  SUB   : BinOperator (I n) (I n) (I n)
  MUL   : BinOperator (I n) (I n) (I n)
  SDIV  : BinOperator (I n) (I n) (I n)
  UDIV  : BinOperator (I n) (I n) (I n)
  SREM  : BinOperator (I n) (I n) (I n)
  UREM  : BinOperator (I n) (I n) (I n)

-- TODO: parametrise this?
-- what types can be compared?
public export
data CMPKind = EQ | NE | SGT | SGE | SLT | SLE | UGT | UGE | ULT | ULE

public export
data BlockKind = Entry | NonEntry

public export
data BlockLabel : BlockKind -> Type where
  LEntry : BlockLabel Entry
  LName : String -> BlockLabel NonEntry

export
implementation Eq (BlockLabel k) where
  LEntry == LEntry = True
  LName s == LName s' = s == s'

public export
data FinishKind = Return | Jump (List $ BlockLabel NonEntry)



public export
data Inputs : BlockKind -> Type where
  NoInputs : Inputs Entry
  MkInputs : List (Some BlockLabel) -> Inputs NonEntry



public export
data BlockContext : BlockKind -> Type where
  
  Start : Inputs kind -> BlockContext kind
  Proper : BlockContext kind
  Finish : FinishKind -> BlockContext kind


public export
data LLExpr : {k : BlockKind} -> BlockContext k -> LLType -> Type where
  BinOperation : BinOperator tl tr t -> LLValue tl -> LLValue tr -> LLExpr Proper t
  Call : LLValue (Ptr (FunType t ts)) -> DList LLValue ts -> LLExpr Proper t

  -- TODO: geleelementptr

  -- TODO what about pointers
  -- TODO fcmp, dcmp? what else?
  ICMP : CMPKind -> LLValue (I n) -> LLValue (I n) -> LLExpr Proper (I n)

  Load : LLValue (Ptr t) -> LLExpr Proper t

  BitCast : LLValue t1 -> (t2 : LLType) -> LLExpr Proper t2

  Phi : (l : List (Some BlockLabel, LLValue t)) -> LLExpr (Start . MkInputs $ map (\t => fst t) l) t


public export
data LLInstr : {k : BlockKind} -> BlockContext k -> Type where
  Assign : Reg t -> LLExpr ctx t -> LLInstr ctx
  Exec : LLExpr Proper Void -> LLInstr Proper
  Store : LLValue t -> LLValue (Ptr t) -> LLInstr Proper

  Branch : (l : BlockLabel NonEntry) -> LLInstr (Finish $ Jump [l])
  CondBranch : LLValue I1 -> (l1 : BlockLabel NonEntry) -> (l1 : BlockLabel NonEntry) -> LLInstr (Finish $ Jump [l1, l2])

  Ret : LLValue t -> LLInstr (Finish Return)
  RetVoid : LLInstr (Finish Return)


public export
record SimpleBlock (kind : BlockKind) (label : BlockLabel kind) (inputs : Inputs kind) (output : FinishKind) where
  constructor MkSimpleBlock
  --label   : BlockLabel kind
  start   : List (LLInstr $ Start inputs)
  proper  : List (LLInstr $ Proper {kind})
  finish  : LLInstr (Finish {kind} output)
