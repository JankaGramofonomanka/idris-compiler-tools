module LLVM

import Data.List

import Data.DList
import Data.DMap
import Data.Some
import Utils
import CFG

import FEq

{-
TODO: define a "pseudo LLVM" type that would generalize over `LLValue`, that is
an LLVM parametrized by the type of values that can be put in expressions.
This will allow to add placeholders to expressions.
-}

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
    (or if 2 structs have the same structure, then they will be indistinghushible)
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
I256  : LLType
I256  = I 256

public export
data Reg : LLType -> Type where
  MkReg : String -> Reg t

implementation Eq (Reg t) where
  MkReg s == MkReg s' = s == s'

public export
data Const : LLType -> Type where
  MkConst : String -> Const t

implementation Eq (Const t) where
  MkConst s == MkConst s' = s == s'

public export
data LLValue : LLType -> Type where
  Var : Reg t -> LLValue t
  ILit : Integer -> LLValue (I n)
  ConstPtr : Const t -> LLValue (Ptr t)
  Null : LLValue (Ptr t)

export
implementation Eq (LLValue t) where
  Var reg       == Var reg'       = reg   == reg'
  ILit i        == ILit i'        = i     == i'
  ConstPtr cnst == ConstPtr cnst' = cnst  == cnst'
  Null          == Null           = True
  _             == _              = False

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
data BlockLabel = MkBlockLabel String

export
implementation Eq BlockLabel where
  MkBlockLabel s == MkBlockLabel s' = s == s'

public export
data CFKind = Return | Jump (List BlockLabel)



public export
data Inputs = MkInputs (List BlockLabel)

public export
(++) : Inputs -> Inputs -> Inputs
MkInputs labels ++ MkInputs labels' = MkInputs (labels ++ labels')


public export
data LLExpr : LLType -> Type where
  BinOperation : BinOperator tl tr t -> LLValue tl -> LLValue tr -> LLExpr t
  Call : LLValue (Ptr (FunType t ts)) -> DList LLValue ts -> LLExpr t

  -- TODO: getelementptr

  -- TODO what about pointers
  -- TODO fcmp, dcmp? what else?
  ICMP : CMPKind -> LLValue (I n) -> LLValue (I n) -> LLExpr (I 1)

  Load : LLValue (Ptr t) -> LLExpr t

  BitCast : LLValue t1 -> (t2 : LLType) -> LLExpr t2

public export
data PhiExpr : Inputs -> LLType -> Type where
  Phi : (l : List (BlockLabel, LLValue t)) -> PhiExpr (MkInputs $ map (\t => fst t) l) t



public export
data STInstr : Type where
  Assign : Reg t -> LLExpr t -> STInstr
  Exec : LLExpr Void -> STInstr
  Store : LLValue t -> LLValue (Ptr t) -> STInstr

public export
data CFInstr : CFKind -> Type where
  
  Branch : (l : BlockLabel) -> CFInstr (Jump [l])
  CondBranch : LLValue I1 -> (l1 : BlockLabel) -> (l2 : BlockLabel) -> CFInstr (Jump [l1, l2])

  Ret : LLValue t -> CFInstr Return
  RetVoid : CFInstr Return

public export
data PhiInstr : Inputs -> Type where
  AssignPhi : Reg t -> PhiExpr inputs t -> PhiInstr inputs



public export
record SimpleBlock
  (label : BlockLabel)
  (inputs : Inputs)
  (cfkind : CFKind)
where
  constructor MkSimpleBlock
  phis : List (PhiInstr inputs)
  body : List STInstr
  term : CFInstr cfkind



public export
BlockVertex : Vertex BlockLabel
BlockVertex lbl Nothing _ = Void
BlockVertex lbl _ Nothing = Void
BlockVertex lbl (Just ins) (Just []) = SimpleBlock lbl (MkInputs ins) Return
BlockVertex lbl (Just ins) (Just (out :: outs))
  = SimpleBlock lbl (MkInputs ins) (Jump $ out :: outs)


public export
record FunDecl (retType : LLType) (paramTypes : List LLType) where

  constructor MkFunDecl
  params : DList Reg paramTypes

  -- TODO: enforce the existence of an entry block
  -- TODO: enforce correct return types
  body : CFG BlockVertex (Defined []) (Defined [])

public export
record Program where
  constructor MkProgram
  funcs : List (retType ** paramTypes ** FunDecl retType paramTypes)

