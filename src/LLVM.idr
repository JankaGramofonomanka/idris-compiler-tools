module LLVM

import Data.List
import Data.Vect
import Derive.Prelude

import Data.DList
import Data.Singleton
import Data.Singleton.Extra
import Data.Some
import Data.Typed
import Utils
import CFG

%language ElabReflection

-- The following implementations are needed to derive `Eq` and `Ord` instances
-- for `LLVM` elements defined in this module
implementation Eq (Singleton x) where
  _ == _ = True

implementation Ord (Singleton x) where
  compare _ _ = EQ


{-
TODO: define a "pseudo LLVM" type that would generalize over `LLValue`, that is
an LLVM parametrized by the type of values that can be put in expressions.
This will allow to add placeholders to expressions.
-}

||| The types of variables in LLVM
public export
data LLType

  = ||| `I n` is the `n`-bit integer, `i<n>` in LLVM
    I Nat

  -- TODO: floats?, what else?
  -- | F ?

  | ||| The `void` type
    Void

  | ||| `Ptr t` is a pointer to `t`, `<t>*` in LLVM
    Ptr LLType

  | ||| `Array t n` an `n`-element array of elements of type `t`
    Array LLType Nat

  {-
    TODO: how to parametrize structs?
    with struct name and then get the contents of the struct from a context
    or have the contents in the parameter?
    The latter aproach allows multiple structs with the same name
    (or if 2 structs have the same structure, then they will be
    indistinghushible)

    Solution 1:
      parametrize structs by the name and contents attached to the name or
      parametrize the contents by the name.
  -}
  -- | Struct ?

  -- TODO: wasn't VTable a type of struct?
  -- | VTable ?

  | ||| `FunType t ts` is the type of functions with the return type `t` and
    ||| parameters of types `ts`
    FunType LLType (List LLType)

||| `i1`, alias for `I 1`
public export
I1    : LLType
I1    = I 1

||| `i8`, alias for `I 8`
public export
I8    : LLType
I8    = I 8

||| `i16`, alias for `I 16`
public export
I16   : LLType
I16   = I 16

||| `i32`, alias for `I 32`
public export
I32   : LLType
I32   = I 32

||| `i64`, alias for `I 64`
public export
I64   : LLType
I64   = I 64

||| `i128`, alias for `I 128`
public export
I128  : LLType
I128  = I 128

||| `i256`, alias for `I 256`
public export
I256  : LLType
I256  = I 256

-- Reg, RegId -----------------------------------------------------------------
||| A register identifier
||| @ t the type of the value stored in the register
public export
data RegId : (t : LLType) -> Type where
  ||| Make a register identifier
  ||| @ name the name of the register
  MkRegId : (name : String) -> RegId t

%runElab derive "RegId" [Eq]

||| A register identifier with a runtime representation of its type
||| @ t the type of the value stored in the register
public export
data Reg : (t : LLType) -> Type where
  ||| Make a `Reg` out of `RegId`
  |||
  ||| Note: `t` is wrapped in `Singleton` in order to appease the deriving
  ||| mechanism
  |||
  ||| @ t     the type of the register
  ||| @ regId the register identifier
  MkReg : Singleton t -> (regId : RegId t) -> Reg t

%runElab deriveIndexed "Reg" [Eq]

export
implementation Typed Reg where
  typeOf (MkReg t id) = t

-- Const, ConstId -------------------------------------------------------------
||| A constant identifier
||| @ t the type of the constant
public export
data ConstId : (t : LLType) -> Type where
  ||| Make a constant identifier
  ||| @ name the name of the constant
  MkConstId : (name : String) -> ConstId t

%runElab derive "ConstId" [Eq]

||| A constant identifier with a runtime representation of its type
||| @ t the type of the constant
public export
data Const : LLType -> Type where
  ||| Make a `Const` out of `ConstId`
  |||
  ||| Note: `t` is wrapped in `Singleton` in order to appease the deriving
  ||| mechanism
  |||
  ||| @ t       the type of the constant
  ||| @ constId the constant identifier
  MkConst : Singleton t -> (constId : ConstId t) -> Const t

%runElab deriveIndexed "Const" [Eq]

export
implementation Typed Const where
  typeOf (MkConst t id) = t

-- LLLiteral ------------------------------------------------------------------
||| An LLVM Literal
public export
data LLLiteral : LLType -> Type where
  ||| An integer literal
  ||| @ n   the number of bits in the type of the literal
  ||| @ lit the value of the literal
  ILit : {n : Nat} -> (lit : Integer) -> LLLiteral (I n)
  CharArrLit : {n : Nat} -> Vect n Char -> LLLiteral (Array I8 (S n))

-- TODO move this to some utils module
||| Convert a string to a vector of chars
export
stringToCharVect : String -> (n ** Vect n Char)
stringToCharVect s = go (unpack s) where
  go : List Char -> (n ** Vect n Char)
  go Nil = (Z ** Nil)
  go (ch :: chs) = let (n ** chars) = go chs in (S n ** ch :: chars)

%runElab deriveIndexed "LLLiteral" [Eq]

export
implementation Typed LLLiteral where
  typeOf (ILit {n} _) = Val (I n)
  typeOf (CharArrLit {n} chars) = Val (Array I8 (S n))

-- LLValue --------------------------------------------------------------------
||| An LLVM value
||| @ t the type of the value
public export
data LLValue : (t : LLType) -> Type where
  ||| A register
  ||| @ reg the register identifier
  Var : (reg : Reg t) -> LLValue t
  ||| A Literal
  ||| @ lit the literal
  Lit : (lit : LLLiteral t) -> LLValue t
  ||| A constant pointer
  ||| @ cst the constant
  ConstPtr : (cst : Const t) -> LLValue (Ptr t)
  ||| A null pointer.
  |||
  ||| Note: `t` is wrapped in `Singleton` in order to appease the deriving
  ||| mechanism
  |||
  ||| @ t the type of the pointer
  Null : Singleton t -> LLValue (Ptr t)

||| An alias for an integer literal value
||| @ n   the number of bits in the type of the literal
||| @ lit the value of the literal
public export
ILitV : {n : Nat} -> (lit : Integer) -> LLValue (I n)
ILitV i = Lit (ILit i)

%runElab deriveIndexed "LLValue" [Eq]

export
implementation Typed LLValue where
  typeOf (Var reg) = typeOf reg
  typeOf (Lit lit) = typeOf lit
  typeOf (ConstPtr cst) = Ptr <$> (typeOf cst)
  typeOf (Null t) = Ptr <$> t

||| An alias for a function pointer type
||| @ t  the return type of the function
||| @ ts the types of the function parameters
public export
LLFun : (t : LLType) -> (ts : List LLType) -> Type
LLFun t ts = LLValue (Ptr $ FunType t ts)

||| An alias for a function pointer type, parametrized by a tuple instead of
||| two parameters
||| @ tup the return type and parameter types of the function
public export
LLFun' : (tup : (LLType, List LLType)) -> Type
LLFun' (t, ts) = LLFun t ts



-- BinOperator, CMPKind, Label ------------------------------------------------
||| A binary operator
||| @ lhsT the type of the left operand
||| @ rhsT the type of the right operand
||| @ resT the type of the result
public export
data BinOperator : (lhsT : LLType) -> (rhsT : LLType) -> (resT : LLType) -> Type where
  ||| `add` - addition operator
  ||| @ n the number of bits in the type of operands and the return type
  ADD   : {n : Nat} -> BinOperator (I n) (I n) (I n)
  ||| `sub` - subtraction operator
  ||| @ n the number of bits in the type of operands and the return type
  SUB   : {n : Nat} -> BinOperator (I n) (I n) (I n)
  ||| `mul` - multiplication operator
  ||| @ n the number of bits in the type of operands and the return type
  MUL   : {n : Nat} -> BinOperator (I n) (I n) (I n)
  ||| `sdiv` - signed division operator
  ||| @ n the number of bits in the type of operands and the return type
  SDIV  : {n : Nat} -> BinOperator (I n) (I n) (I n)
  ||| `udiv` - unsigned division operator
  ||| @ n the number of bits in the type of operands and the return type
  UDIV  : {n : Nat} -> BinOperator (I n) (I n) (I n)
  ||| `srem` - signed remainer operator
  ||| @ n the number of bits in the type of operands and the return type
  SREM  : {n : Nat} -> BinOperator (I n) (I n) (I n)
  ||| `urem` - unsigned remainer operator
  ||| @ n the number of bits in the type of operands and the return type
  UREM  : {n : Nat} -> BinOperator (I n) (I n) (I n)

||| The return type of a binary operator
export
resType : BinOperator t1 t2 t3 -> Singleton t3
resType (ADD  {n}) = Val (I n)
resType (SUB  {n}) = Val (I n)
resType (MUL  {n}) = Val (I n)
resType (SDIV {n}) = Val (I n)
resType (UDIV {n}) = Val (I n)
resType (SREM {n}) = Val (I n)
resType (UREM {n}) = Val (I n)

-- TODO: parametrise this?
-- what types can be compared?
||| kind of integer comparison
public export
data CMPKind
  = ||| `eq` - Equality
    EQ
  | ||| `ne` - Inequality
    NE
  | ||| `sgt` - signed greater than
    SGT
  | ||| `sge` - signed greater or equal
    SGE
  | ||| `slt` - signed lesser than
    SLT
  | ||| `sle` - signed lesser or equal
    SLE
  | ||| `ugt` - unsigned greater than
    UGT
  | ||| `uge` - unsigned greater or equal
    UGE
  | ||| `ult` - unsigned lesser than
    ULT
  | ||| `ule` - unsigned lesser or equal
    ULE

||| A label of a basic block
public export
data Label = MkLabel String

%runElab derive "Label" [Eq]

-- Expr -----------------------------------------------------------------------
||| An LLVM expression
||| @ t the type of the expression
public export
data LLExpr : (t : LLType) -> Type where

  ||| A binary operation
  ||| @ op  the operation (`add`, `sub`, `mul` etc.)
  ||| @ lhs the left operand
  ||| @ the right operand
  BinOperation : (op : BinOperator tl tr t) -> (lhs : LLValue tl) -> (rhs : LLValue tr) -> LLExpr t

  ||| `call` - A function call
  ||| @ funPtr the function pointer
  ||| @ args   the arguments passed to the function
  Call : (funPtr : LLValue (Ptr $ FunType t ts)) -> (args : DList LLValue ts) -> LLExpr t

  -- TODO provide informative documentation of `idx0` and `idx1` parameters
  ||| `getelementptr` applied to arrays
  |||
  ||| `GetElementPtr` does not express the full functionality of the
  ||| `getelementptr` instruction
  ||| More info: https://llvm.org/docs/GetElementPtr.html
  ||| @ t the  type of array elements
  ||| @ k the  number of elements in the array
  ||| @ arrPtr the array pointer
  ||| @ idx1   index 0
  ||| @ idx2   index 1
  GetElementPtr : {t : LLType}
               -> {k : Nat}
               -> (arrPtr : LLValue (Ptr (Array t k)))
               -> (idx1 : LLValue (I n))
               -> (idx2 : LLValue (I n))
               -> LLExpr (Ptr t)

  -- TODO what about pointers
  -- TODO fcmp, dcmp? what else?
  ||| `icmp` - Comparison of integers
  ||| @ cmpKind the kind of comparison (`eq`, , `sgt`, etc.)
  ||| @ lhs     the left operand
  ||| @ rhs     the right operand
  ICMP : (cmpKind : CMPKind) -> (lhs: LLValue (I n)) -> (rhs : LLValue (I n)) -> LLExpr (I 1)

  ||| `load` - Dereferencing of a pointer
  ||| @ ptr the pointer to be dereferenced
  Load : (ptr : LLValue (Ptr t)) -> LLExpr t

  ||| `bitcast` - casting a value of one type to another
  ||| @ val the cast value
  ||| @ t2  the type to which the value is cast
  BitCast : (val : LLValue t1) -> (t2 : LLType) -> LLExpr t2

||| Returns the type of the value stored behind the pointer
export
unPtr : Singleton (LLVM.Ptr t) -> Singleton t
unPtr (Val (Ptr t)) = Val t

||| Returns the return type of the function
export
unFun : Singleton (FunType t ts) -> Singleton t
unFun (Val (FunType t ts)) = Val t

||| Returns the return type of the function
export
retTypeOf : LLValue (Ptr (FunType t ts)) -> Singleton t
retTypeOf = unFun . unPtr . typeOf

export
implementation Typed LLExpr where
  typeOf (BinOperation op lhs rhs)         = resType op
  typeOf (Call fun args)                   = retTypeOf fun
  typeOf (GetElementPtr {t} arr idx1 idx2) = Val (Ptr t)
  typeOf (ICMP cmp lhs rhs)                = Val I1
  typeOf (Load ptr)                        = unPtr (typeOf ptr)
  typeOf (BitCast val t)                   = Val t

||| A "phi" expresion, the right side of a "phi" assignment
||| @ ins the list of labels of blocks, from which the control flow jumps to
|||       the phi assignment, this expression is part of
||| @ t   the type of the expression
public export
data PhiExpr : (ins : List Label) -> (t : LLType) -> Type where
  -- TODO: the `t` is here in case the list is empty but I think an empty list is invalid
  ||| Make a phi assignemt
  ||| @ t the type of the expression
  ||| @ l the list of label-value pairs, each block label is paired with a
  |||   value that will be asuumend by the phi expression when the control
  |||   jumps from that block
  Phi : (t : LLType) -> (l : List (Label, LLValue t)) -> PhiExpr (map (\t => fst t) l) t

export
implementation Typed (PhiExpr inputs) where
  typeOf (Phi t l) = Val t

-- Isntr ----------------------------------------------------------------------
||| An simple LLVM instruction
public export
data STInstr : Type where

  ||| An assignment instruction
  ||| @ reg  the register to which a value is assigned
  ||| @ expr the expression from which thre assigned value is computed
  Assign : (reg : Reg t) -> (expr : LLExpr t) -> STInstr

  ||| A computation of an void expression
  ||| @ expr the expression to be computed
  Exec : (expr : LLExpr Void) -> STInstr

  ||| The `store` instruction, stores a value under a pointer
  ||| @ val the stored value
  ||| @ ptr the pointer under which the value is stored
  Store : (val : LLValue t) -> (ptr : LLValue (Ptr t)) -> STInstr

  ||| An empty line
  Empty : STInstr

||| A control-flow instruction - a jump or a return
||| @ returnType the return type of the function the instruction is part of,
|||              used to enforce the correct type of returned values
||| @ outs       the output labels of the block the instruction is part of
public export
data CFInstr : (returnType : LLType) -> (outs : List Label) -> Type where

  ||| An unconditional branch instruction
  ||| @ l the label of the block to jump to
  Branch : (l : Label) -> CFInstr rt [l]

  ||| A conditional branch
  ||| @ cond the condition which determines which block to jump to
  ||| @ l1 the block to jump to, when the condition is true
  ||| @ l2 the block to jump to, when the condition is false
  CondBranch : (cond : LLValue I1) -> (l1 : Label) -> (l2 : Label) -> CFInstr rt [l1, l2]

  ||| A return of a value
  ||| @ val the returned value
  Ret : (val : LLValue t) -> CFInstr t []

  ||| A void return
  RetVoid : CFInstr Void []

||| A "phi" assignemnt
||| @ ins the list of labels of blocks, from which the control flow jumps to
|||       the phi assignment
public export
data PhiInstr : (ins : List Label) -> Type where
  ||| Make a phi assignment
  ||| @ reg the  registor, to which a value is assigned
  ||| @ expr the expression whose value is assignemd to the register
  AssignPhi : (reg : Reg t) -> (expr : PhiExpr inputs t) -> PhiInstr inputs


-- BasicBlock -----------------------------------------------------------------
||| A basic block
||| @ retT    the return type of the function, whose body the block is a part of
||| @ label   the label of the block
||| @ inputs  the input labels of the block
||| @ outputs the output labels of the block
public export
record BasicBlock
  (retT     : LLType)
  (label    : Label)
  (inputs   : List Label)
  (outputs  : List Label)
  where
  constructor MkBasicBlock

  ||| the label of the block
  theLabel : Singleton label

  ||| "phi" assignments preceding the body of the block
  phis : List (PhiInstr inputs, Maybe String)

  ||| The body of the block
  body : List (STInstr, Maybe String)

  ||| The terminator of the block
  term : CFInstr retT outputs



||| A wrapper around `BasicBlock` that fits it in the `Vertex` type
||| @ returnType the return type of the function, whose body the block is a
|||              part of
public export
BlockVertex : (returnType : LLType) -> Vertex Label
BlockVertex rt lbl Nothing _ = Void
BlockVertex rt lbl _ Nothing = Void
BlockVertex rt lbl (Just ins) (Just outs) = BasicBlock rt lbl ins outs

-- FunDef ---------------------------------------------------------------------
||| A function definition
public export
record FunDef where
  constructor MkFunDef

  ||| The return type of the function
  retT : LLType

  ||| The identifier of the function
  name : Const (FunType retT paramTs)

  ||| The parameters of the function
  params : DList Reg paramTs

  -- TODO: enforce the existence of an entry block
  ||| The body of the function
  body : CFG (BlockVertex retT) (Defined []) (Defined [])

-- FunDecl --------------------------------------------------------------------
||| A function declaraition, used to import functions
public export
record FunDecl where
  constructor MkFunDecl
  ||| The return type of the function
  retT : LLType

  ||| The parameter types of the function
  paramTs : List LLType

  ||| The identifier of the function
  name : Const (FunType retT paramTs)

-- ConstDef -------------------------------------------------------------------
||| A constant definition
public export
data ConstDef : Type where
  ||| Make a constant definition
  ||| @ t   the type of the constant
  ||| @ cst the constant identifier
  ||| @ the value of the constant
  DefineConst : (t : LLType) -> (cst : Const t) -> (val : LLValue t) -> ConstDef

-- Program --------------------------------------------------------------------
||| An LLVM program
public export
record Program where
  constructor MkProgram

  ||| function declarations
  funDecls : List FunDecl

  ||| constant definitions
  constDefs : List ConstDef

  ||| function definitions
  funcs : List FunDef
