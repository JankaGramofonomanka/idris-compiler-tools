module LLVM

import Data.List
import Data.Vect

import Data.DList
import Data.Some
import Data.The
import Data.Typed
import Utils
import CFG

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
public export
data RegId : LLType -> Type where
  MkRegId : String -> RegId t

export
implementation Eq (RegId t) where
  MkRegId s == MkRegId s' = s == s'

||| A register identifier with a runtime representation of its type
public export
data Reg : LLType -> Type where
  MkReg : (t : LLType) -> RegId t -> Reg t

-- TODO: is this needed?
export
implementation Eq (Reg t) where
  MkReg _ id == MkReg _ id' = id == id'

export
implementation Typed Reg where
  typeOf (MkReg t id) = MkThe t

-- Const, ConstId -------------------------------------------------------------
||| A constant identifier
public export
data ConstId : LLType -> Type where
  MkConstId : String -> ConstId t

public export
implementation Eq (ConstId t) where
  MkConstId s == MkConstId s' = s == s'

||| A constant identifier with a runtime representation of its type
public export
data Const : LLType -> Type where
  MkConst : (t : LLType) -> ConstId t -> Const t

-- TODO: is this needed?
export
implementation Eq (Const t) where
  MkConst _ id == MkConst _ id' = id == id'

export
implementation Typed Const where
  typeOf (MkConst t id) = MkThe t

-- LLLiteral ------------------------------------------------------------------
||| An LLVM Literal
public export
data LLLiteral : LLType -> Type where
  ILit : {n : Nat} -> Integer -> LLLiteral (I n)
  CharArrLit : {n : Nat} -> Vect n Char -> LLLiteral (Array I8 (S n))

-- TODO move this to some utils module
||| Convert a string to a vector of chars
export
stringToCharVect : String -> (n ** Vect n Char)
stringToCharVect s = go (unpack s) where
  go : List Char -> (n ** Vect n Char)
  go Nil = (Z ** Nil)
  go (ch :: chs) = let (n ** chars) = go chs in (S n ** ch :: chars)

export
implementation Eq (LLLiteral t) where
  ILit i == ILit i' = i == i'
  CharArrLit s == CharArrLit s' = s == s'

export
implementation Typed LLLiteral where
  typeOf (ILit {n} _) = MkThe (I n)
  typeOf (CharArrLit {n} chars) = MkThe (Array I8 (S n))

-- LLValue --------------------------------------------------------------------
||| An LLVM value
public export
data LLValue : LLType -> Type where
  ||| A variable
  Var : Reg t -> LLValue t
  ||| A Literal
  Lit : LLLiteral t -> LLValue t
  ||| A constant pointer
  ConstPtr : Const t -> LLValue (Ptr t)
  ||| A null pointer
  Null : (t : LLType) -> LLValue (Ptr t)

||| An alias for an integer literal
public export
ILitV : {n : Nat} -> Integer -> LLValue (I n)
ILitV i = Lit (ILit i)

export
implementation Eq (LLValue t) where
  Var reg       == Var reg'       = reg   == reg'
  Lit i         == Lit i'         = i     == i'
  ConstPtr cnst == ConstPtr cnst' = cnst  == cnst'
  Null _        == Null _         = True
  _             == _              = False

export
implementation Typed LLValue where
  typeOf (Var reg) = typeOf reg
  typeOf (Lit lit) = typeOf lit
  typeOf (ConstPtr cst) = The.map Ptr (typeOf cst)
  typeOf (Null t) = MkThe (Ptr t)

||| An alias for a function pointer type
public export
LLFun : LLType -> List LLType -> Type
LLFun t ts = LLValue (Ptr $ FunType t ts)

||| An alias for a function pointer type, parametrized by a tuple instead of
||| two parameters
public export
LLFun' : (LLType, List LLType) -> Type
LLFun' (t, ts) = LLFun t ts



-- BinOperator, CMPKind, Label ------------------------------------------------
||| A binary operator
public export
data BinOperator : LLType -> LLType -> LLType -> Type where
  ||| `add` - addition operator
  ADD   : {n : Nat} -> BinOperator (I n) (I n) (I n)
  ||| `sub` - subtraction operator
  SUB   : {n : Nat} -> BinOperator (I n) (I n) (I n)
  ||| `mul` - multiplication operator
  MUL   : {n : Nat} -> BinOperator (I n) (I n) (I n)
  ||| `sdiv` - signed division operator
  SDIV  : {n : Nat} -> BinOperator (I n) (I n) (I n)
  ||| `udiv` - unsigned division operator
  UDIV  : {n : Nat} -> BinOperator (I n) (I n) (I n)
  ||| `srem` - signed remainer operator
  SREM  : {n : Nat} -> BinOperator (I n) (I n) (I n)
  ||| `urem` - unsigned remainer operator
  UREM  : {n : Nat} -> BinOperator (I n) (I n) (I n)

||| The return type of a binary operator
export
resType : BinOperator t1 t2 t3 -> The t3
resType (ADD  {n}) = MkThe (I n)
resType (SUB  {n}) = MkThe (I n)
resType (MUL  {n}) = MkThe (I n)
resType (SDIV {n}) = MkThe (I n)
resType (UDIV {n}) = MkThe (I n)
resType (SREM {n}) = MkThe (I n)
resType (UREM {n}) = MkThe (I n)

-- TODO: parametrise this?
-- what types can be compared?
||| kind of integer comparison
public export
data CMPKind
  = ||| Equality
    EQ
  | ||| Inequality
    NE
  | ||| signed greater than
    SGT
  | ||| signed greater or equal
    SGE
  | ||| signed lesser than
    SLT
  | ||| signed lesser or equal
    SLE
  | ||| unsigned greater than
    UGT
  | ||| unsigned greater or equal
    UGE
  | ||| unsigned lesser than
    ULT
  | ||| unsigned lesser or equal
    ULE

||| A label of a basic block
public export
data Label = MkLabel String

export
implementation Eq Label where
  MkLabel s == MkLabel s' = s == s'


-- Expr -----------------------------------------------------------------------
||| An LLVM expression
public export
data LLExpr : LLType -> Type where

  ||| A binary operation, such as `add`, `sub`, `mul` etc.
  BinOperation : BinOperator tl tr t -> LLValue tl -> LLValue tr -> LLExpr t

  ||| `call` - A function call
  Call : LLValue (Ptr (FunType t ts)) -> DList LLValue ts -> LLExpr t

  -- this does not express the full functionality of the `getelementptr` instruction
  ||| `getelementptr` applied to arrays
  GetElementPtr : {t : LLType}
               -> {k : Nat}
               -> LLValue (Ptr (Array t k))
               -> (idx1 : LLValue (I n))
               -> (idx2 : LLValue (I n))
               -> LLExpr (Ptr t)

  -- TODO what about pointers
  -- TODO fcmp, dcmp? what else?
  ||| `icmp` - Comparison of integers
  ICMP : CMPKind -> LLValue (I n) -> LLValue (I n) -> LLExpr (I 1)

  ||| `load` - Dereferencing of a pointer
  Load : LLValue (Ptr t) -> LLExpr t

  ||| `bitcast` - casting a value of one type to another
  BitCast : LLValue t1 -> (t2 : LLType) -> LLExpr t2

||| Returns the type of the value stored behind the pointer
export
unPtr : The (LLVM.Ptr t) -> The t
unPtr (MkThe (Ptr t)) = MkThe t

||| Returns the return type of the function
export
unFun : The (FunType t ts) -> The t
unFun (MkThe (FunType t ts)) = MkThe t

||| Returns the return type of the function
export
retTypeOf : LLValue (Ptr (FunType t ts)) -> The t
retTypeOf = unFun . unPtr . typeOf

export
implementation Typed LLExpr where
  typeOf (BinOperation op lhs rhs) = resType op
  typeOf (Call fun args) = retTypeOf fun
  typeOf (GetElementPtr {t} arr idx1 idx2) = MkThe (Ptr t)
  typeOf (ICMP cmp lhs rhs) = MkThe I1
  typeOf (Load ptr) = unPtr (typeOf ptr)
  typeOf (BitCast val t) = MkThe t

||| A "phi" expresion, the right side of a "phi" assignment
public export
data PhiExpr : List Label -> LLType -> Type where
  -- TODO: the `t` is here in case the list is empty but I think an empty list is invalid
  Phi : (t : LLType) -> (l : List (Label, LLValue t)) -> PhiExpr (map (\t => fst t) l) t

export
implementation Typed (PhiExpr inputs) where
  typeOf (Phi t l) = MkThe t

-- Isntr ----------------------------------------------------------------------
||| An simple LLVM instruction
public export
data STInstr : Type where
  Assign : Reg t -> LLExpr t -> STInstr
  Exec : LLExpr Void -> STInstr
  Store : LLValue t -> LLValue (Ptr t) -> STInstr
  Empty : STInstr

||| A control-flow instruction - a jump or a return
public export
data CFInstr : (returnType : LLType) -> (outs : List Label) -> Type where

  Branch : (l : Label) -> CFInstr rt [l]
  CondBranch : LLValue I1 -> (l1 : Label) -> (l2 : Label) -> CFInstr rt [l1, l2]

  Ret : LLValue t -> CFInstr t []
  RetVoid : CFInstr Void []

||| A "phi" assignemnt
public export
data PhiInstr : List Label -> Type where
  AssignPhi : Reg t -> PhiExpr inputs t -> PhiInstr inputs


-- BasicBlock -----------------------------------------------------------------
||| A basic block
public export
record BasicBlock
  (retT     : LLType)
  (label    : Label)
  (inputs   : List Label)
  (outputs  : List Label)
  where
  constructor MkBasicBlock

  ||| the label of the block
  theLabel : The label

  ||| "phi" assignments preceding the body of the block
  phis : List (PhiInstr inputs, Maybe String)

  ||| The body of the block
  body : List (STInstr, Maybe String)

  ||| The terminator of the block
  term : CFInstr retT outputs



||| A wrapper around `BasicBlock` that fits it in the `Vertex` type
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
  DefineConst : (t : LLType) -> Const t -> LLValue t -> ConstDef

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
