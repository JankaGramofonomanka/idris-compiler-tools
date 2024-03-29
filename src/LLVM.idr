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
    (or if 2 structs have the same structure, then they will be
    indistinghushible)

    Solution 1:
      parametrize structs by the name and contents attached to the name or
      parametrize the contents by the name.
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

-- Reg, RegId -----------------------------------------------------------------
public export
data RegId : LLType -> Type where
  MkRegId : String -> RegId t

export
implementation Eq (RegId t) where
  MkRegId s == MkRegId s' = s == s'

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
public export
data ConstId : LLType -> Type where
  MkConstId : String -> ConstId t

public export
implementation Eq (ConstId t) where
  MkConstId s == MkConstId s' = s == s'

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
public export
data LLLiteral : LLType -> Type where
  ILit : {n : Nat} -> Integer -> LLLiteral (I n)
  CharArrLit : {n : Nat} -> Vect n Char -> LLLiteral (Array I8 (S n))

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
public export
data LLValue : LLType -> Type where
  Var : Reg t -> LLValue t
  Lit : LLLiteral t -> LLValue t
  ConstPtr : Const t -> LLValue (Ptr t)
  Null : (t : LLType) -> LLValue (Ptr t)

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

public export
LLFun : LLType -> List LLType -> Type
LLFun t ts = LLValue (Ptr $ FunType t ts)

public export
LLFun' : (LLType, List LLType) -> Type
LLFun' (t, ts) = LLFun t ts



-- BinOperator, CMPKind, Label ------------------------------------------------
public export
data BinOperator : LLType -> LLType -> LLType -> Type where
  ADD   : {n : Nat} -> BinOperator (I n) (I n) (I n)
  SUB   : {n : Nat} -> BinOperator (I n) (I n) (I n)
  MUL   : {n : Nat} -> BinOperator (I n) (I n) (I n)
  SDIV  : {n : Nat} -> BinOperator (I n) (I n) (I n)
  UDIV  : {n : Nat} -> BinOperator (I n) (I n) (I n)
  SREM  : {n : Nat} -> BinOperator (I n) (I n) (I n)
  UREM  : {n : Nat} -> BinOperator (I n) (I n) (I n)

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
public export
data CMPKind = EQ | NE | SGT | SGE | SLT | SLE | UGT | UGE | ULT | ULE

public export
data Label = MkLabel String

export
implementation Eq Label where
  MkLabel s == MkLabel s' = s == s'


-- Expr -----------------------------------------------------------------------
public export
data LLExpr : LLType -> Type where
  BinOperation : BinOperator tl tr t -> LLValue tl -> LLValue tr -> LLExpr t
  Call : LLValue (Ptr (FunType t ts)) -> DList LLValue ts -> LLExpr t

  -- this does not express the full functionality of the `getelementptr` instruction
  GetElementPtr : {t : LLType}
               -> {k : Nat}
               -> LLValue (Ptr (Array t k))
               -> (idx1 : LLValue (I n))
               -> (idx2 : LLValue (I n))
               -> LLExpr (Ptr t)

  -- TODO what about pointers
  -- TODO fcmp, dcmp? what else?
  ICMP : CMPKind -> LLValue (I n) -> LLValue (I n) -> LLExpr (I 1)

  Load : LLValue (Ptr t) -> LLExpr t

  BitCast : LLValue t1 -> (t2 : LLType) -> LLExpr t2

export
unPtr : The (LLVM.Ptr t) -> The t
unPtr (MkThe (Ptr t)) = MkThe t

export
unFun : The (FunType t ts) -> The t
unFun (MkThe (FunType t ts)) = MkThe t

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

public export
data PhiExpr : List Label -> LLType -> Type where
  -- TODO: the `t` is here in case the list is empty but I think an empty list is invalid
  Phi : (t : LLType) -> (l : List (Label, LLValue t)) -> PhiExpr (map (\t => fst t) l) t

export
implementation Typed (PhiExpr inputs) where
  typeOf (Phi t l) = MkThe t

-- Isntr ----------------------------------------------------------------------
public export
data STInstr : Type where
  Assign : Reg t -> LLExpr t -> STInstr
  Exec : LLExpr Void -> STInstr
  Store : LLValue t -> LLValue (Ptr t) -> STInstr
  Empty : STInstr

public export
data CFInstr : (returnType : LLType) -> (outs : List Label) -> Type where
  
  Branch : (l : Label) -> CFInstr rt [l]
  CondBranch : LLValue I1 -> (l1 : Label) -> (l2 : Label) -> CFInstr rt [l1, l2]

  Ret : LLValue t -> CFInstr t []
  RetVoid : CFInstr Void []

public export
data PhiInstr : List Label -> Type where
  AssignPhi : Reg t -> PhiExpr inputs t -> PhiInstr inputs


-- BasicBlock -----------------------------------------------------------------
public export
record BasicBlock
  (retT     : LLType)
  (label    : Label)
  (inputs   : List Label)
  (outputs  : List Label)
  where
  constructor MkBasicBlock
  theLabel  : The label
  phis      : List (PhiInstr inputs, Maybe String)
  body      : List (STInstr, Maybe String)
  term      : CFInstr retT outputs



public export
BlockVertex : (returnType : LLType) -> Vertex Label
BlockVertex rt lbl Nothing _ = Void
BlockVertex rt lbl _ Nothing = Void
BlockVertex rt lbl (Just ins) (Just outs) = BasicBlock rt lbl ins outs

-- FunDef ---------------------------------------------------------------------
public export
record FunDef where

  constructor MkFunDef
  retT : LLType
  name : Const (FunType retT paramTs)
  params : DList Reg paramTs

  -- TODO: enforce the existence of an entry block
  body : CFG (BlockVertex retT) (Defined []) (Defined [])

-- FunDecl --------------------------------------------------------------------
public export
record FunDecl where
  constructor MkFunDecl
  retT : LLType
  paramTs : List LLType
  name : Const (FunType retT paramTs)

-- ConstDef -------------------------------------------------------------------
public export
data ConstDef : Type where
  DefineConst : (t : LLType) -> Const t -> LLValue t -> ConstDef


-- Program --------------------------------------------------------------------
public export
record Program where
  constructor MkProgram
  funDecls : List FunDecl
  constDefs : List ConstDef
  funcs : List FunDef

