module LLVM.Generalized

import Data.List
import Data.Vect

import Data.DList
import Data.Some
import Data.The
import Data.Typed
import Utils
import CFG

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
data LLValue : (LLType -> Type) -> LLType -> Type where
  Var : var t -> LLValue var t
  Lit : LLLiteral t -> LLValue var t
  ConstPtr : Const t -> LLValue var (Ptr t)
  Null : (t : LLType) -> LLValue var (Ptr t)

public export
ILitV : {n : Nat} -> Integer -> LLValue var (I n)
ILitV i = Lit (ILit i)

export
implementation Eq (var t) => Eq (LLValue var t) where
  Var reg       == Var reg'       = reg   == reg'
  Lit i         == Lit i'         = i     == i'
  ConstPtr cnst == ConstPtr cnst' = cnst  == cnst'
  Null _        == Null _         = True
  _             == _              = False

export
implementation Typed var => Typed (LLValue var) where
  typeOf (Var reg) = typeOf reg
  typeOf (Lit lit) = typeOf lit
  typeOf (ConstPtr cst) = The.map Ptr (typeOf cst)
  typeOf (Null t) = MkThe (Ptr t)

public export
LLFun : (LLType -> Type) -> LLType -> List LLType -> Type
LLFun var t ts = LLValue var (Ptr $ FunType t ts)

public export
LLFun' : (LLType -> Type) -> (LLType, List LLType) -> Type
LLFun' var (t, ts) = LLFun var t ts



-- BinOperator, CMPKind, BlockLabel, Inputs -----------------------------------
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
data BlockLabel = MkBlockLabel String

export
implementation Eq BlockLabel where
  MkBlockLabel s == MkBlockLabel s' = s == s'

public export
data CFKind = Return | Jump (List BlockLabel)


-- TODO: shouldn' this be just an alias for `List BlockLabel`?
public export
data Inputs = MkInputs (List BlockLabel)

public export
(++) : Inputs -> Inputs -> Inputs
MkInputs labels ++ MkInputs labels' = MkInputs (labels ++ labels')

-- Expr -----------------------------------------------------------------------
public export
data LLExpr : (LLType -> Type) -> LLType -> Type where
  BinOperation : BinOperator tl tr t -> LLValue var tl -> LLValue var tr -> LLExpr var t
  Call : LLValue var (Ptr (FunType t ts)) -> DList (LLValue var) ts -> LLExpr var t

  -- this does not express the ful functionality of the `getelementptr` instruction
  GetElementPtr : {t : LLType}
               -> {k : Nat}
               -> LLValue var (Ptr (Array t k))
               -> (idx1 : LLValue var (I n))
               -> (idx2 : LLValue var (I n))
               -> LLExpr var (Ptr t)

  -- TODO what about pointers
  -- TODO fcmp, dcmp? what else?
  ICMP : CMPKind -> LLValue var (I n) -> LLValue var (I n) -> LLExpr var (I 1)

  Load : LLValue var (Ptr t) -> LLExpr var t

  BitCast : LLValue var t1 -> (t2 : LLType) -> LLExpr var t2

export
unPtr : The (LLVM.Generalized.Ptr t) -> The t
unPtr (MkThe (Ptr t)) = MkThe t

export
unFun : The (FunType t ts) -> The t
unFun (MkThe (FunType t ts)) = MkThe t

export
retTypeOf : Typed var => LLValue var (Ptr (FunType t ts)) -> The t
retTypeOf = unFun . unPtr . typeOf

export
implementation Typed var => Typed (LLExpr var) where
  typeOf (BinOperation op lhs rhs) = resType op
  typeOf (Call fun args) = retTypeOf fun
  typeOf (GetElementPtr {t} arr idx1 idx2) = MkThe (Ptr t)
  typeOf (ICMP cmp lhs rhs) = MkThe I1
  typeOf (Load ptr) = unPtr (typeOf ptr)
  typeOf (BitCast val t) = MkThe t

public export
data PhiExpr : (LLType -> Type) -> Inputs -> LLType -> Type where
  -- TODO: the `t` is here in case the list is empty but I think an empty list is invalid
  Phi : (t : LLType) -> (l : List (BlockLabel, LLValue var t)) -> PhiExpr var (MkInputs $ map (\t => fst t) l) t

export
implementation Typed var => Typed (PhiExpr var inputs) where
  typeOf (Phi t l) = MkThe t

-- Isntr ----------------------------------------------------------------------
public export
data STInstr : (LLType -> Type) -> Type where
  Assign : var t -> LLExpr var t -> STInstr var
  Exec : LLExpr var Void -> STInstr var
  Store : LLValue var t -> LLValue var (Ptr t) -> STInstr var
  Empty : STInstr var

public export
data CFInstr : (LLType -> Type) -> (returnType : LLType) -> (kind : CFKind) -> Type where
  
  Branch : (l : BlockLabel) -> CFInstr var rt (Jump [l])
  CondBranch : LLValue var I1 -> (l1 : BlockLabel) -> (l2 : BlockLabel) -> CFInstr var rt (Jump [l1, l2])

  Ret : LLValue var t -> CFInstr var t Return
  RetVoid : CFInstr var Void Return

public export
data PhiInstr : (LLType -> Type) -> Inputs -> Type where
  AssignPhi : var t -> PhiExpr var inputs t -> PhiInstr var inputs


-- SimpleBlock ----------------------------------------------------------------
public export
record SimpleBlock
  (var : LLType -> Type)
  (retT : LLType)
  (label : BlockLabel)
  (inputs : Inputs)
  (cfkind : CFKind)
where
  constructor MkSimpleBlock
  theLabel  : The label
  phis      : List (PhiInstr var inputs, Maybe String)
  body      : List (STInstr var, Maybe String)
  term      : CFInstr var retT cfkind



public export
BlockVertex : (var : LLType -> Type) -> (returnType : LLType) -> Vertex BlockLabel
BlockVertex var rt lbl Nothing _ = Void
BlockVertex var rt lbl _ Nothing = Void
BlockVertex var rt lbl (Just ins) (Just []) = SimpleBlock var rt lbl (MkInputs ins) Return
BlockVertex var rt lbl (Just ins) (Just (out :: outs))
  = SimpleBlock var rt lbl (MkInputs ins) (Jump $ out :: outs)

-- FunDef ---------------------------------------------------------------------
public export
record FunDef (var : LLType -> Type) (retT : LLType) (paramTs : List LLType) where

  constructor MkFunDef
  name : Const (FunType retT paramTs)
  
  theRetType : The retT
  params : DList var paramTs

  -- TODO: enforce the existence of an entry block
  -- TODO: enforce correct return types
  body : CFG (BlockVertex var retT) (Defined []) (Defined [])

-- FunDecl --------------------------------------------------------------------
public export
record FunDecl (retT : LLType) (paramTs : List LLType) where
  constructor MkFunDecl
  name : Const (FunType retT paramTs)
  
  theRetType : The retT
  theParamTypes : The paramTs

-- ConstDef -------------------------------------------------------------------
public export
data ConstDef : (LLType -> Type) -> Type where
  DefineConst : (t : LLType) -> Const t -> LLValue var t -> ConstDef var


-- Program --------------------------------------------------------------------
public export
record Program (var : LLType -> Type) where
  constructor MkProgram
  funDecls : List (retType ** paramTypes ** FunDecl retType paramTypes)
  constDefs : List (ConstDef var)
  funcs : List (retType ** paramTypes ** FunDef var retType paramTypes)

