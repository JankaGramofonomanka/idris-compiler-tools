module LLVM

import Data.List

import Data.DList
import Data.DMap
import Data.Some
import Utils
import CFG

import FEq

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
data InputKind = Entry | NonEntry

public export
data BlockLabel : InputKind -> Type where
  LEntry : BlockLabel Entry
  LName : String -> BlockLabel NonEntry

export
implementation FEq BlockLabel where
  LEntry  == LEntry   = True
  LName s == LName s' = s == s'
  LEntry  == LName s  = False
  LName s == LEntry   = False

export
implementation Eq (BlockLabel k) where
  LEntry == LEntry = True
  LName s == LName s' = s == s'

public export
data CFKind = Return | Jump (List $ BlockLabel NonEntry)



public export
data Inputs : InputKind -> Type where
  NoInputs : Inputs Entry
  MkInputs : List (Some BlockLabel) -> Inputs NonEntry

public export
(++) : Inputs k -> Inputs k -> Inputs k
NoInputs ++ NoInputs = NoInputs
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
data PhiExpr : Inputs kind -> LLType -> Type where
  Phi : (l : List (Some BlockLabel, LLValue t)) -> PhiExpr (MkInputs $ map (\t => fst t) l) t



public export
data STInstr : Type where
  Assign : Reg t -> LLExpr t -> STInstr
  Exec : LLExpr Void -> STInstr
  Store : LLValue t -> LLValue (Ptr t) -> STInstr

public export
data CFInstr : CFKind -> Type where
  
  Branch : (l : BlockLabel NonEntry) -> CFInstr (Jump [l])
  CondBranch : LLValue I1 -> (l1 : BlockLabel NonEntry) -> (l2 : BlockLabel NonEntry) -> CFInstr (Jump [l1, l2])

  Ret : LLValue t -> CFInstr Return
  RetVoid : CFInstr Return

public export
data PhiInstr : Inputs kind -> Type where
  AssignPhi : Reg t -> PhiExpr inputs t -> PhiInstr inputs



public export
record SimpleBlock
  (inputKind : InputKind)
  (label : BlockLabel inputKind)
  (inputs : Inputs inputKind)
  (cfkind : CFKind)
where
  constructor MkSimpleBlock
  phis : List (PhiInstr inputs)
  body : List STInstr
  term : CFInstr cfkind



-- Control Flow Graph ---------------------------------------------------------
Edge : Type
Edge = (Some BlockLabel, BlockLabel NonEntry)

JumpGraph : Type
JumpGraph = List Edge

getLabels : JumpGraph -> List (Some BlockLabel)
getLabels graph = let
  (froms, tos) = unzip graph
  in nub $ froms ++ (map MkSome tos)

getInputs : BlockLabel kind -> JumpGraph -> Inputs kind
getInputs LEntry g = NoInputs
getInputs label@(LName s) g = MkInputs (map fst $ filter (\(from, to) => to == label) g)

getCFKind : BlockLabel kind -> JumpGraph -> CFKind
getCFKind l graph = case map snd $ filter (\(from, to) => from == MkSome l) graph of
  Nil     => Return
  labels  => Jump labels


{-
  A control flow graph, parametrized by
  * `jumpGraph` - a graph of jumps between blocks
  * `toBeDefined` - a list of block labels, that are missing from the graph,
    ie. labels that occur in `jumpGraph` but a blocks with such labels are not 
    part of the graph.
  
  The type `CFG g []` is a type of a correct control flow graph.

  Note! the `jumpGraph` parameneter has to be known in advance, before we start
  building the graph, therefore an intermediate representation of the graph, is
  needed (See `LLVM.Construction`).
-}
public export
data CFG : (jumpGraph : JumpGraph) -> (toBeDefined : List (Some BlockLabel)) -> Type where
  Empty : CFG graph (getLabels graph)

  -- TODO: Enforce uniqueness of blocks?
  AddBlock : SimpleBlock inputKind label (getInputs label graph) (getCFKind label graph)
          -> CFG graph toBeDefined
          -> CFG graph (delete (MkSome label) toBeDefined)


public export
record FunDecl (retType : LLType) (paramTypes : List LLType) where
  constructor MkFunDecl
  params : DList Reg paramTypes

  -- TODO: enforce the existence of an entry block
  0 jumpGraph : JumpGraph

  -- TODO: enforce correct return types
  body : CFG jumpGraph Nil

