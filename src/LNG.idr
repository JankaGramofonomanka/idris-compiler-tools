{-
  A simple programming language, for testing the usefulness and demonstration
  of compiler frameworks defined in this project.
-}
module LNG

import Data.DList

public export
data LNGType = TInt | TBool | TVoid

public export
data EqComparable : LNGType -> Type where
  EqCMPInt : EqComparable TInt
  EqCMPBool : EqComparable TBool

public export
data BinOperator : LNGType -> LNGType -> Type where
  Add : BinOperator TInt TInt
  Sub : BinOperator TInt TInt
  Mul : BinOperator TInt TInt
  Div : BinOperator TInt TInt
  And : BinOperator TBool TBool
  Or  : BinOperator TBool TBool
  
  EQ  : {auto 0 prf : EqComparable t} -> BinOperator t TBool
  LE  : BinOperator TInt TBool
  LT  : BinOperator TInt TBool
  GE  : BinOperator TInt TBool
  GT  : BinOperator TInt TBool

public export
data UnOperator : LNGType -> LNGType -> Type where
  Neg : UnOperator TInt TInt
  Not : UnOperator TBool TBool

public export
data Literal : LNGType -> Type where
  LitBool : Bool -> Literal TBool
  LitInt : Integer -> Literal TInt

export
data Variable : LNGType -> Type where
  MkVar : String -> Variable t

export
data FunId : LNGType -> List LNGType -> Type where
  MkFunId : String -> FunId t ts

public export
data Expr : LNGType -> Type where
  Lit : Literal t -> Expr t
  Var : Variable t -> Expr t
  BinOperation : BinOperator t1 t2 -> Expr t1 -> Expr t1 -> Expr t2
  UnOperation : UnOperator t1 t2 -> Expr t1 -> Expr t2
  Call : FunId t ts -> DList Expr ts -> Expr t

public export
data Instr : Type where
  Block : List Instr -> Instr
  Assign : Variable t -> Expr t -> Instr
  If : Expr TBool -> Instr -> Instr
  IfElse : Expr TBool -> Instr -> Instr -> Instr
  While : Expr TBool -> Instr -> Instr
  Return : Expr TBool -> Instr
  RetVoid : Instr

public export
record FunDecl (retType : LNGType) (paramTypes : List LNGType) (funId : FunId retType paramTypes) where
  constructor MkFunDecl
  params : DList Variable paramTypes
  body : Instr

public export
record Program where
  constructor MkProgram
  main : FunDecl TVoid [] (MkFunId "main")
  funcs : List (t ** ts ** fun ** FunDecl t ts fun)


