{-
  A simple programming language, for testing the usefulness and demonstration
  of compiler frameworks defined in this project.
-}
module LNG

import Data.DList

public export
data LNGType = TInt | TBool | TVoid

data EqComparable : LNGType -> Type where
  EqCMPInt : EqComparable TInt
  EqCMPBool : EqComparable TBool

public export
data Operator : LNGType -> LNGType -> Type where
  Add : Operator TInt TInt
  Sub : Operator TInt TInt
  Mul : Operator TInt TInt
  Div : Operator TInt TInt
  And : Operator TBool TBool
  Or  : Operator TBool TBool
  
  EQ  : {auto 0 prf : EqComparable t} -> Operator t TBool
  LE  : Operator TInt TBool
  LT  : Operator TInt TBool
  GE  : Operator TInt TBool
  GT  : Operator TInt TBool

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
  Operation : Operator t1 t2 -> Expr t1 -> Expr t1 -> Expr t2
  Call : FunId t ts -> DList Expr ts -> Expr t

public export
data Instr : Type where
  Assign : Variable t -> Expr t -> Instr
  If : Expr TBool -> Instr -> Instr
  IfElse : Expr TBool -> Instr -> Instr -> Instr
  Return : Expr TBool -> Instr
  RetVoid : Instr

public export
record FunDecl (retType : LNGType) (paramTypes : List LNGType) (funId : FunId retType paramTypes) where
  constructor MkFunDecl
  params : DList Variable paramTypes
  body : List Instr

public export
record Program where
  constructor MkProgram
  main : FunDecl TVoid [] (MkFunId "main")
  funcs : (t ** ts ** fun ** FunDecl t ts fun)


