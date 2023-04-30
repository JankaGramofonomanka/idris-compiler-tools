{-
  A simple programming language, for testing the usefulness and demonstration
  of compiler frameworks defined in this project.
-}
module LNG

import Data.DList
import Data.GCompare
import Data.GEq

public export
data LNGType = TInt | TBool | TVoid

export
implementation Eq LNGType where
  TInt  == TInt   = True
  TBool == TBool  = True
  TVoid == TVoid  = True
  _     == _      = False

export
implementation Ord LNGType where
  compare TInt TInt = EQ
  compare TInt TBool = LT
  compare TInt TVoid = LT

  compare TBool TInt = GT
  compare TBool TBool = EQ
  compare TBool TVoid = LT
  
  compare TVoid TInt = GT
  compare TVoid TBool = GT
  compare TVoid TVoid = EQ

export
lngeq : (t1 : LNGType) -> (t2 : LNGType) -> Maybe (t1 = t2)
TInt  `lngeq` TInt  = Just Refl
TBool `lngeq` TBool = Just Refl
TVoid `lngeq` TVoid = Just Refl
_     `lngeq` _     = Nothing

export
lngcompare : (t1 : LNGType) -> (t2 : LNGType) -> GOrdering t1 t2

lngcompare TInt  TInt  = GEQ
lngcompare TInt  TBool = GLT
lngcompare TInt  TVoid = GLT

lngcompare TBool TInt  = GGT
lngcompare TBool TBool = GEQ
lngcompare TBool TVoid = GLT

lngcompare TVoid TInt  = GGT
lngcompare TVoid TBool = GGT
lngcompare TVoid TVoid = GEQ

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
  MkVar : (t : LNGType) -> String -> Variable t

export
implementation GEq Variable where
  MkVar t1 id1 `geq` MkVar t2 id2 = case t1 `lngeq` t2 of
    Just prf => if id1 == id2 then Just prf else Nothing
    Nothing => Nothing

export
implementation GCompare Variable where
  gcompare (MkVar t1 id1) (MkVar t2 id2) = case compare id1 id2 of
    LT => GLT
    EQ => lngcompare t1 t2
    GT => GGT

-- TODO: should this be public?
public export
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


