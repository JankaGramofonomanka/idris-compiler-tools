{-
  A simple programming language, for testing the usefulness and demonstration
  of compiler frameworks defined in this project.
-}
module LNG.TypeChecked

import Data.DList
import Data.GCompare
import Data.GEq
import Data.The
import Data.Typed

import Theory

public export
data LNGType = TInt | TBool | TString | TVoid

export
implementation Eq LNGType where
  TInt    == TInt     = True
  TBool   == TBool    = True
  TString == TString  = True
  TVoid   == TVoid    = True
  _       == _        = False

export
implementation Ord LNGType where
  compare TInt TInt     = EQ
  compare TInt TBool    = LT
  compare TInt TString  = LT
  compare TInt TVoid    = LT

  compare TBool TInt    = GT
  compare TBool TBool   = EQ
  compare TBool TString = LT
  compare TBool TVoid   = LT

  compare TString TInt    = GT
  compare TString TBool   = GT
  compare TString TString = EQ
  compare TString TVoid   = LT
  
  compare TVoid TInt    = GT
  compare TVoid TBool   = GT
  compare TVoid TString = GT
  compare TVoid TVoid   = EQ

lngeq : (t1 : LNGType) -> (t2 : LNGType) -> Maybe (t1 = t2)
TInt  `lngeq` TInt  = Just Refl
TBool `lngeq` TBool = Just Refl
TVoid `lngeq` TVoid = Just Refl
_     `lngeq` _     = Nothing

lngcompare : (t, t' : LNGType) -> GOrdering t t'

lngcompare TInt  TInt     = GEQ
lngcompare TInt  TBool    = GLT
lngcompare TInt  TString  = GLT
lngcompare TInt  TVoid    = GLT

lngcompare TBool TInt     = GGT
lngcompare TBool TBool    = GEQ
lngcompare TBool TString  = GLT
lngcompare TBool TVoid    = GLT

lngcompare TString TInt     = GGT
lngcompare TString TBool    = GGT
lngcompare TString TString  = GEQ
lngcompare TString TVoid    = GLT

lngcompare TVoid TInt     = GGT
lngcompare TVoid TBool    = GGT
lngcompare TVoid TString  = GGT
lngcompare TVoid TVoid    = GEQ

lngcompare' : (ts, ts' : List LNGType) -> GOrdering ts ts'
lngcompare' Nil Nil = GEQ
lngcompare' (t :: ts) (t' :: ts') = case lngcompare t t' of
  GLT => GLT
  GGT => GGT
  GEQ => case lngcompare' ts ts' of
    GLT => GLT
    GGT => GGT
    GEQ => GEQ
lngcompare' Nil (t' :: ts') = GLT
lngcompare' (t :: ts) Nil = GGT

public export
data EqComparable : LNGType -> Type where
  EqCMPInt : EqComparable TInt
  EqCMPBool : EqComparable TBool
  EqCMPString : EqComparable TString

export
voidNotEqComparable : EqComparable TVoid -> Void
voidNotEqComparable prf = case prf of {}

public export
data BinOperator : LNGType -> LNGType -> LNGType -> Type where
  Add : BinOperator TInt TInt TInt
  Sub : BinOperator TInt TInt TInt
  Mul : BinOperator TInt TInt TInt
  Div : BinOperator TInt TInt TInt
  Mod : BinOperator TInt TInt TInt
  And : BinOperator TBool TBool TBool
  Or  : BinOperator TBool TBool TBool
  
  EQ  : {auto 0 prf : EqComparable t} -> BinOperator t t TBool
  NE  : {auto 0 prf : EqComparable t} -> BinOperator t t TBool
  LE  : BinOperator TInt TInt TBool
  LT  : BinOperator TInt TInt TBool
  GE  : BinOperator TInt TInt TBool
  GT  : BinOperator TInt TInt TBool

  Concat : BinOperator TString TString TString

binRetTypeOf : BinOperator t1 t2 t3 -> The t3

binRetTypeOf Add = MkThe TInt
binRetTypeOf Sub = MkThe TInt
binRetTypeOf Mul = MkThe TInt
binRetTypeOf Div = MkThe TInt
binRetTypeOf Mod = MkThe TInt
binRetTypeOf And = MkThe TBool
binRetTypeOf Or  = MkThe TBool

binRetTypeOf EQ = MkThe TBool
binRetTypeOf NE = MkThe TBool
binRetTypeOf LE = MkThe TBool
binRetTypeOf LT = MkThe TBool
binRetTypeOf GE = MkThe TBool
binRetTypeOf GT = MkThe TBool

binRetTypeOf Concat = MkThe TString

public export
data UnOperator : LNGType -> LNGType -> Type where
  Neg : UnOperator TInt TInt
  Not : UnOperator TBool TBool

unRetTypeOf : UnOperator t1 t2 -> The t2
unRetTypeOf Neg = MkThe TInt
unRetTypeOf Not = MkThe TBool

public export
data Literal : LNGType -> Type where
  LitBool : Bool -> Literal TBool
  LitInt : Integer -> Literal TInt
  LitString : String -> Literal TString

export
implementation Typed Literal where
  typeOf (LitBool b)    = MkThe TBool
  typeOf (LitInt i)     = MkThe TInt
  typeOf (LitString s)  = MkThe TString

public export
data VarId : LNGType -> Type where
  MkVarId : String -> VarId t

public export
data Variable : LNGType -> Type where
  MkVar : (t : LNGType) -> VarId t -> Variable t

export
implementation GEq Variable where
  MkVar t1 (MkVarId id1) `geq` MkVar t2 (MkVarId id2) = case t1 `lngeq` t2 of
    Just prf => if id1 == id2 then Just prf else Nothing
    Nothing => Nothing

export
implementation GCompare Variable where
  gcompare (MkVar t1 (MkVarId id1)) (MkVar t2 (MkVarId id2)) = case compare id1 id2 of
    LT => GLT
    EQ => lngcompare t1 t2
    GT => GGT

export
implementation Typed Variable where
  typeOf (MkVar t id) = MkThe t

public export
data FunId : LNGType -> List LNGType -> Type where
  MkFunId : String -> FunId t ts

-- TODO: should this be public?
public export
data Fun : LNGType -> List LNGType -> Type where
  MkFun : (t : LNGType) -> (ts : List LNGType) -> FunId t ts -> Fun t ts

export
getFunId : Fun t ts -> FunId t ts
getFunId (MkFun _ _ id) = id

retTypeOf : Fun t ts -> The t
retTypeOf (MkFun t ts id) = MkThe t

argTypesOf : Fun t ts -> The ts
argTypesOf (MkFun t ts id) = MkThe ts

typeOfFun : Fun t ts -> The (t, ts)
typeOfFun (MkFun t ts id) = MkThe (t, ts)

funeq : (id1 : Fun t1 ts1) -> (id2 : Fun t2 ts2) -> Maybe ((t1, ts1) = (t2, ts2))
funeq (MkFun t1 ts1 id1) (MkFun t2 ts2 id2) = case lngeq t1 t2 of
    Nothing   => Nothing
    Just tprf => case lngeq' ts1 ts2 of
      Nothing     => Nothing
      Just tsprf  => rewrite tprf
                  in rewrite tsprf
                  in Just Refl
    
    where
      lngeq' : (xs : List LNGType) -> (ys : List LNGType) -> Maybe (xs = ys)
      lngeq' Nil Nil = Just Refl
      lngeq' (x :: xs) (y :: ys) = case lngeq x y of
        Nothing => Nothing
        Just prf => case lngeq' xs ys of
          Nothing => Nothing
          Just prf' => rewrite prf
                    in rewrite prf'
                    in Just Refl
      lngeq' _ _ = Nothing

funcompare : (id1 : Fun t1 ts1) -> (id2 : Fun t2 ts2) -> GOrdering (t1, ts1) (t2, ts2)
funcompare (MkFun t ts (MkFunId id)) (MkFun t' ts' (MkFunId id')) = case compare id id' of
  LT => GLT
  GT => GGT
  EQ => case lngcompare t t' of
    GLT => GLT
    GGT => GGT
    GEQ => case lngcompare' ts ts' of
      GLT => GLT
      GEQ => GEQ
      GGT => GGT
    
  

public export
Fun' : (LNGType, List LNGType) -> Type
Fun' (t, ts) = Fun t ts

thm : (t : (LNGType, List LNGType)) -> Fun (fst t) (snd t) = Fun' t
thm (t, ts) = Refl

export
implementation GEq Fun' where
  geq {a, b} k1 k2 = rewrite tuple_destruct a
                  in rewrite tuple_destruct b
                  in funeq (rewrite thm a in k1) (rewrite thm b in k2)

export
implementation GCompare Fun' where
  gcompare {a, b} k1 k2 = rewrite tuple_destruct a
                       in rewrite tuple_destruct b
                       in funcompare (rewrite thm a in k1) (rewrite thm b in k2)

export
implementation Typed Fun' where
  typeOf {x} fun = rewrite tuple_destruct x
                in typeOfFun (rewrite thm x in fun)

public export
data Expr : LNGType -> Type where
  Lit : Literal t -> Expr t
  Var : Variable t -> Expr t
  BinOperation : BinOperator t1 t2 t3 -> Expr t1 -> Expr t2 -> Expr t3
  UnOperation : UnOperator t1 t2 -> Expr t1 -> Expr t2
  Call : Fun t ts -> DList Expr ts -> Expr t

export
implementation Typed Expr where
  typeOf (Lit l) = typeOf l
  typeOf (Var v) = typeOf v
  typeOf (BinOperation op lhs rhs) = binRetTypeOf op
  typeOf (UnOperation op expr) = unRetTypeOf op
  typeOf (Call fun args) = retTypeOf fun

public export
data InstrKind : LNGType -> Type where
  Simple : InstrKind t
  Returning : (t : LNGType) -> InstrKind t

public export
BrKind : InstrKind t -> InstrKind t -> InstrKind t
BrKind Simple         Simple          = Simple
BrKind Simple         (Returning t')  = Simple
BrKind (Returning t)  Simple          = Simple
BrKind (Returning t)  (Returning t)   = Returning t

mutual
  public export
  data Instr : InstrKind t -> Type where
    Block : Instrs k -> Instr k
    Assign : Variable t -> Expr t -> Instr Simple
    Exec : Expr TVoid -> Instr Simple
    If : Expr TBool -> Instr k -> Instr Simple
    IfElse : Expr TBool -> Instr k -> Instr k' -> Instr (BrKind k k')
    While : Expr TBool -> Instr k -> Instr Simple
    Return : Expr t -> Instr (Returning t)
    RetVoid : Instr (Returning TVoid)
    -- TODO: Add `WhileTrue`

  public export
  data Instrs : InstrKind t -> Type where
    Nil : Instrs Simple
    TermSingleton : Instr (Returning t) -> Instrs (Returning t)
    (::) : Instr Simple -> Instrs k -> Instrs k

public export
record FunDef (retType : LNGType) (paramTypes : List LNGType) (funId : FunId retType paramTypes) where
  constructor MkFunDef
  theId : The funId
  theRetType : The retType
  params : DList Variable paramTypes
  body : Instr (Returning retType)

public export
record Program where
  constructor MkProgram
  main : FunDef TInt [] (MkFunId "main")
  funcs : List (t ** ts ** fun ** FunDef t ts fun)


