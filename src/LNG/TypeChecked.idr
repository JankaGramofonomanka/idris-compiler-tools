||| A simple programming language, for testing the usefulness and demonstration
||| of compiler frameworks defined in this project.
module LNG.TypeChecked

import Derive.Prelude

import Data.DList
import Data.DOrd
import Data.DEq
import Data.Singleton
import Data.Typed

import Theory

%language ElabReflection

||| The types of variables in LNG
public export
data LNGType = TInt | TBool | TString | TVoid

%runElab derive "LNGType" [Eq, Ord]

implementation PEq LNGType where
  TInt  `peq` TInt  = Just Refl
  TBool `peq` TBool = Just Refl
  TVoid `peq` TVoid = Just Refl
  _     `peq` _     = Nothing

implementation POrd LNGType where
  pcompare TInt  TInt     = DEQ
  pcompare TInt  TBool    = DLT
  pcompare TInt  TString  = DLT
  pcompare TInt  TVoid    = DLT

  pcompare TBool TInt     = DGT
  pcompare TBool TBool    = DEQ
  pcompare TBool TString  = DLT
  pcompare TBool TVoid    = DLT

  pcompare TString TInt     = DGT
  pcompare TString TBool    = DGT
  pcompare TString TString  = DEQ
  pcompare TString TVoid    = DLT

  pcompare TVoid TInt     = DGT
  pcompare TVoid TBool    = DGT
  pcompare TVoid TString  = DGT
  pcompare TVoid TVoid    = DEQ

public export
data EqComparable : LNGType -> Type where
  EqCMPInt    : EqComparable TInt
  EqCMPBool   : EqComparable TBool
  EqCMPString : EqComparable TString

||| A proof that `TVoid` is not comparable, i.e., has no `EqComparable` instance
export
voidNotEqComparable : EqComparable TVoid -> Void
voidNotEqComparable prf = case prf of {}

||| A binary operator
||| @ lhsT the type of the left operand
||| @ rhsT the type of the right operand
||| @ resT the type of the result
public export
data BinOperator : (lhsT : LNGType) -> (rhsT : LNGType) -> (resT : LNGType) -> Type where
  ||| `+`  - Addition
  Add : BinOperator TInt TInt TInt
  ||| `-`  - Subtraction
  Sub : BinOperator TInt TInt TInt
  ||| `*`  - Multiplication
  Mul : BinOperator TInt TInt TInt
  ||| `\`  - Division
  Div : BinOperator TInt TInt TInt
  ||| `%`  - The Modulo operator
  Mod : BinOperator TInt TInt TInt
  ||| `&&` - Logical "And"
  And : BinOperator TBool TBool TBool
  ||| `||` - Logical "Or"
  Or  : BinOperator TBool TBool TBool

  ||| `==` - Equality
  EQ  : {auto 0 prf : EqComparable t} -> BinOperator t t TBool
  ||| `!=` - Inequality
  NE  : {auto 0 prf : EqComparable t} -> BinOperator t t TBool
  ||| `<=` - Lesser or equal
  LE  : BinOperator TInt TInt TBool
  ||| `<`  - Lesser than
  LT  : BinOperator TInt TInt TBool
  ||| `>=` - Greater or equal
  GE  : BinOperator TInt TInt TBool
  ||| `>`  - Greater than
  GT  : BinOperator TInt TInt TBool

  ||| `++` - Concatenation of strings
  Concat : BinOperator TString TString TString

||| The return type of a binary operator
binRetTypeOf : BinOperator t1 t2 t3 -> Singleton t3

binRetTypeOf Add = Val TInt
binRetTypeOf Sub = Val TInt
binRetTypeOf Mul = Val TInt
binRetTypeOf Div = Val TInt
binRetTypeOf Mod = Val TInt
binRetTypeOf And = Val TBool
binRetTypeOf Or  = Val TBool

binRetTypeOf EQ = Val TBool
binRetTypeOf NE = Val TBool
binRetTypeOf LE = Val TBool
binRetTypeOf LT = Val TBool
binRetTypeOf GE = Val TBool
binRetTypeOf GT = Val TBool

binRetTypeOf Concat = Val TString

||| An unary operator
||| @ ot the type or the operand
||| @ rt the type of the result
public export
data UnOperator : (ot : LNGType) -> (rt : LNGType) -> Type where
  ||| `-` - Arithmetic negation
  Neg : UnOperator TInt TInt
  ||| `!` - Logical negation
  Not : UnOperator TBool TBool

||| The return type of an unary operator
unRetTypeOf : UnOperator t1 t2 -> Singleton t2
unRetTypeOf Neg = Val TInt
unRetTypeOf Not = Val TBool

||| A Literal, such as `0`, `"hello"`, or `false`
||| @ t the type of the literal
public export
data Literal : (t : LNGType) -> Type where
  ||| A boolean literal
  ||| @ b the value of the literal
  LitBool   : (b : Bool)    -> Literal TBool
  ||| An integer literal
  ||| @ i the value of the literal
  LitInt    : (i : Integer) -> Literal TInt
  ||| A string literal
  ||| @ s the value of the literal
  LitString : (s : String)  -> Literal TString

export
implementation Typed Literal where
  typeOf (LitBool b)    = Val TBool
  typeOf (LitInt i)     = Val TInt
  typeOf (LitString s)  = Val TString

||| An identifier of a variable
||| @ t the type of the variable
public export
data VarId : (t : LNGType) -> Type where
  ||| Make a variable identifier
  ||| @ name the name of the variable
  MkVarId : (name : String) -> VarId t

||| An identifier of a variable with a runtime representation of its type
||| @ t the type of the variable
public export
data Variable : (t : LNGType) -> Type where
  ||| Make a `Variable` out of `VarId`
  ||| @ t     the type of the variable
  ||| @ varId the variable identifier
  MkVar : (t : LNGType) -> (varId : VarId t) -> Variable t

export
implementation DEq Variable where
  MkVar t1 (MkVarId id1) `deq` MkVar t2 (MkVarId id2)
    = peq t1 t2 `butOnlyWhen` id1 == id2

export
implementation DOrd Variable where
  dcompare (MkVar t1 (MkVarId id1)) (MkVar t2 (MkVarId id2))
    = compare id1 id2 `precedes'` pcompare t1 t2

export
implementation Typed Variable where
  typeOf (MkVar t id) = Val t

||| An identifier of a function
||| @ t  the return type of the function
||| @ ts the parameter types of the function
public export
data FunId : (t : LNGType) -> (ts : List LNGType) -> Type where
  ||| Make a function identifier
  ||| @ name the name of the function
  MkFunId : (name : String) -> FunId t ts

-- TODO: should this be public?
||| An identifier of a function with a runtime representation of its return and
||| parameter types
||| @ t  the return type of the function
||| @ ts the parameter types of the function
public export
data Fun : (t : LNGType) -> (ts : List LNGType) -> Type where
  ||| Make a `Fun` oot of `FunId`
  ||| @ t     the return type of the function
  ||| @ ts    the parameter types of the function
  ||| @ funId the function identifier
  MkFun : (t : LNGType) -> (ts : List LNGType) -> (funId : FunId t ts) -> Fun t ts

||| Extracts a `FunId` out of `Fun` by dropping the type representation
export
getFunId : Fun t ts -> FunId t ts
getFunId (MkFun _ _ id) = id

||| Returns the return type of a function identifier
retTypeOf : Fun t ts -> Singleton t
retTypeOf (MkFun t ts id) = Val t

||| Returns the types of the parameters of the function
argTypesOf : Fun t ts -> Singleton ts
argTypesOf (MkFun t ts id) = Val ts

||| Returns the return type of the function
typeOfFun : Fun t ts -> Singleton (t, ts)
typeOfFun (MkFun t ts id) = Val (t, ts)

||| If the operands are equal, returns a proof that they are, otherwise,
||| returns `Nothing`
funeq : (id1 : Fun t1 ts1) -> (id2 : Fun t2 ts2) -> Maybe ((t1, ts1) = (t2, ts2))
-- TODO why no id comaprison?
funeq (MkFun t1 ts1 id1) (MkFun t2 ts2 id2) = peq (t1, ts1) (t2, ts2)

||| Comparison of function identifiers in terms of `DOrd`
funcompare : (id1 : Fun t1 ts1) -> (id2 : Fun t2 ts2) -> DOrdering (t1, ts1) (t2, ts2)
funcompare (MkFun t ts (MkFunId id)) (MkFun t' ts' (MkFunId id'))
  = compare id id' `precedes'` pcompare (t, ts) (t', ts')

||| An alias for `Fun` parametrized by a tuple instead of two separate parameters
public export
Fun' : (LNGType, List LNGType) -> Type
Fun' (t, ts) = Fun t ts

thm : (t : (LNGType, List LNGType)) -> Fun (fst t) (snd t) = Fun' t
thm (t, ts) = Refl

export
implementation DEq Fun' where
  deq {a = (t1, ts1), b = (t2, ts2)} fun1 fun2 = funeq fun1 fun2

export
implementation DOrd Fun' where
  dcompare {a = (t1, ts1), b = (t2, ts2)} fun1 fun2 = funcompare fun1 fun2

export
implementation Typed Fun' where
  typeOf {x = (t1, t2)} fun = typeOfFun fun

||| An LNG expression
public export
data Expr : LNGType -> Type where

  ||| A literal
  ||| @ lit the literal
  Lit : (lit : Literal t) -> Expr t

  ||| A variable
  ||| @ var the variable identifier
  Var : (var : Variable t) -> Expr t

  ||| A binary operation
  ||| @ op  the operator
  ||| @ lhs the left operand
  ||| @ rhs the right operand
  BinOperation : (op : BinOperator t1 t2 t3) -> (lhs : Expr t1) -> (rhs : Expr t2) -> Expr t3

  ||| An unary operation
  ||| @ op   the operator
  ||| @ expr the operand
  UnOperation : (op : UnOperator t1 t2) -> (expr : Expr t1) -> Expr t2

  ||| A function call
  ||| @ fun the function identifier
  ||| @ the arguments passed to the function
  Call : (fun : Fun t ts) -> (args : DList Expr ts) -> Expr t

export
implementation Typed Expr where
  typeOf (Lit l)                   = typeOf l
  typeOf (Var v)                   = typeOf v
  typeOf (BinOperation op lhs rhs) = binRetTypeOf op
  typeOf (UnOperation op expr)     = unRetTypeOf op
  typeOf (Call fun args)           = retTypeOf fun

||| The kind of an instruction
public export
data InstrKind

  = ||| The default kind
    Simple

  | ||| The kind of return instructions and instruction that end with
    ||| a return instruction in their every relevant branch
    Returning

||| Returns the kinds of an if-then-else statement, given the kind of its branches
public export
BrKind : InstrKind -> InstrKind -> InstrKind
BrKind Simple     Simple    = Simple
BrKind Simple     Returning = Simple
BrKind Returning  Simple    = Simple
BrKind Returning  Returning = Returning

mutual
  ||| An LNG Instruction
  ||| @ returnType the return type of the function the instruction is part of,
  |||              used to enforce the correct type of returned values
  ||| @ kind       the kind of the instruction - simple or returning
  public export
  data Instr : (returnType : LNGType) -> (kind : InstrKind) -> Type where

    ||| A block of instructions wrapped in curly braces
    ||| @ instrs the instructions that make up the block
    Block : (instrs : Instrs rt k) -> Instr rt k

    ||| An assignment of a value to a variable
    ||| @ var  the variable to assign value to
    ||| @ expr the expression whose value will be assigned to the variable
    Assign : (var : Variable t) -> (expr : Expr t) -> Instr rt Simple

    ||| An evaluation of a void expression
    ||| @ expr the expression to evaluate
    Exec : (expr : Expr TVoid) -> Instr rt Simple

    ||| An if-then statement
    ||| @ cond the "if" condition
    ||| @ branch the instruction to execute, when the condition is true
    If : (cond : Expr TBool) -> (branch : Instr rt k) -> Instr rt Simple

    ||| An if-then-else statement
    ||| @ cond the "if" condition
    ||| @ thn the "then" branch - the instruction to execute, when the
    |||       condition is true
    ||| @ els the "else" branch - the instruction to execute, when the
    |||       condition is false
    IfElse : {k, k' : InstrKind}
          -> (cond : Expr TBool)
          -> (thn : Instr rt k)
          -> (els : Instr rt k')
          -> Instr rt (BrKind k k')

    ||| A while loop
    ||| @ cond the "while" condition
    ||| @ body the body of the loop
    While : (cond : Expr TBool) -> (body : Instr rt k) -> Instr rt Simple

    ||| A return statement with a return value
    ||| @ expr the returned expression
    Return : (expr : Expr t) -> Instr t Returning

    ||| A return statement without a return value
    RetVoid : Instr TVoid Returning
    -- TODO: Add `WhileTrue`

  ||| A list of simple in structions, followed by a simple or a returning instructions
  ||| @ returnType the return type of the function the instructions are part of,
  |||              used to enforce the correct type of returned values
  ||| @ kind       the kind of the instruction list - simple or returning
  public export
  data Instrs : (returnType : LNGType) -> (kind : InstrKind) -> Type where

    ||| An empty list
    Nil : Instrs rt Simple

    ||| A singleton list containing a returning instruction (a terminator)
    ||| @ term the terminator
    TermSingleton : (term : Instr rt Returning) -> Instrs rt Returning

    ||| A simple instruction prepended to a list of instructions
    ||| @ hd the head of the list
    ||| @ tl the tail of the list
    (::) : (hd : Instr rt Simple) -> (tl : Instrs rt k) -> Instrs rt k

||| A definition of a function
public export
record FunDef where
  constructor MkFunDef

  ||| The return type
  retType : LNGType

  ||| The identifier of the function
  funId : Fun retType paramTypes

  ||| The parameters identifiers
  params : DList Variable paramTypes

  ||| the body of the definition
  body : Instr retType Returning

||| An LNG Program
public export
record Program where
  constructor MkProgram
  ||| The funciton definitions that make up the program
  funcs : List FunDef
