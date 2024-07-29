module LNG.Parsed

import Derive.Prelude

import Parse.Data.Position

%language ElabReflection

||| The types of variables in LNG
public export
data LNGType = TInt | TBool | TString | TVoid

||| A binary operator
public export
data BinOperator
  = ||| `+`  - Addition
    Add
  | ||| `-`  - Subtraction
    Sub
  | ||| `*`  - Multiplication
    Mul
  | ||| `\`  - Division
    Div
  | ||| `%`  - The Modulo operator
    Mod
  | ||| `&&` - Logical "And"
    And
  | ||| `||` - Logical "Or"
    Or
  | ||| `==` - Equality
    EQ
  | ||| `!=` - Inequality
    NE
  | ||| `<=` - Lesser or equal
    LE
  | ||| `<`  - Lesser than
    LT
  | ||| `>=` - Greater or equal
    GE
  | ||| `>`  - Greater than
    GT
  | ||| `++` - Concatenation of strings
    Concat

||| An unary operator
public export
data UnOperator
  = ||| `-` - Arithmetic negation
    Neg
  | ||| `!` - Logical negation
    Not

||| A Literal, such as `0`, `"hello"`, or `false`
public export
data Literal = LitBool Bool | LitInt Integer | LitString String

||| An identifier of a variable or a function
public export
data Ident = MkId String

%runElab derive "Ident" [Eq, Ord]

export
unIdent : Ident -> String
unIdent (MkId s) = s

||| An LNG expression
public export
data Expr

  = ||| A literal
    Lit (^Literal)

  | ||| A variable
    Var (^Ident)

  | ||| A binary operation
    BinOperation (^BinOperator) (^Expr) (^Expr)

  | ||| An unary operation
    UnOperation (^UnOperator) (^Expr)

  | ||| A function call
    Call (^Ident) (^(List (^Expr)))

||| An LNG Instruction
public export
data Instr

  = ||| a block of instructions wrapped in curly braces
    Block (^(List (^Instr)))

  | ||| A declaration and a definition of a variable
    Declare (^LNGType) (^Ident) (^Expr)

  | ||| An assignment of a value to a variable
    Assign (^Ident) (^Expr)

  | ||| An evaluation of an expression
    Exec (^Expr)

  | ||| An if-then statement
    If (^Expr) (^Instr)

  | ||| An if-then-else statement
    IfElse (^Expr) (^Instr) (^Instr)

  | ||| A while loop
    While (^Expr) (^Instr)

  | ||| A return statement with a return value
    Return (^Expr)

  | ||| A return statement without a return value
    RetVoid

||| A definition of a function
public export
record FunDef where
  constructor MkFunDef

  ||| The identifier of the function
  funId : (^Ident)

  ||| The return type
  retType : (^LNGType)

  ||| The parameter identifiers and their types
  params : ^(List (^LNGType, ^Ident))

  ||| the body of the definition
  body : (^Instr)

||| An LNG Program
public export
record Program where
  constructor MkProgram
  ||| The funciton definitions that make up the program
  funcs : ^(List (^FunDef))
