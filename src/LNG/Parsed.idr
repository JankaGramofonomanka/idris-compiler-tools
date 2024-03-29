module LNG.Parsed

import Parse.Data.Position
  
public export
data LNGType = TInt | TBool | TString | TVoid

public export
data BinOperator
  = Add
  | Sub
  | Mul
  | Div
  | Mod
  | And
  | Or
  | EQ
  | NE
  | LE
  | LT
  | GE
  | GT
  | Concat

public export
data UnOperator = Neg | Not

public export
data Literal = LitBool Bool | LitInt Integer | LitString String

public export
data Ident = MkId String

export
implementation Eq Ident where
  MkId s == MkId s' = s == s'

export
implementation Ord Ident where
  MkId s `compare` MkId s' = s `compare` s'

export
unIdent : Ident -> String
unIdent (MkId s) = s

public export
data Expr
  = Lit (^Literal)
  | Var (^Ident)
  | BinOperation (^BinOperator) (^Expr) (^Expr)
  | UnOperation (^UnOperator) (^Expr)
  | Call (^Ident) (^(List (^Expr)))

public export
data Instr
  = Block (^(List (^Instr)))
  | Declare (^LNGType) (^Ident) (^Expr)
  | Assign (^Ident) (^Expr)
  | Exec (^Expr)
  | If (^Expr) (^Instr)
  | IfElse (^Expr) (^Instr) (^Instr)
  | While (^Expr) (^Instr)
  | Return (^Expr)
  | RetVoid

public export
record FunDef where
  constructor MkFunDef
  funId : (^Ident)
  retType : (^LNGType)
  params : ^(List (^LNGType, ^Ident))
  body : (^Instr)

public export
record Program where
  constructor MkProgram
  funcs : ^(List (^FunDef))


