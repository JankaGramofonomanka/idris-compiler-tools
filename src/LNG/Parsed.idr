module LNG.Parsed


public export
data LNGType = TInt | TBool | TVoid

public export
data BinOperator
  = Add
  | Sub
  | Mul
  | Div
  | And
  | Or
  | EQ
  | LE
  | LT
  | GE
  | GT

public export
data UnOperator = Neg | Not

public export
data Literal = LitBool Bool | LitInt Integer

public export
data Ident = MkId String

export
unIdent : Ident -> String
unIdent (MkId s) = s

public export
data Expr
  = Lit Literal
  | Var Ident
  | BinOperation BinOperator Expr Expr
  | UnOperation UnOperator Expr
  | Call Ident (List Expr)

public export
data Instr
  = Block (List Instr)
  | Assign Ident Expr
  | If Expr Instr
  | IfElse Expr Instr Instr
  | While Expr Instr
  | Return Expr
  | RetVoid

public export
record FunDecl where
  constructor MkFunDecl
  funId : Ident
  retType : LNGType
  params : List (LNGType, Ident)
  body : Instr

public export
record Program where
  constructor MkProgram
  funcs : List FunDecl


