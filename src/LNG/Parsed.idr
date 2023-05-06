module LNG.Parsed

public export
record Position where
  constructor MkPosition
  line : Int
  column : Int
  

public export
data Pos

  = Between Position Position
  
  -- used, when the AST tree is artificially constructed in the code, eg. in tests.
  | Fake Int

prefix 10 ^
infix 1 |^
public export
data (^) : Type -> Type where
  (|^) : Pos -> a -> ^ a

export
pos : ^a -> Pos
pos (p |^ x) = p

export
unPos : ^a -> a
unPos (p |^ x) = x

prefix 10 ^^
export
(^^) : ^a -> a
(^^) = unPos


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
  | Call (^Ident) (List $ ^Expr)

public export
data Instr
  = Block (List $ ^Instr)
  | Declare (^LNGType) (^Ident) (^Expr)
  | Assign (^Ident) (^Expr)
  | If (^Expr) (^Instr)
  | IfElse (^Expr) (^Instr) (^Instr)
  | While (^Expr) (^Instr)
  | Return (^Expr)
  | RetVoid

public export
record FunDecl where
  constructor MkFunDecl
  funId : (^Ident)
  retType : (^LNGType)
  params : List (^LNGType, ^Ident)
  body : (^Instr)

public export
record Program where
  constructor MkProgram
  funcs : List (^FunDecl)


