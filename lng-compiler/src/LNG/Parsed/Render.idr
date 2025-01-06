||| A module that defines how to print the relevant not type-checked LNG items
module LNG.Parsed.Render

import Data.Doc
import LNG.Parsed

export
implementation DocItem LNGType where
  prt TInt    = "int"
  prt TBool   = "boolean"
  prt TString = "string"
  prt TVoid   = "void"

export
implementation DocItem BinOperator where
  prt Add = "(+)"
  prt Sub = "(-)"
  prt Mul = "(*)"
  prt Div = "(/)"
  prt Mod = "(%)"
  prt And = "(&&)"
  prt Or = "(||)"
  prt EQ = "(==)"
  prt NE = "(!=)"
  prt LE = "(<=)"
  prt LT = "(<)"
  prt GE = "(>=)"
  prt GT = "(>)"
  prt Concat = "(++)"

export
implementation DocItem UnOperator where
  prt Neg = "(-)"
  prt Not = "(!)"

export
implementation DocItem Literal where
  prt (LitBool b) = if b then "true" else "false"
  prt (LitInt i) = show i
  prt (LitString s) = show s

export
implementation DocItem Ident where
  prt (MkId s) = s
