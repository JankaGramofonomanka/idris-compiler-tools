module LNG.TypeChecked.Render

import Data.String
import Data.DList
import Data.Doc
import LNG.TypeChecked
import Utils

brkts : String -> String
brkts s = "(" ++ s ++ ")"

export
implementation DocItem LNGType where
  prt TInt    = "int"
  prt TBool   = "boolean"
  prt TString = "string"
  prt TVoid   = "void"

export
implementation [infixx] DocItem (BinOperator t1 t2 t3) where
  prt Add = "+"
  prt Sub = "-"
  prt Mul = "*"
  prt Div = "/"
  prt Mod = "%"
  prt And = "&&"
  prt Or = "||"
  prt EQ = "=="
  prt NE = "!="
  prt LE = "<="
  prt LT = "<"
  prt GE = ">="
  prt GT = ">"
  prt Concat = "++"

export
implementation DocItem (BinOperator t1 t2 t3) where
  prt op = brkts (prt @{infixx} op)

export
implementation [prefixx] DocItem (UnOperator t1 t2) where
  prt Neg = "-"
  prt Not = "!"

export
implementation DocItem (UnOperator t1 t2) where
  prt op = brkts (prt @{prefixx} op)


export
implementation DocItem (Literal t) where
  prt (LitBool b) = if b then "true" else "false"
  prt (LitInt i) = show i
  prt (LitString s) = show s

export
implementation DocItem (VarId t) where
  prt (MkVarId s) = s

export
implementation DocItem (Variable t) where
  prt (MkVar t id) = prt id

export
implementation DocItem (FunId t ts) where
  prt (MkFunId s) = s

export
implementation DocItem (Fun t ts) where
  prt (MkFun t ts id) = prt id

export
implementation DocItem (Expr t) where
  prt (Lit lit) = prt lit
  prt (Var var) = prt var
  prt (BinOperation op lhs rhs) = mkSentence [brkts (prt lhs), prt op @{infixx}, brkts (prt rhs)]
  prt (UnOperation op expr) = prt op @{prefixx} ++ brkts (prt expr)
  prt (Call fun args) = prt fun ++ brkts (concat . intersperse ", " $ undmap prt args)

export
implementation DocItem (Instr k) where

  prt instr = case instr of
    (Block instrs) => concat . intersperse "\n" $ ["{"] ++ map ("    " ++) (prt' instrs) ++ ["}"]
    (Assign var expr) => mkSentence [prt var, "=", prt expr]
    (Exec expr) => prt expr
    (If cond thn) => mkSentence ["if" ++ brkts (prt cond), prt thn]
    (IfElse cond thn els) => mkSentence ["if" ++ brkts (prt cond), prt thn, "else", prt els]
    (While cond body) => mkSentence ["while" ++ brkts (prt cond), prt body]
    (Return expr) => mkSentence ["return", prt expr]
    RetVoid => "return"

    where
      prt' : Instrs k' -> List String
      prt' Nil = Nil
      prt' (TermSingleton instr) = [prt instr]
      prt' (instr :: instrs) = prt instr :: prt' instrs
