module LNG.TypeChecked.Render

import Data.Doc
import LNG.TypeChecked

export
implementation DocItem LNGType where
  prt TInt    = "int"
  prt TBool   = "boolean"
  prt TString = "string"
  prt TVoid   = "void"

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

