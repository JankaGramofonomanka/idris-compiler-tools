module LNG.TypeChecked.Render

import Data.Doc
import LNG.TypeChecked

export
implementation DocItem LNGType where
  prt TInt    = "int"
  prt TBool   = "boolean"
  prt TString = "string"
  prt TVoid   = "void"
