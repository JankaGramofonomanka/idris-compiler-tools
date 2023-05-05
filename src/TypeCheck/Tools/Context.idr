module TypeCheck.Tools.Context

import Data.SortedMap

import LNG.Parsed       as LNG
import LNG.TypeChecked  as TC


-- TODO: consider making it non-public
public export
FunCTX : Type
FunCTX = SortedMap LNG.Ident (TC.LNGType, List TC.LNGType)

-- TODO: consider making it non-public
public export
VarCTX : Type
VarCTX = SortedMap LNG.Ident TC.LNGType

export
declare : LNG.Ident -> TC.LNGType -> VarCTX -> VarCTX
declare = insert


