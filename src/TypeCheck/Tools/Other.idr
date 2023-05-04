module TypeCheck.Tools.Other

import LNG.Parsed       as LNG
import LNG.TypeChecked  as TC

export
mkVar : (t : TC.LNGType) -> LNG.Ident -> TC.Variable t
mkVar t id = MkVar t (MkVarId $ unIdent id)

export
mkFun : (t : TC.LNGType) -> (ts : List TC.LNGType) -> LNG.Ident -> TC.Fun t ts
mkFun t ts id = MkFun t ts (MkFunId $ unIdent id)
