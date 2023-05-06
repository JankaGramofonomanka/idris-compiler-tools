module TypeCheck.Utils

import LNG.Parsed       as LNG
import LNG.TypeChecked  as TC

export
mkVar : (t : TC.LNGType) -> LNG.Ident -> TC.Variable t
mkVar t id = MkVar t (MkVarId $ unIdent id)

export
mkFunId : {0 t : TC.LNGType} -> {0 ts : List TC.LNGType} -> LNG.Ident -> TC.FunId t ts
mkFunId id = MkFunId (unIdent id)

export
mkFun : (t : TC.LNGType) -> (ts : List TC.LNGType) -> LNG.Ident -> TC.Fun t ts
mkFun t ts id = MkFun t ts (mkFunId id)

export
tc : LNG.LNGType -> TC.LNGType
tc LNG.TInt   = TC.TInt
tc LNG.TBool  = TC.TBool
tc LNG.TVoid  = TC.TVoid

export
tc' : ^LNG.LNGType -> TC.LNGType
tc' (_ |^ t) = tc t

