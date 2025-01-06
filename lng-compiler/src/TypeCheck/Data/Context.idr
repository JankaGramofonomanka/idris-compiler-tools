module TypeCheck.Data.Context

import Data.SortedMap

import LNG.Parsed       as LNG
import LNG.TypeChecked  as TC
import Parse.Data.Position

public export
data DefPos = BuiltIn | DefinedAt Pos

export
FunCTX : Type
FunCTX = SortedMap LNG.Ident (DefPos, TC.LNGType, List TC.LNGType)

export
VarCTX : Type
VarCTX = SortedMap LNG.Ident (Pos, TC.LNGType)

namespace FunCTX

  export
  empty : FunCTX
  empty = SortedMap.empty

  export
  declare : TC.LNGType -> List TC.LNGType -> ^LNG.Ident -> FunCTX -> FunCTX
  declare t ts (p |^ fun) = insert fun (DefinedAt p, t, ts)

  export
  declareBuiltIn : TC.LNGType -> List TC.LNGType -> LNG.Ident -> FunCTX -> FunCTX
  declareBuiltIn t ts fun = insert fun (BuiltIn, t, ts)

  export
  lookup : LNG.Ident -> FunCTX -> Maybe (DefPos, TC.LNGType, List TC.LNGType)
  lookup = SortedMap.lookup

  export
  union : FunCTX -> FunCTX -> FunCTX
  union = mergeLeft

namespace VarCTX

  export
  empty : VarCTX
  empty = SortedMap.empty

  export
  declare : TC.LNGType -> ^LNG.Ident -> VarCTX -> VarCTX
  declare t (p |^ id) = SortedMap.insert id (p, t)

  export
  lookup : LNG.Ident -> VarCTX -> Maybe (Pos, TC.LNGType)
  lookup = SortedMap.lookup

