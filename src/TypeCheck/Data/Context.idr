module TypeCheck.Data.Context

import Data.SortedMap

import LNG.Parsed       as LNG
import LNG.TypeChecked  as TC


export
FunCTX : Type
FunCTX = SortedMap LNG.Ident (TC.LNGType, List TC.LNGType)

export
VarCTX : Type
VarCTX = SortedMap LNG.Ident TC.LNGType

namespace FunCTX

  export
  empty : FunCTX
  empty = SortedMap.empty

  export
  insert : LNG.Ident -> (TC.LNGType, List TC.LNGType) -> FunCTX -> FunCTX
  insert = SortedMap.insert

  export
  declare : TC.LNGType -> List TC.LNGType -> LNG.Ident -> FunCTX -> FunCTX
  declare t ts fun = FunCTX.insert fun (t, ts)

  export
  lookup : LNG.Ident -> FunCTX -> Maybe (TC.LNGType, List TC.LNGType)
  lookup = SortedMap.lookup

namespace VarCTX

  export
  empty : VarCTX
  empty = SortedMap.empty

  export
  insert : LNG.Ident -> TC.LNGType -> VarCTX -> VarCTX
  insert = SortedMap.insert

  export
  declare : TC.LNGType -> LNG.Ident -> VarCTX -> VarCTX
  declare = flip SortedMap.insert

  export
  lookup : LNG.Ident -> VarCTX -> Maybe TC.LNGType
  lookup = SortedMap.lookup

