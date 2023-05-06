module TypeCheck.Data.Context

import Data.SortedMap

import LNG.Data.Position
import LNG.Parsed       as LNG
import LNG.TypeChecked  as TC


export
FunCTX : Type
FunCTX = SortedMap LNG.Ident (Pos, TC.LNGType, List TC.LNGType)

export
VarCTX : Type
VarCTX = SortedMap LNG.Ident (Pos, TC.LNGType)

namespace FunCTX

  export
  empty : FunCTX
  empty = SortedMap.empty

  export
  declare : TC.LNGType -> List TC.LNGType -> ^LNG.Ident -> FunCTX -> FunCTX
  declare t ts (p |^ fun) = insert fun (p, t, ts)

  export
  lookup : LNG.Ident -> FunCTX -> Maybe (TC.LNGType, List TC.LNGType)
  lookup = map snd .: SortedMap.lookup

namespace VarCTX

  export
  empty : VarCTX
  empty = SortedMap.empty

  export
  declare : TC.LNGType -> ^LNG.Ident -> VarCTX -> VarCTX
  declare t (p |^ id) = SortedMap.insert id (p, t)

  export
  lookup : LNG.Ident -> VarCTX -> Maybe TC.LNGType
  lookup = map snd .: SortedMap.lookup

