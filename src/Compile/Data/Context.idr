module Compile.Data.Context

import Control.Monad.State

import Data.Attached
import Data.DMap
import Data.DList
import Data.DSum
import Data.GCompare
import Data.Some
import Data.The
import Data.Typed
import LNG.TypeChecked
import LLVM
import Compile.Utils
import CFG

public export
FunVal : LNGType -> List LNGType -> Type
FunVal t ts = LLValue (Ptr $ FunType (GetLLType t) (map GetLLType ts))

public export
FunVal' : (LNGType, List LNGType) -> Type
FunVal' (t, ts) = FunVal t ts

export
FunCTX : Type
FunCTX = DMap Fun' FunVal'

{-
A map, that stores the values of variables in a particular place in the control
flow graph
-}
export
VarCTX : Type
VarCTX = DMap Variable (LLValue . GetLLType)

-- Same as `VarCTX` but every value is in a register
public export
VarCTX' : Type
VarCTX' = DMap Variable (Reg . GetLLType)


namespace FunCTX

  export
  empty : FunCTX
  empty = DMap.empty

  export
  lookup : Fun t ts -> FunCTX -> Maybe (FunVal t ts)
  lookup {t, ts} fun ctx = DMap.lookup {v = (t, ts)} fun ctx

  export
  insert : Fun t ts -> FunVal t ts -> FunCTX -> FunCTX
  insert fun val ctx = DMap.insert {v = (t, ts)} fun val ctx

namespace VarCTX

  export
  empty : VarCTX
  empty = DMap.empty

  export
  lookup : Variable t -> VarCTX -> Maybe (LLValue (GetLLType t))
  lookup var ctx = DMap.lookup var ctx

  export
  insert : Variable t -> LLValue (GetLLType t) -> VarCTX -> VarCTX
  insert var val ctx = DMap.insert var val ctx

  export
  union : VarCTX -> VarCTX -> VarCTX
  union = DMap.union

  export
  toList : VarCTX -> List (DSum Variable (LLValue . GetLLType))
  toList = DMap.toList
  
namespace VarCTX'

  export
  empty : VarCTX'
  empty = DMap.empty

  export
  lookup : Variable t -> VarCTX' -> Maybe (Reg (GetLLType t))
  lookup var ctx = DMap.lookup var ctx

  export
  insert : Variable t -> Reg (GetLLType t) -> VarCTX' -> VarCTX'
  insert var val ctx = DMap.insert var val ctx

  export
  union : VarCTX' -> VarCTX' -> VarCTX'
  union = DMap.union

  export
  toList : VarCTX' -> List (DSum Variable (Reg . GetLLType))
  toList = DMap.toList

  export
  toValues : VarCTX' -> VarCTX
  toValues ctx = DMap.map Var ctx
