module Compile.Data.VarContext

import Data.DMap
import Data.DSum
import Data.GCompare
import Data.Some
import Data.The
import Data.Typed
import LNG.TypeChecked
import LLVM
import LLVM.Generalized as LLVM.G
import Compile.Utils


{-
A map, that stores the values of variables in a particular place in the control
flow graph
-}
export
VarCTX : Type
VarCTX = DMap Variable (LLValue . GetLLType)

-- Same as `VarCTX` but every value is in a register
export
VarCTX' : Type
VarCTX' = DMap Variable (Reg . GetLLType)

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

  export
  intersection : VarCTX -> VarCTX -> VarCTX
  intersection = DMap.intersection

  export
  keys : VarCTX -> List (t ** Variable t)
  keys ctx = map toDPair (keys ctx) where
    
    toDPair : Some Variable -> (t ** Variable t)
    toDPair (MkSome var) = case typeOf {f = Variable} var of
      MkThe t => (t ** var)
  
  export
  toDMap : VarCTX -> DMap Variable (LLValue . GetLLType)
  toDMap = id

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
