module Compile.Data.Context

import Control.Monad.State

import Data.Attached
import Data.DMap
import Data.DList
import Data.DSum
import Data.GCompare
import Data.Singleton
import Data.Some
import Data.Typed
import LNG.TypeChecked
import LLVM
import Compile.Utils
import CFG
import Compile.Utils

||| A function context.
||| A mapping from the identifiers of the functions declared in the source code
||| to the LLVM function pointers that represent them.
export
FunCTX : Type
FunCTX = DMap Fun' FunVal'

||| A variable context.
||| A mapping from LNG variables to LLVM values that represent them in a given
||| place in the control flow graph.
export
VarCTX : Type
VarCTX = DMap Variable (LLValue . GetLLType)

||| Same as `VarCTX` but every value is in a register
export
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

  ||| A union of two function contexts.
  ||| In case of duplicates, the left context takes precedence.
  export
  union : FunCTX -> FunCTX -> FunCTX
  union = DMap.union

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

  ||| A union of two variable contexts.
  ||| In case of duplicates, the left context takes precedence.
  export
  union : VarCTX -> VarCTX -> VarCTX
  union = DMap.union

  ||| Convert a variable context to a list of variable-value paris
  export
  toList : VarCTX -> List (DSum Variable (LLValue . GetLLType))
  toList = DMap.toList

  ||| The intersection of two variable contexts.
  ||| Contains those variables that are present in both of the operands.
  ||| In case the value assigned to a given key is different the two contexts,
  ||| the left one takes precedence.
  |||
  ||| In other words, returns the variable-value paris in the first context for
  ||| the variables present in both contexts.
  export
  intersection : VarCTX -> VarCTX -> VarCTX
  intersection = DMap.intersection

  |||| Returns the variables present in the given context
  export
  keys : VarCTX -> List (t ** Variable t)
  keys ctx = map toDPair (DMap.keys ctx) where

    toDPair : Some Variable -> (t ** Variable t)
    toDPair (MkSome var) = case typeOf {f = Variable} var of
      Val t => (t ** var)

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

  ||| A union of two variable contexts.
  ||| In case of duplicates, the left context takes precedence.
  export
  union : VarCTX' -> VarCTX' -> VarCTX'
  union = DMap.union

  ||| Convert a variable context to a list of variable-register paris
  export
  toList : VarCTX' -> List (DSum Variable (Reg . GetLLType))
  toList = DMap.toList

  ||| Convert a `VarCTX'` to a `VarCTX`
  export
  toValues : VarCTX' -> VarCTX
  toValues ctx = DMap.map Var ctx
