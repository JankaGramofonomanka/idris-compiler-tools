module Compile.Data.FunContext

import Data.DMap
import Data.GCompare
import LNG.TypeChecked
import LLVM.Generalized as LLVM.G
import Compile.Data.LLVM as LLVM
import Compile.Data.LLVM.Utils

export
FunCTX : Type
FunCTX = DMap Fun' FunVal'


export
empty : FunCTX
empty = DMap.empty

export
lookup : Fun t ts -> FunCTX -> Maybe (FunVal t ts)
lookup {t, ts} fun ctx = DMap.lookup {v = (t, ts)} fun ctx

export
insert : Fun t ts -> FunVal t ts -> FunCTX -> FunCTX
insert fun val ctx = DMap.insert {v = (t, ts)} fun val ctx

export
union : FunCTX -> FunCTX -> FunCTX
union = DMap.union

