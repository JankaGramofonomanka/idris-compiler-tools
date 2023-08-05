module Compile.Data.FunContext

import Data.DMap
import Data.GCompare
import LNG.TypeChecked
import LLVM.Generalized as LLVM.G
import LLVM
import Compile.Utils

export
FunCTX : Type
FunCTX = DMap Fun' (FunVal' Reg)


export
empty : FunCTX
empty = DMap.empty

export
lookup : Fun t ts -> FunCTX -> Maybe (FunVal Reg t ts)
lookup {t, ts} fun ctx = DMap.lookup {v = (t, ts)} fun ctx

export
insert : Fun t ts -> FunVal Reg t ts -> FunCTX -> FunCTX
insert fun val ctx = DMap.insert {v = (t, ts)} fun val ctx

export
union : FunCTX -> FunCTX -> FunCTX
union = DMap.union

