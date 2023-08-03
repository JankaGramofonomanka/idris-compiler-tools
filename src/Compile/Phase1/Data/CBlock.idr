module Compile.Phase1.Data.CBlock

import Data.Attached
import Data.Doc
import Data.DList
import Data.GCompare
import Data.The

import LLVM.Generalized as LLVM.G
import LLVM.Render
import LNG.TypeChecked
import LNG.TypeChecked.Render
import Compile.Data.CBlock as G
import Compile.Data.LLVM as LLVM
import Compile.Utils
import CFG

import Utils

public export
MbPhis : Neighbors BlockLabel -> Type
MbPhis = G.MbPhis LLVM.Reg'


public export
MbTerm : LLType -> Neighbors BlockLabel -> Type
MbTerm = G.MbTerm LLVM.Reg'

public export
CBlock : (retT : LLType)
      -> (label : BlockLabel)
      -> (ins : Neighbors BlockLabel)
      -> (outs : Neighbors BlockLabel)
      -> Type
CBlock = G.CBlock' LLVM.Reg'




