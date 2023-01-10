module Compile.Tools.CompM

import Control.Monad.State
import Control.Monad.Either

import Data.DMap

import LLVM
import LNG

import Compile.Tools
import Compile.Tools.CBlock
import CFG

public export
record CompState where
  constructor MkCompST

public export
data Error : Type where
  NoSuchVariable : Variable t -> Error
  NoSuchFunction : FunId t ts -> Error


public export
CompM : Type -> Type
CompM = StateT CompState (Either Error)

export
assign : Variable t -> LLValue (GetLLType t) -> CBlock lbl ins Undefined -> CBlock lbl ins Undefined
assign var reg (MkBB phis body term ctx) = MkBB phis body term $ insert var reg ctx

export
freshReg : CompM (Reg t)

export
freshLabel : CompM BlockLabel

export
addBlock : CBlock lbl (Just inputs) (Just cfk) -> CompM ()

export
getValue : Variable t -> CompM (LLValue (GetLLType t))

export
getFunPtr : FunId t ts -> CompM $ LLValue (Ptr $ FunType (GetLLType t) (map GetLLType ts))

export
freshRegister : CompM (Reg t)





