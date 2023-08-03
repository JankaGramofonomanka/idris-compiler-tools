module Compile.Phase2.Data.CompM'

import Control.Monad.Either
import Control.Monad.State

import Data.The
import Data.Typed
import Compile.Data.CompM
import Compile.Data.Error
import Compile.Phase2.Data.VarContext
import Compile.Utils
import LLVM
import LLVM.Generalized
import LNG.TypeChecked

public export
CompM' : Type -> Type
CompM' = StateT VarCTX CompM

export
getValue : Variable t -> CompM' (LLValue (GetLLType t))
getValue var = do
  Just val <- gets (lookup var) | Nothing => lift $ throwError (NoSuchVariable var)
  pure val

export
assignRegister : Variable t -> LLValue (GetLLType t) -> CompM' ()
assignRegister var reg = modify (insert var reg)

export
freshRegisterFor : Variable t -> CompM' (Reg $ GetLLType t)
freshRegisterFor var = do
  reg <- lift $ freshReg' (map GetLLType $ typeOf var)
  assignRegister var (Var reg)
  pure reg
