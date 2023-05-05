module Compile.Tools.CompM

import Control.Monad.State
import Control.Monad.Either

--import Data.DMap
import Data.GCompare
import Data.GEq
import Data.The
import Data.Typed

import LLVM
import LNG.TypeChecked

import Compile.Tools
import Compile.Tools.CBlock
import Compile.Tools.Context
import CFG

import Utils

public export
record CompState where
  constructor MkCompST
  -- TODO: move this type to a separate module, as with `VarCTX`
  funcs : FunCTX
  regCount : Int
  lblCount : Int

export
emptyState : CompState
emptyState = MkCompST { funcs = empty, regCount = 0, lblCount = 0 }

public export
data Error : Type where
  NoSuchVariable : Variable t -> Error
  NoSuchFunction : FunId t ts -> Error
  Impossible : String -> Error


-- TODO: remove the `public` keyword
public export
CompM : Type -> Type
CompM = StateT CompState (Either Error)

export
assign : Variable t -> LLValue (GetLLType t) -> CBlock lbl ins Undefined -> CBlock lbl ins Undefined
assign var reg (MkBB { theLabel, phis, body, term, ctx })
  = MkBB { theLabel, phis, body, term, ctx = insert var reg ctx }

export
freshRegister : (t : LLType) -> CompM (Reg t)
freshRegister t = do
  n <- gets regCount
  modify { regCount := n + 1 }
  pure $ MkReg t (MkRegId $ "r" ++ show n)

export
freshRegister' : The t -> CompM (Reg t)
freshRegister' (MkThe t) = freshRegister t

export
freshLabel : CompM BlockLabel
freshLabel = do
  n <- gets lblCount
  modify { lblCount := n + 1 }
  pure $ MkBlockLabel ("L" ++ show n)

export
getFunPtr : Fun' (t, ts) -> CompM $ LLValue (Ptr $ FunType (GetLLType t) (map GetLLType ts))
getFunPtr {t, ts} funId = do
  funcs <- gets funcs
  let Just ptr = lookup funId funcs
    | Nothing => throwError (NoSuchFunction (getFunId funId))
  
  pure ptr





