module Compile.Tools.CompM

import Control.Monad.State
import Control.Monad.Either

import Data.DMap
import Data.GCompare
import Data.GEq

import LLVM
import LNG

import Compile.Tools
import Compile.Tools.CBlock
import CFG

import Utils

public export
FunKey : (LNGType, List LNGType) -> Type
FunKey (t, ts) = Fun t ts

thm : (t : (LNGType, List LNGType)) -> Fun (fst t) (snd t) = FunKey t
thm (t, ts) = Refl

export
implementation GEq FunKey where
  geq {a, b} k1 k2 = rewrite tuple_destruct a
                  in rewrite tuple_destruct b
                  in funeq (rewrite thm a in k1) (rewrite thm b in k2)

export
implementation GCompare FunKey where
  gcompare {a, b} k1 k2 = rewrite tuple_destruct a
                       in rewrite tuple_destruct b
                       in funcompare (rewrite thm a in k1) (rewrite thm b in k2)
                       

public export
FunVal : (LNGType, List LNGType) -> Type
FunVal (t, ts) = LLValue (Ptr $ FunType (GetLLType t) (map GetLLType ts))

public export
record CompState where
  constructor MkCompST
  -- TODO: move this type to a separate module, as with `VarCTX`
  funcs : DMap FunKey FunVal
  regCount : Int
  lblCount : Int

export
emptyState : CompState
emptyState = MkCompST { funcs = DMap.empty, regCount = 0, lblCount = 0 }

public export
data Error : Type where
  NoSuchVariable : Variable t -> Error
  NoSuchFunction : FunId t ts -> Error
  UnexpectedOpenGraph : Error
  Impossible : String -> Error


-- TODO: remove the `public` keyword
public export
CompM : Type -> Type
CompM = StateT CompState (Either Error)

export
assign : Variable t -> LLValue (GetLLType t) -> CBlock lbl ins Undefined -> CBlock lbl ins Undefined
assign var reg (MkBB phis body term ctx) = MkBB phis body term $ insert var reg ctx

export
freshRegister : CompM (Reg t)
freshRegister = do
  n <- gets regCount
  modify { regCount := n + 1 }
  pure $ MkReg ("r" ++ show n)

export
freshLabel : CompM BlockLabel
freshLabel = do
  n <- gets lblCount
  modify { lblCount := n + 1 }
  pure $ MkBlockLabel ("L" ++ show n)

export
getFunPtr : FunKey (t, ts) -> CompM $ LLValue (Ptr $ FunType (GetLLType t) (map GetLLType ts))
getFunPtr {t, ts} funId = do
  funcs <- gets funcs
  let Just ptr = DMap.lookup {v = (t, ts)} funId funcs
    | Nothing => throwError (NoSuchFunction (getFunId funId))
  
  pure ptr





