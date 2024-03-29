module Compile.Data.CompM

import Control.Monad.State
import Control.Monad.Either

import Data.SortedMap
import Data.Vect

import Data.Attached
import Data.GCompare
import Data.GEq
import Data.The
import Data.Typed

import LLVM
import LNG.TypeChecked

import Compile.Data.CBlock
import Compile.Data.Context
import Compile.Data.Error
import Compile.Utils
import CFG

import Utils

public export
record CompState where
  constructor MkCompST
  funcs : FunCTX
  regCount : Int
  lblCount : Int
  strLits : SortedMap String (n ** (Const (Array I8 n), LLValue (Array I8 n)))
  strLitCount : Int

export
emptyState : CompState
emptyState = MkCompST { funcs = empty, regCount = 0, lblCount = 0, strLits = empty, strLitCount = 0 }

-- TODO: remove the `public` keyword
public export
CompM : Type -> Type
CompM = StateT CompState (Either Error)

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
freshLabel : CompM Label
freshLabel = do
  n <- gets lblCount
  modify { lblCount := n + 1 }
  pure $ MkLabel ("L" ++ show n)

export
getFunPtr : Fun' (t, ts) -> CompM $ LLValue (Ptr $ FunType (GetLLType t) (map GetLLType ts))
getFunPtr {t, ts} funId = do
  funcs <- gets funcs
  let Just ptr = lookup funId funcs
    | Nothing => throwError (NoSuchFunction (getFunId funId))
  
  pure ptr

freshStrConst : (n : Nat) -> CompM (Const (Array I8 n))
freshStrConst n = do
  k <- gets strLitCount
  modify { strLitCount $= (+1) }
  pure $ MkConst (Array I8 n) (MkConstId $ "s" ++ show k)

export
getStringLiteral : String -> CompM (n ** Const (Array I8 n))
getStringLiteral s = do

  Nothing <- lookup s <$> gets strLits
           | Just (n ** (cst, arr)) => pure (n ** cst)

  let (cstLength ** chars) = stringToCharVect s
  cst <- freshStrConst (S cstLength)
  modify { strLits $= insert s (S cstLength ** (cst, Lit $ CharArrLit chars)) }

  pure (S cstLength ** cst)



