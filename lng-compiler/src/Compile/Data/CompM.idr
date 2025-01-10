module Compile.Data.CompM

import Control.Monad.State
import Control.Monad.Either

import Data.SortedMap
import Data.Vect

import Data.Attached
import Data.Singleton
import Data.Typed

import LLVM
import LNG.TypeChecked

import Compile.Data.CBlock
import Compile.Data.Context
import Compile.Data.Error
import Compile.Utils
import ControlFlow.CFG

||| The state of the compiler
public export
record CompState where
  constructor MkCompST

  ||| The mapping from LNG functions to LLVM function pointers
  funcs : FunCTX

  ||| The number of registers used so far. Used to generate unique register
  ||| names
  regCount : Int

  ||| The number of labels used so far. Used to generate unique label names
  lblCount : Int

  ||| The mapping from string literals to the constant pointers representing
  ||| them.
  strLits : SortedMap String (n ** (Const (Array I8 n), LLValue (Array I8 n)))

  ||| The number of string literals identified so far. Used to generate unique
  ||| constant names for constants representing the string literals.
  strLitCount : Int

||| An empty compiler state
export
emptyState : CompState
emptyState = MkCompST { funcs = empty, regCount = 0, lblCount = 0, strLits = empty, strLitCount = 0 }

-- TODO: remove the `public` keyword
-- I keep it public because I don't know how to export the instances for
-- `StateT` without it.
||| The comiler monad
public export
CompM : Type -> Type
CompM = StateT CompState (Either Error)

||| Generate a unique register of the given type
||| @ t the type of the register
export
freshRegister : (t : LLType) -> CompM (Reg t)
freshRegister t = do
  n <- gets regCount
  modify { regCount := n + 1 }
  pure $ MkReg (Val t) (MkRegId $ "r" ++ show n)

||| Generate a unique register of the given type
||| @ t the type of the register
export
freshRegister' : Singleton t -> CompM (Reg t)
freshRegister' (Val t) = freshRegister t

||| Generate a unique label
export
freshLabel : CompM Label
freshLabel = do
  n <- gets lblCount
  modify { lblCount := n + 1 }
  pure $ MkLabel ("L" ++ show n)

||| Get the function pointer representing the given LNG function
||| @ fun the LNG function identifier
export
getFunPtr : (fun : Fun' (t, ts)) -> CompM $ LLValue (Ptr $ FunType (GetLLType t) (map GetLLType ts))
getFunPtr {t, ts} funId = do
  funcs <- gets funcs
  let Just ptr = lookup funId funcs
    | Nothing => throwError (NoSuchFunction (getFunId funId))

  pure ptr

||| Generate a unique string literal constant
||| @ n the size of the array representing the string literal
freshStrConst : (n : Nat) -> CompM (Const (Array I8 n))
freshStrConst n = do
  k <- gets strLitCount
  modify { strLitCount $= (+1) }
  pure $ MkConst (Val $ Array I8 n) (MkConstId $ "s" ++ show k)

||| Get the constant representing the given string literal
||| @ s the string literal
export
getStringLiteral : (s : String) -> CompM (n ** Const (Array I8 n))
getStringLiteral s = do

  Nothing <- lookup s <$> gets strLits
           | Just (n ** (cst, arr)) => pure (n ** cst)

  let (cstLength ** chars) = stringToCharVect s
  cst <- freshStrConst (S cstLength)
  modify { strLits $= insert s (S cstLength ** (cst, Lit $ CharArrLit chars)) }

  pure (S cstLength ** cst)



