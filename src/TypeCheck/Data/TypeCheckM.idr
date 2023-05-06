module TypeCheck.Data.TypeCheckM

import Control.Monad.Either
import Control.Monad.State

import Data.SortedMap

import LNG.Parsed               as LNG
import LNG.TypeChecked          as TC
import TypeCheck.Data.Context

public export
record TypeCheckState where
  constructor MkTCST
  funcs : FunCTX

public export
data Error
  = NoSuchVariable Ident
  | NoSuchFunction Ident
  | TypeError
  | NumParamsMismatch
  | ReturnPrecedingInstructions
  | MissingReturnInstr
  | NoMainFunction
  | VariableAlreadyDeclared Ident

-- TODO: remove the `public` keyword
public export
TypeCheckM : Type -> Type
TypeCheckM = StateT TypeCheckState (Either Error)


export
getFunTypes : ^Ident -> TypeCheckM (TC.LNGType, List TC.LNGType)
getFunTypes funId = do
  Just ptr <- gets (lookup (^^funId) . funcs)
            | Nothing => throwError (NoSuchFunction $ ^^funId)
  pure ptr
