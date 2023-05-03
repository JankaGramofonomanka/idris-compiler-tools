module TypeCheck.TypeCheckM

import Control.Monad.Either
import Control.Monad.State

import Data.SortedMap

import LNG.Parsed       as LNG
import LNG.TypeChecked  as TC

record TypeCheckState where
  constructor MkTCST
  funcs : SortedMap Ident (TC.LNGType, List TC.LNGType)

public export
data Error
  = NoSuchVariable Ident
  | NoSuchFunction Ident
  | TypeError
  | NumParamsMismatch

-- TODO: remove the `public` keyword
public export
TypeCheckM : Type -> Type
TypeCheckM = StateT TypeCheckState (Either Error)


export
getFunTypes : Ident -> TypeCheckM (TC.LNGType, List TC.LNGType)
getFunTypes funId = do
  Just ptr <- gets (lookup funId . funcs)
            | Nothing => throwError (NoSuchFunction funId)
  pure ptr
