module TypeCheck.Data.TypeCheckM

import Control.Monad.Either
import Control.Monad.State

import Data.SortedMap

import LNG.Parsed               as LNG
import LNG.TypeChecked          as TC
import Parse.Data.Position
import TypeCheck.Data.Context
import TypeCheck.Data.Error

public export
record TypeCheckState where
  constructor MkTCST
  funcs : FunCTX

-- TODO: remove the `public` keyword
public export
TypeCheckM : Type -> Type
TypeCheckM = StateT TypeCheckState (Either Error)


export
getFunTypes : ^Ident -> TypeCheckM (TC.LNGType, List TC.LNGType)
getFunTypes funId = do
  Just (p, t, ts) <- gets (lookup (^^funId) . funcs)
            | Nothing => throwError (noSuchFunction funId)
  pure (t, ts)
