module Parse.Data.Parser

import Control.Monad.State

import Parse.Data.Position

public export
Parser : Type -> Type -> Type
Parser token a = StateT (Position, List token) List a

