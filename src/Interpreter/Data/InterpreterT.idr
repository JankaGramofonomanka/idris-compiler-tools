module Interpreter.Data.InterpreterT

import Control.Monad.Either
import Control.Monad.State

import Data.List
import Data.SortedMap

import Data.Console
import Data.DList
import Interpreter.Data.Error
import Interpreter.Semantics
import LNG.BuiltIns
import LNG.Parsed
import Parse.Data.Position

mutual
  public export
  record InterpreterState (m : Type -> Type) where
    constructor MkIST
    ctx : SortedMap Ident (Pos, (t : LNGType ** Value t))
    funcs : SortedMap Ident (t : LNGType ** ts : List LNGType ** Fun t ts (InterpreterT m))

  public export
  InterpreterT : (Type -> Type) -> Type -> Type
  InterpreterT m = StateT (InterpreterState m) (EitherT Error m)

implementation [deepError] MonadError e m => MonadError e (InterpreterT m) where
  throwError = lift . lift . throwError
  catchError ima handler = do
    st <- get
    lift . MkEitherT $ catchError (runEitherT $ evalStateT st ima) (runEitherT . evalStateT st . handler)

export
initState : MonadError String m => ConsoleI m => ConsoleO m => InterpreterState m
initState = MkIST { ctx = empty, funcs = builtIns @{deepError} }


export
printError : Monad m => Error -> InterpreterT m ()
printError e = throwError e


export
getVar : Monad m => ^Ident -> InterpreterT m (t : LNGType ** Value t)
getVar var = do
  Just (_, val) <- gets $ lookup (^^var) . ctx
                 | Nothing => throwError $ noSuchVariable var
  pure val




export
getFun : Monad m => ^Ident -> InterpreterT m (t : LNGType ** ts : List LNGType ** Fun t ts (InterpreterT m))
getFun funId = do

  Just fun <- gets $ lookup (^^funId) . InterpreterState.funcs
            | Nothing => throwError $ noSuchFunction funId
            
  pure fun
