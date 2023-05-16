module Interpreter.InterpreterT

import Control.Monad.Either
import Control.Monad.State

import Data.List
import Data.SortedMap

import Data.Console
import Data.DList
import Interpreter.Semantics
import LNG.BuiltIns
import LNG.Data.Position
import LNG.Parsed

data Error'
  = NoSuchVariable Ident
  | NoSuchFunction Ident
  | TypeError LNGType LNGType
  | TypeError' (List LNGType) LNGType
  | NumParamsMismatch Nat Nat
  | ReturnPrecedingInstructions
  | MissingReturnInstr
  | NoMainFunction
  | VariableAlreadyDeclared Ident Pos
  --| FunctionAlreadyDefined Ident DefPos

export
Error : Type
Error = ^Error'

export
noSuchVariable : ^Ident -> Error
noSuchVariable (p |^ ident) = p |^ NoSuchVariable ident

export
noSuchFunction : ^Ident -> Error
noSuchFunction (p |^ ident) = p |^ NoSuchFunction ident

export
typeError : Pos -> LNGType -> LNGType -> Error
typeError p expected actual = p |^ TypeError expected actual

export
typeError' : Pos -> List LNGType -> LNGType -> Error
typeError' p expected actual = p |^ TypeError' expected actual

export
numParamsMismatch : Pos -> Nat -> Nat -> Error
numParamsMismatch p expected actual = (p |^ NumParamsMismatch expected actual)

export
returnPrecedingInstructions : Pos -> Error
returnPrecedingInstructions = (|^ ReturnPrecedingInstructions)

export
missingReturnInstr : Pos -> Error
missingReturnInstr = (|^ MissingReturnInstr)

export
noMainFunction : Pos -> Error
noMainFunction = (|^ NoMainFunction)

export
variableAlreadyDeclared : ^Ident -> Pos -> Error
variableAlreadyDeclared (p |^ ident) p' = p |^ VariableAlreadyDeclared ident p'

--export
--fuctionAlreadyDefined : ^Ident -> DefPos -> Error
--fuctionAlreadyDefined (p |^ ident) p' = p |^ FunctionAlreadyDefined ident p'



mutual
  public export
  record InterpreterState (m : Type -> Type) where
    constructor MkIST
    ctx : SortedMap Ident (Pos, (t : LNGType ** Value t))
    --funcs : SortedMap Ident FunDecl
    --funInterpreter : FunDecl -> (t : LNGType ** ts : List LNGType ** Fun t ts m)
    funcs : SortedMap Ident (t : LNGType ** ts : List LNGType ** Fun t ts (InterpreterT m))

  public export
  InterpreterT : (Type -> Type) -> Type -> Type
  InterpreterT m = StateT (InterpreterState m) (EitherT Error m)

  --public export
  --Fun : LNGType -> List LNGType -> (Type -> Type) -> Type
  --Fun t ts m = DList Value ts -> InterpreterT m (Value t)

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
