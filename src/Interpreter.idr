module Interpreter

import Control.Monad.Either
import Control.Monad.State

import Data.SortedMap

import Data.Console
import Interpreter.Data.Error
import Interpreter.Data.InterpreterT
import Interpreter.Program
import LNG.Parsed



interpreter : MonadError String m => ConsoleI m => ConsoleO m => Program -> EitherT Error m ()
interpreter = evalStateT initState . interpretProgram

