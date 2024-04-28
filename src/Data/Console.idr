||| A module defining console-like interfaces
module Data.Console

import Control.Monad.Trans

||| Type constructors that have the console-like functionality of reading input
public export
interface ConsoleI (0 m : Type -> Type) where

  ||| Read a string from input
  readStr : m String

  ||| Read an integer from input
  readInt : m Int

export
implementation ConsoleI IO where
  readStr = getLine
  readInt = cast <$> getLine

export
implementation Monad m => MonadTrans t => ConsoleI m => ConsoleI (t m) where
  readStr = lift readStr
  readInt = lift readInt

||| Type constructors that have the console-like functionality of printing output
public export
interface ConsoleO (0 m : Type -> Type) where

  ||| Print a string to the output
  printStr : String -> m ()

  ||| Print an integer to the output
  printInt : Int -> m ()

export
implementation ConsoleO IO where
  printStr = putStrLn
  printInt = putStrLn . show

export
implementation Monad m => MonadTrans t => ConsoleO m => ConsoleO (t m) where
  printInt = lift . printInt
  printStr = lift . printStr
