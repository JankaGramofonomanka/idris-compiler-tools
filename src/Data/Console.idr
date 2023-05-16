module Data.Console

import Control.Monad.Trans

public export
interface ConsoleI (0 m : Type -> Type) where
  readStr : m String
  readInt : m Int

export
implementation ConsoleI IO where
  readStr = getLine
  readInt = cast <$> getLine

export
implementation Monad m => MonadTrans t => ConsoleI m => ConsoleI (t m) where
  readStr = lift readStr
  readInt = lift readInt

public export
interface ConsoleO (0 m : Type -> Type) where
  printStr : String -> m ()
  printInt : Int -> m ()
  
export
implementation ConsoleO IO where
  printStr = putStrLn
  printInt = putStrLn . show

export
implementation Monad m => MonadTrans t => ConsoleO m => ConsoleO (t m) where
  printInt = lift . printInt
  printStr = lift . printStr
