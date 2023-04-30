module Data.ShowS

public export
ShowS : Type
ShowS = String -> String

export
showString : String -> ShowS
showString = (++)