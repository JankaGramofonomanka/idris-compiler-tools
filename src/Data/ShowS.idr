||| A module defining the `ShowS` type
module Data.ShowS

||| A copy of Haskells `ShowS` type
public export
ShowS : Type
ShowS = String -> String

||| A copy of Haskells `GHC.Show.showString` function
export
showString : String -> ShowS
showString = (++)
