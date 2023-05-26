module Compile.Data.Error

import LNG.TypeChecked

public export
data Error : Type where
  NoSuchVariable : Variable t -> Error
  NoSuchFunction : FunId t ts -> Error
  Impossible : String -> Error

