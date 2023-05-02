module Data.Typed

import Data.The

public export
interface Typed (0 f : a -> Type) where
  typeOf : {0 x : a} -> f x -> The x

export
typeOf' : (impl : Typed {a} f) => {0 x : a} -> f x -> a
typeOf' fx = unThe (typeOf fx @{impl})

