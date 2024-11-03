||| A module defining the `Typed` interface
module Data.Typed

import Data.Singleton

||| Dependent type constructors, that allow for computing the type parameter
||| from the value
public export
interface Typed (0 f : a -> Type) where
  ||| Return the parameter of the type of a value
  ||| @ x   the type parameter
  ||| @ val the value
  typeOf : {0 x : a} -> (val : f x) -> Singleton x

||| Return the unwrapped parameter of the type of a value
||| @ x   the type parameter
||| @ val the value
export
typeOf' : (impl : Typed {a} f) => {0 x : a} -> (val : f x) -> a
typeOf' fx = unVal (typeOf fx @{impl})
