||| Extra utilities for the `Singleton` type
module Data.Singleton.Extra

import Data.Singleton

||| Apply
export
(<$>) : (f : a -> b) -> Singleton x -> Singleton (f x)
(<$>) f (Val x) = Val (f x)

