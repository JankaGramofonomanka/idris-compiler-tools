||| A module describing the `The` type
module Data.The

||| Wraps a value and lifts it to the type level
||| @ x the wrapped and lifted value
|||
||| Used to enforce an exact value of values, especially return values
||| For example, the length of a vector could be described with the `The` type
||| ```idris example
||| length : Vector n a -> The n
||| ```
public export
data The : (v : a) -> Type where
  ||| Wrap a value and lift it to the type-level
  ||| @ x the wrapped and lifted value
  MkThe : (x : a) -> The x

||| Apply
export
map : (f : a -> b) -> The x -> The (f x)
map f (MkThe x) = MkThe (f x)

||| Unwrap the lifeted value
||| @ x    the value behind the wrapper
||| @ theX the wrapped value
export
unThe : {0 x : a} -> (theX : The x) -> a
unThe (MkThe x) = x

export
implementation Eq (The x) where
  _ == _ = True

export
implementation Ord (The x) where
  compare _ _ = EQ
