module Data.Some

public export
data Some : (t -> Type) -> Type where
  MkSome : {0 a : t} -> f a -> Some f



