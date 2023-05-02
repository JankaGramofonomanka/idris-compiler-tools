module Data.The

public export
data The : a -> Type where
  MkThe : (x : a) -> The x

export
map : (f : a -> b) -> The x -> The (f x)
map f (MkThe x) = MkThe (f x)

export
unThe : {0 x : a} -> The x -> a
unThe (MkThe x) = x
