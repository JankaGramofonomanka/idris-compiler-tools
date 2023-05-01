module Data.Typed

public export
data The : a -> Type where
  MkThe : (x : a) -> The x

export
map : (f : a -> b) -> The x -> The (f x)
map f (MkThe x) = MkThe (f x)

export
unThe : {0 x : a} -> The x -> a
unThe (MkThe x) = x

public export
interface Typed (0 f : a -> Type) where
  typeOf : {0 x : a} -> f x -> The x

export
typeOf' : (impl : Typed {a} f) => {0 x : a} -> f x -> a
typeOf' fx = unThe (typeOf fx @{impl})

