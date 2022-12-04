module Data.Attached




public export
data Attached : (x : t) -> Type -> Type where
  Attach : (x : t) -> (y : t') -> Attached x t'

export
combine : (a -> b -> c) -> Attached x a -> Attached x b -> Attached x c
combine f (Attach x a) (Attach x b) = Attach x (f a b)

export
detach : Attached x t -> t
detach (Attach x a) = a

