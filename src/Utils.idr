module Utils

public export
deleteAll : Eq a => a -> List a -> List a
deleteAll _ Nil = Nil
deleteAll x (x' :: xs) = if x == x' then deleteAll x xs else x' :: deleteAll x xs



public export
data Forall : List a -> (a -> Type) -> Type where
  ForallNil : Forall Nil prop
  ForallCons : {x : a} -> prop x -> Forall xs prop -> Forall (x :: xs) prop



public export
data Attached : (x : t) -> Type -> Type where
  Attach : (x : t) -> (y : t') -> Attached x t'

export
combine : (a -> b -> c) -> Attached x a -> Attached x b -> Attached x c
combine f (Attach x a) (Attach x b) = Attach x (f a b)

export
detach : Attached x t -> t
detach (Attach x a) = a


