module Prop.Forall

public export
data Forall : List a -> (a -> Type) -> Type where
  ForallNil : Forall Nil prop
  ForallCons : {x : a} -> prop x -> Forall xs prop -> Forall (x :: xs) prop
