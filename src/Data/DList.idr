module Data.DList


public export
data DList : (a -> Type) -> List a -> Type where
  Nil : DList f Nil
  (::) : {0 x : a} -> f x -> DList f xs -> DList f (x :: xs)

public export
(++) : DList f xs -> DList f ys -> DList f (xs ++ ys)
Nil         ++ fys = fys
(fx :: fxs) ++ fys = fx :: fxs ++ fys
