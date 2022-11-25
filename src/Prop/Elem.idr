module Prop.Elem

public export
data Elem : a -> List a -> Type where
  ElemHead : x `Elem` (x :: xs)
  ElemTail : x `Elem` xs -> x `Elem` (x' :: xs)
