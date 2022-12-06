module Prop.Elem

import Prop.Forall

public export
data Elem : a -> List a -> Type where
  ElemHead : x `Elem` (x :: xs)
  ElemTail : x `Elem` xs -> x `Elem` (x' :: xs)


public export
NotElem : a -> List a -> Type
NotElem x l = Forall l (\y => Not (x = y))
