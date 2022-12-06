module Prop.Elem.Eq

import Data.So
import Prop.Forall

public export
data Elem : Eq a => a -> List a -> Type where
  ElemHead : Eq a => {x, y : a} -> So (x == x') -> x `Elem` (x' :: xs)
  ElemTail : Eq a => {x, y : a} -> x `Elem` xs  -> x `Elem` (x' :: xs)


public export
NotElem : Eq a => a -> List a -> Type
NotElem x l = Forall l (\y => So (not $ x == y))


