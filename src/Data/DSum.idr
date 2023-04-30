module Data.DSum

infixr 1 :=>
public export
data DSum : (tag : a -> Type) -> (f : a -> Type) -> Type where 
  (:=>) : {0 x : a} -> tag x -> f x -> DSum tag f
