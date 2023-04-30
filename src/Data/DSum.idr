module Data.DSum

import Data.Some

infixr 1 :=>
public export
data DSum : (tag : a -> Type) -> (f : a -> Type) -> Type where 
  (:=>) : {0 x : a} -> tag x -> f x -> DSum tag f

export
fst : DSum tag f -> Some tag
fst (x :=> y) = MkSome x

export
snd : DSum tag f -> Some f
snd (x :=> y) = MkSome y

export
toSome : DSum tag f -> Some (\x => (tag x, f x))
toSome (x :=> y) = MkSome (x, y)
