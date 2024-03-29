module Data.Some

import Data.GEq
import Data.GCompare

public export
data Some : (t -> Type) -> Type where
  MkSome : {0 a : t} -> f a -> Some f

export
implementation [viaGEq] (impl : GEq f) => Eq (Some f) where
  MkSome x == MkSome y = geq' x y @{impl}

export
implementation [viaGCompare] (impl : GCompare f) => Ord (Some f) using viaGEq where
  compare (MkSome x) (MkSome y) = case gcompare x y @{impl} of
    GLT => LT
    GGT => GT
    GEQ => EQ

export
withSome : Some f -> ({0 x : a} -> f x -> b) -> b
withSome (MkSome thing) some = some thing

export
map : ({0 a : t} -> f a -> g a) -> Some f -> Some g
map f (MkSome x) = MkSome (f x)
