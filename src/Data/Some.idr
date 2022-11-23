module Data.Some

import FEq

public export
data Some : (t -> Type) -> Type where
  MkSome : {0 a : t} -> f a -> Some f

export
implementation (impl : FEq f) => Eq (Some f) where
  MkSome l == MkSome r = (l == r) @{impl}

