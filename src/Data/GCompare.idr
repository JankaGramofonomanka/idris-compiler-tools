module Data.GCompare

import Data.GEq

public export
data GOrdering : t -> t -> Type where
  GLT : GOrdering a b
  GEQ : GOrdering a a
  GGT : GOrdering a b

public export
interface (geqImpl : GEq f) => GCompare (0 f : t -> Type) where
  gcompare : f a -> f b -> GOrdering a b
