||| A module defining the `GCompare` interface
module Data.GCompare

import Data.GEq

||| An ordering of dependent types
|||
||| Modeled after the `GOrdering` type from Haskells "some" package
public export
data GOrdering : t -> t -> Type where
  GLT : GOrdering a b
  GEQ : GOrdering a a
  GGT : GOrdering a b

||| Constructors of types that allow for comparing values of such types, even
||| in the case when their types are constructed from different parameters
|||
||| Modeled after the `GCompare` typeclass from Haskells "some" package
public export
interface (geqImpl : GEq f) => GCompare (0 f : t -> Type) where
  gcompare : f a -> f b -> GOrdering a b
