||| A module defining the `GEq` interface
module Data.GEq

public export
toBool : Maybe thm -> Bool
toBool (Just _) = True
toBool Nothing = False

||| Constructors of types that allow for deciding the equality between values
||| of such types, even in the case when their types are constructed from
||| different parameters
|||
||| Modeled after the `GEq` typeclass from Haskells "some" package
public export
interface GEq (0 f : t -> Type) where
  ||| If the operands are equal, returns a proof, that their type parameters
  ||| are equal
  geq : f a -> f b -> Maybe (a = b)


||| Compare the operands and ignore the equality proof
export
geq', (==) : (impl : GEq f) => f a -> f b -> Bool
geq' fa fb = toBool (geq fa fb @{impl})
(==) = geq' @{impl}

||| Decide the inequality of the operands
export
ngeq', (/=) : (impl : GEq f) => f a -> f b -> Bool
ngeq' fa fb = not (geq' fa fb @{impl})
(/=) = ngeq' @{impl}
