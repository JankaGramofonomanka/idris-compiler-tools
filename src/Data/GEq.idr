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

||| Takes a function and an optional proof of the equality between two values
||| and returns a proof of the equality between the results of that function
||| applied to these values
export
mcong : (0 f : a -> b) -> {0 x, y : a} -> Maybe (x = y) -> Maybe (f x = f y)
-- A "kosher" definition of `mcong would be this:
-- ```
-- mcong f Nothing     = Nothing
-- mcong f (Just Refl) = Just Refl
-- ```
-- but, for performance resons, I will skip the pattern matching and use
-- `believe_me` the values are indistinguishible runtime-wise.
--
-- This should be dafinable with the `cong` function
-- (`mcong f prf = map (cong f) prf`)
-- but I cannot figure out why it doesn't type check.
mcong f prf = believe_me prf

||| Like `mcong` but the function is implicit
export
mcong' : {0 f : a -> b} -> {0 x, y : a} -> Maybe (x = y) -> Maybe (f x = f y)
mcong' {f} mprf = mcong f mprf

namespace Nat
  ||| Returns a proof that the two natural numbers are equal when they are,
  ||| otherwise, returns `Nothing`
  export
  nateq : (n1, n2 : Nat) -> Maybe (n1 = n2)
  nateq Z Z = Just Refl
  nateq (S n) (S n') = mcong S (nateq n n')
  nateq _ _ = Nothing

