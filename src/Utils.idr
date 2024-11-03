module Utils

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
