||| A module defining the dependent list and its interface
module Data.DList


||| A dependent list
||| @ f  the constructor of the types of elements
||| @ ts the partameters from which the types of the lists elements are
|||      constructed
public export
data DList : (f : a -> Type) -> (ts : List a) -> Type where
  ||| The empty dependent list
  Nil : DList f Nil
  ||| Prepends a dependently typed element to a dependent list
  (::) : {0 x : a} -> f x -> DList f xs -> DList f (x :: xs)

||| Concatenate two dependent lists
public export
(++) : DList f xs -> DList f ys -> DList f (xs ++ ys)
Nil         ++ fys = fys
(fx :: fxs) ++ fys = fx :: fxs ++ fys

||| Return the length of a dependent list
export
length : DList f xs -> Nat
length Nil = Z
length (x :: xs) = S (length xs)

-- TODO: rewrite in terms of `Applicative`
||| Dependent version of `traverse`.
|||
||| Map each element of a dependent list to a computation, evaluate those
||| computations and combine the results.
export
dtraverse : Monad f
        => {0 t : Type}
        -> {0 a, b : t -> Type}
        -> {0 xs : List t}

        -> ({0 x : t} -> a x -> f (b x))
        -> DList a xs
        -> f (DList b xs)

dtraverse f Nil = pure Nil
dtraverse f (ax :: axs) = do
  bx <- f ax
  bxs <- dtraverse f axs

  pure (bx :: bxs)

-- TODO: rewrite in termos of `Applicative`
||| Map each element of a list to a computation whose result type is dependent
||| on the element, evaluate those computations and combine the results.
export
dtraverse' : Monad f
        => {0 a : Type}
        -> {0 g : a -> Type}

        -> ((x : a) -> f (g x))
        -> (xs : List a)
        -> f (DList g xs)

dtraverse' f Nil = pure Nil
dtraverse' f (ax :: axs) = do
  bx <- f ax
  bxs <- dtraverse' f axs

  pure (bx :: bxs)


-- TODO what about dependent accumulator?
||| `foldr` version for dependent lists
export
dfoldr : ({0 x : t} -> elem x -> acc -> acc) -> acc -> DList elem ts -> acc
dfoldr f acc Nil = acc
dfoldr f acc (x :: xs) = f x $ dfoldr f acc xs

||| `foldl` version for dependent lists
export
dfoldl : ({0 x : t} -> acc -> elem x -> acc) -> acc -> DList elem ts -> acc
dfoldl f acc Nil = acc
dfoldl f acc (x :: xs) = dfoldl f (f acc x) xs

||| Apply a function to every element of a dependent list
export
dmap : ({0 x : t} -> a x -> b x) -> DList a xs -> DList b xs
dmap f Nil = Nil
dmap f (ax :: axs) = f ax :: dmap f axs

||| Turn a dependent list into a non-dependent one by applying a
||| dependency-removing function to its elements.
export
undmap : ({0 x : t} -> a x -> b) -> DList a xs -> List b
undmap f Nil = Nil
undmap f (ax :: axs) = f ax :: undmap f axs

-- TODO This is a special case of `replicate'`, rewrite it in terms of it
||| Generate a dependent lists from its parameters
export
replicate : (xs : List t) -> ((x : t) -> f x) -> DList f xs
replicate Nil g = Nil
replicate (x :: xs) g = g x :: replicate xs g

||| Generate a dependent lists from its parameters
export
replicate' : (0 f : a -> b) -> (xs : List a) -> ((x : a) -> g (f x)) -> DList g (map f xs)
replicate' f Nil g = Nil
replicate' f (x :: xs) g = g x :: replicate' f xs g

||| The head of a dependent list
export
head : DList f (x :: xs) -> f x
head (fx :: fxs) = fx

||| The tail of a dependent list
export
tail : DList f (x :: xs) -> DList f xs
tail (fx :: fxs) = fxs

||| split a dependent list in two
export
split : {xs, xs' : List a} -> DList f (xs ++ xs') -> (DList f xs, DList f xs')
split {xs = Nil} dl = (Nil, dl)
split {xs = x :: xs''} (fx :: fxs''') = let (fxs'', fxs') = split (fxs''') in (fx :: fxs'', fxs')

||| Unzip a list with a function that returns a dependent pair
export
dunzipWith : {0 f : b -> Type} -> (a -> (y ** f y)) -> List a -> (ys ** DList f ys)
dunzipWith g Nil = (Nil ** Nil)
dunzipWith g (x :: xs) = let
    (y ** fy) = g x
    (ys ** fys) = dunzipWith g xs
  in (y :: ys ** fy :: fys)

||| Unzip a list of dependent pairs
export
dunzip : {0 f : a -> Type} -> (dpairs : List (x ** f x)) -> (xs ** DList f xs)
dunzip = dunzipWith id

||| Zip a dependent list with its params, according to a zipping function
export
dzipWith : {0 f : b -> Type} -> ((y : b) -> f y -> a) -> (ys ** DList f ys) -> List a
dzipWith g (Nil ** Nil) = Nil
dzipWith g (y :: ys ** fy :: fys) = let
    x = g y fy
    xs = dzipWith g (ys ** fys)
  in (x :: xs)

||| Zip a dependent list with its params
export
dzip : {0 f : b -> Type} -> (ys ** DList f ys) -> List (y ** f y)
dzip dpairs = dzipWith (\y => \fy => (y ** fy)) dpairs
