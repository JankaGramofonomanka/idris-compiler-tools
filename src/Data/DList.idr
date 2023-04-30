module Data.DList


public export
data DList : (a -> Type) -> List a -> Type where
  Nil : DList f Nil
  (::) : {0 x : a} -> f x -> DList f xs -> DList f (x :: xs)

public export
(++) : DList f xs -> DList f ys -> DList f (xs ++ ys)
Nil         ++ fys = fys
(fx :: fxs) ++ fys = fx :: fxs ++ fys


-- TODO: rewrite in termos of `Applicative`
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

-- TODO what about dependent accumulator?
export
dfoldr : ({0 x : t} -> elem x -> acc -> acc) -> acc -> DList elem ts -> acc
dfoldr f acc Nil = acc
dfoldr f acc (x :: xs) = f x $ dfoldr f acc xs

export
dfoldl : ({0 x : t} -> acc -> elem x -> acc) -> acc -> DList elem ts -> acc
dfoldl f acc Nil = acc
dfoldl f acc (x :: xs) = dfoldl f (f acc x) xs

export
dmap : ({0 x : t} -> a x -> b x) -> DList a xs -> DList b xs
dmap f Nil = Nil
dmap f (ax :: axs) = f ax :: dmap f axs

export
replicate : (xs : List t) -> ((x : t) -> f x) -> DList f xs
replicate Nil g = Nil
replicate (x :: xs) g = g x :: replicate xs g

export
replicate' : (0 f : a -> b) -> (xs : List a) -> ((x : a) -> g (f x)) -> DList g (map f xs)
replicate' f Nil g = Nil
replicate' f (x :: xs) g = g x :: replicate' f xs g

export
head : DList f (x :: xs) -> f x
head (fx :: fxs) = fx

export
tail : DList f (x :: xs) -> DList f xs
tail (fx :: fxs) = fxs

export
split : {xs, xs' : List a} -> DList f (xs ++ xs') -> (DList f xs, DList f xs')
split {xs = Nil} dl = (Nil, dl)
split {xs = x :: xs''} (fx :: fxs''') = let (fxs'', fxs') = split (fxs''') in (fx :: fxs'', fxs')
