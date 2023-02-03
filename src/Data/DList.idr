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
        => {t : Type}
        -> {a, b : t -> Type}
        -> {0 xs : List t}
        
        -> ({0 x : t} -> a x -> f (b x))
        -> DList a xs
        -> f (DList b xs)

dtraverse f Nil = pure Nil
dtraverse f (ax :: axs) = do
  bx <- f ax
  bxs <- dtraverse f axs
  
  pure (bx :: bxs)



export
dmap : ({0 x : t} -> a x -> b x) -> DList a xs -> DList b xs
dmap f Nil = Nil
dmap f (ax :: axs) = f ax :: dmap f axs
