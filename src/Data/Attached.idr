module Data.Attached

import Data.Some


export
data Attached : (x : t) -> Type -> Type where
  Attach : (0 x : t) -> (y : t') -> Attached x t'

infixr 6 :~:
public export
(:~:) : (x : t) -> Type -> Type
(:~:) = Attached

export
combine : (a -> b -> c) -> Attached x a -> Attached x b -> Attached x c
combine f (Attach x a) (Attach x b) = Attach x (f a b)

export
attach : (0 x : t) -> (y : t') -> Attached x t'
attach = Attach

export
detach : Attached x t -> t
detach (Attach x a) = a

export
reattach : {x : t} -> (y : t) -> Attached x a -> Attached y a
reattach y (Attach x a) = Attach y a

export
implementation Functor (Attached x) where
  map f (Attach x y) = Attach x (f y)

export
implementation Foldable (Attached x) where
  foldr f acc (Attach x elem) = f elem acc

export
implementation Traversable (Attached x) where
  traverse f (Attach x y) = pure (Attach x) <*> (f y)
    


export
distribute : Attached x (List a) -> List (Attached x a)
distribute (Attach x l) = foldr (\elem => (Attach x elem ::)) Nil l

export
detachParam : {f : a -> Type} -> Attached x (y ** f y) -> (y ** Attached x (f y))
detachParam (Attach x (y ** fy)) = (y ** Attach x fy)

export
inSome : Attached x (Some f) -> Some (Attached x . f)
inSome (Attach x (MkSome y)) = MkSome (Attach x y)

export
outOfSome : Some (Attached x . f) -> Attached x (Some f)
outOfSome (MkSome (Attach x y)) = Attach x (MkSome y)