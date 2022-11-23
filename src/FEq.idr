module FEq

public export
interface FEq (0 f : t -> Type) where
  (==) : f a -> f b -> Bool

(/=) : (impl : FEq f) => f a -> f b -> Bool
fa /= fb = not $ (fa == fb) @{impl}

