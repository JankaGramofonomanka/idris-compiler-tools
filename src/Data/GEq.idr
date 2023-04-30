module Data.GEq

public export
toBool : Maybe thm -> Bool
toBool (Just _) = True
toBool Nothing = False

public export
interface GEq (0 f : t -> Type) where
  geq : f a -> f b -> Maybe (a = b)


export
geq', (==) : (impl : GEq f) => f a -> f b -> Bool
geq' fa fb = toBool (geq fa fb @{impl})
(==) = geq' @{impl}

export
ngeq', (/=) : (impl : GEq f) => f a -> f b -> Bool
ngeq' fa fb = not (geq' fa fb @{impl})
(/=) = ngeq' @{impl}

