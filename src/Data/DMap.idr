module Data.DMap

export
DMap : (k : a -> Type) -> (f : a -> Type) -> Type

export
insert : {0 t : a} -> k t -> f t -> DMap k f -> DMap k f

export
lookup : {0 t : a} -> k t -> DMap k f -> Maybe (f t)

export
empty : DMap k f

export
toList : DMap k f -> List (x : t ** (k x, f x))

export
fromList : List (x : t ** (k x, f x)) -> DMap k f
fromList l = foldl (\acc => \(x ** (k, v)) => insert k v acc) DMap.empty l

export
merge : DMap k f -> DMap k f -> DMap k f
merge m m' = fromList (DMap.toList m ++ DMap.toList m')

