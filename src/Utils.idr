module Utils

public export
deleteAll : Eq a => a -> List a -> List a
deleteAll _ Nil = Nil
deleteAll x (x' :: xs) = if x == x' then deleteAll x xs else x' :: deleteAll x xs



total
export
revEq : a = b -> b = a
revEq Refl = Refl


total
export
concat_assoc : (l, l', l'' : List a) -> l ++ (l' ++ l'') = (l ++ l') ++ l''
concat_assoc Nil l' l'' = Refl
concat_assoc (x :: xs) l' l'' = rewrite revEq $ concat_assoc {l = xs, l', l''} in Refl

total
export
concat_nil : (l : List a) -> l ++ Nil = l
concat_nil Nil = Refl
concat_nil (x :: xs) = rewrite concat_nil xs in Refl


total
export
map_concat : {f : a -> b}
          -> (l, l' : List a)
          -> map f (l ++ l') = map f l ++ map f l'
map_concat {f} Nil l = Refl
map_concat {f} (x :: xs) l = rewrite revEq $ map_concat {f} xs l in Refl


total
export
map_append : {f : a -> b}
          -> (l : List a)
          -> (x : a)
          -> map f (l ++ [x]) = map f l ++ [f x]
map_append l x = map_concat l [x]

total
export
tuple_destruct : (t : (a, b)) -> t = (fst t, snd t)
tuple_destruct (x, y) = Refl

