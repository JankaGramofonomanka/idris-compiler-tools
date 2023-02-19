module Utils

import Data.List
import Data.List1

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
nonempty_plusplus' : (xs, ys : List a) -> NonEmpty xs -> NonEmpty (xs ++ ys)
nonempty_plusplus' Nil        ys        IsNonEmpty impossible
nonempty_plusplus' (x :: xs)  Nil       IsNonEmpty = IsNonEmpty
nonempty_plusplus' (x :: xs)  (y :: ys) IsNonEmpty = IsNonEmpty

total
export
nonempty_plusplus : {xs, ys : List a} -> NonEmpty xs -> NonEmpty (xs ++ ys)
nonempty_plusplus {xs, ys} = nonempty_plusplus' xs ys

total
export
plusplus_nonempty' : (xs, ys : List a) -> NonEmpty ys -> NonEmpty (xs ++ ys)
plusplus_nonempty' xs         Nil       IsNonEmpty impossible
plusplus_nonempty' Nil        (y :: ys) IsNonEmpty = IsNonEmpty
plusplus_nonempty' (x :: xs)  (y :: ys) IsNonEmpty = IsNonEmpty

total
export
plusplus_nonempty : {xs, ys : List a} -> NonEmpty ys -> NonEmpty (xs ++ ys)
plusplus_nonempty {xs, ys} = plusplus_nonempty' xs ys

total
export
nonempty_flip_concat' : (xs, ys : List a) -> NonEmpty (xs ++ ys) -> NonEmpty (ys ++ xs)
nonempty_flip_concat' Nil        Nil       IsNonEmpty impossible
nonempty_flip_concat' Nil        (y :: ys) IsNonEmpty = IsNonEmpty
nonempty_flip_concat' (x :: xs)  Nil       IsNonEmpty = IsNonEmpty
nonempty_flip_concat' (x :: xs)  (y :: ys) IsNonEmpty = IsNonEmpty

total
export
nonempty_flip_concat : {xs, ys : List a} -> NonEmpty (xs ++ ys) -> NonEmpty (ys ++ xs)
nonempty_flip_concat {xs, ys} = nonempty_flip_concat' xs ys

total
export
nonempty_map' : (xs : List a) -> (f : a -> b) -> NonEmpty xs -> NonEmpty (map f xs)
nonempty_map' Nil       f IsNonEmpty impossible
nonempty_map' (x :: xs) f IsNonEmpty = IsNonEmpty

total
export
nonempty_map : {xs : List a} -> {f : a -> b} -> NonEmpty xs -> NonEmpty (map f xs)
nonempty_map {xs} {f} = nonempty_map' xs f

total
export
nonempty_concat' : (xs, ys : List a) -> NonEmpty (xs ++ ys) -> Either (NonEmpty xs) (NonEmpty ys)
nonempty_concat' Nil        Nil       IsNonEmpty impossible
nonempty_concat' Nil        (y :: ys) IsNonEmpty = Right IsNonEmpty
nonempty_concat' (x :: xs)  ys        IsNonEmpty = Left IsNonEmpty

total
export
nonempty_concat : {xs, ys : List a} -> NonEmpty (xs ++ ys) -> Either (NonEmpty xs) (NonEmpty ys)
nonempty_concat {xs, ys} = nonempty_concat' xs ys

total
export
nonempty_cmap_cmap' : (xs, ys : List a)
                   -> (f, g : a -> b)
                   -> NonEmpty (xs ++ ys)
                   -> NonEmpty (map f xs ++ map g ys)
nonempty_cmap_cmap' Nil       Nil       f g IsNonEmpty impossible
nonempty_cmap_cmap' Nil       (y :: ys) f g IsNonEmpty = IsNonEmpty
nonempty_cmap_cmap' (x :: xs) ys        f g IsNonEmpty = IsNonEmpty

total
export
nonempty_cmap_cmap : {xs, ys : List a}
                  -> {f, g : a -> b}
                  -> NonEmpty (xs ++ ys)
                  -> NonEmpty (map f xs ++ map g ys)
nonempty_cmap_cmap {xs, ys, f, g} = nonempty_cmap_cmap' xs ys f g

infixr 7 +++
public export
(+++) : List1 a -> List a -> List1 a
(x ::: xs) +++ ys = x ::: xs ++ ys



