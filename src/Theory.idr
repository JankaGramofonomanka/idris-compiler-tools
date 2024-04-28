||| A module with theorems about general-purpose data types
module Theory

import Data.List
import Data.List1

||| Equality is symmetric
total
export
revEq : a = b -> b = a
revEq Refl = Refl

||| From falsehood, anything follows
||| a.k.a the principle of explosion
total
export
exfalso : Void -> a
exfalso v = case v of {}

namespace List
  ||| Concatenation of lists os associative
  total
  export
  concat_assoc : (l, l', l'' : List a) -> l ++ (l' ++ l'') = (l ++ l') ++ l''
  concat_assoc Nil l' l'' = Refl
  concat_assoc (x :: xs) l' l'' = rewrite revEq $ concat_assoc {l = xs, l', l''} in Refl

  ||| Concatenating a list with an emoty list results in the same list
  total
  export
  concat_nil : (l : List a) -> l ++ Nil = l
  concat_nil Nil = Refl
  concat_nil (x :: xs) = rewrite concat_nil xs in Refl


  ||| The mapping of a function on a concatenation of two lists
  ||| is the concatenation of mappings of that function on those lists
  total
  export
  map_concat : {f : a -> b}
            -> (l, l' : List a)
            -> map f (l ++ l') = map f l ++ map f l'
  map_concat {f} Nil l = Refl
  map_concat {f} (x :: xs) l = rewrite revEq $ map_concat {f} xs l in Refl


  ||| `map_concat` in the case when the right operand is a singleton
  total
  export
  map_append : {f : a -> b}
            -> (l : List a)
            -> (x : a)
            -> map f (l ++ [x]) = map f l ++ [f x]
  map_append l x = map_concat l [x]

  ||| The concatenation of a non-empty list with another list is non-empty
  total
  export
  nonempty_plusplus' : (xs, ys : List a) -> NonEmpty xs -> NonEmpty (xs ++ ys)
  nonempty_plusplus' Nil        ys        IsNonEmpty impossible
  nonempty_plusplus' (x :: xs)  Nil       IsNonEmpty = IsNonEmpty
  nonempty_plusplus' (x :: xs)  (y :: ys) IsNonEmpty = IsNonEmpty

  ||| The concatenation of a non-empty list with another list is non-empty
  total
  export
  nonempty_plusplus : {xs, ys : List a} -> NonEmpty xs -> NonEmpty (xs ++ ys)
  nonempty_plusplus {xs, ys} = nonempty_plusplus' xs ys

  ||| The concatenation of a list with a non-empty list is non-empty
  total
  export
  plusplus_nonempty' : (xs, ys : List a) -> NonEmpty ys -> NonEmpty (xs ++ ys)
  plusplus_nonempty' xs         Nil       IsNonEmpty impossible
  plusplus_nonempty' Nil        (y :: ys) IsNonEmpty = IsNonEmpty
  plusplus_nonempty' (x :: xs)  (y :: ys) IsNonEmpty = IsNonEmpty

  ||| The concatenation of a list with a non-empty list is non-empty
  total
  export
  plusplus_nonempty : {xs, ys : List a} -> NonEmpty ys -> NonEmpty (xs ++ ys)
  plusplus_nonempty {xs, ys} = plusplus_nonempty' xs ys

  ||| If   the concatenation of one list  with another is non-empty,
  ||| then the concatenation of the other with the one is non-empty
  total
  export
  nonempty_flip_concat' : (xs, ys : List a) -> NonEmpty (xs ++ ys) -> NonEmpty (ys ++ xs)
  nonempty_flip_concat' Nil        Nil       IsNonEmpty impossible
  nonempty_flip_concat' Nil        (y :: ys) IsNonEmpty = IsNonEmpty
  nonempty_flip_concat' (x :: xs)  Nil       IsNonEmpty = IsNonEmpty
  nonempty_flip_concat' (x :: xs)  (y :: ys) IsNonEmpty = IsNonEmpty

  ||| If   the concatenation of one list  with another is non-empty,
  ||| then the concatenation of the other with the one is non-empty
  total
  export
  nonempty_flip_concat : {xs, ys : List a} -> NonEmpty (xs ++ ys) -> NonEmpty (ys ++ xs)
  nonempty_flip_concat {xs, ys} = nonempty_flip_concat' xs ys

  ||| If a list is non-empty, then any mapping on that list is also non-empty
  total
  export
  nonempty_map' : (xs : List a) -> (f : a -> b) -> NonEmpty xs -> NonEmpty (map f xs)
  nonempty_map' Nil       f IsNonEmpty impossible
  nonempty_map' (x :: xs) f IsNonEmpty = IsNonEmpty

  ||| If a list is non-empty, then any mapping on that list is also non-empty
  total
  export
  nonempty_map : {xs : List a} -> {f : a -> b} -> NonEmpty xs -> NonEmpty (map f xs)
  nonempty_map {xs} {f} = nonempty_map' xs f

  ||| If the concatenation of two lists is non-empty, then one of the two lists is non-empty
  total
  export
  nonempty_concat' : (xs, ys : List a) -> NonEmpty (xs ++ ys) -> Either (NonEmpty xs) (NonEmpty ys)
  nonempty_concat' Nil        Nil       IsNonEmpty impossible
  nonempty_concat' Nil        (y :: ys) IsNonEmpty = Right IsNonEmpty
  nonempty_concat' (x :: xs)  ys        IsNonEmpty = Left IsNonEmpty

  ||| If the concatenation of two lists is non-empty,
  ||| then one of the two lists is non-empty
  total
  export
  nonempty_concat : {xs, ys : List a} -> NonEmpty (xs ++ ys) -> Either (NonEmpty xs) (NonEmpty ys)
  nonempty_concat {xs, ys} = nonempty_concat' xs ys

  ||| If   the concatenation of two               lists is non-empty,
  ||| then the concatenation of mappings on those lists is non-empty
  total
  export
  nonempty_cmap_cmap' : (xs, ys : List a)
                    -> (f, g : a -> b)
                    -> NonEmpty (xs ++ ys)
                    -> NonEmpty (map f xs ++ map g ys)
  nonempty_cmap_cmap' Nil       Nil       f g IsNonEmpty impossible
  nonempty_cmap_cmap' Nil       (y :: ys) f g IsNonEmpty = IsNonEmpty
  nonempty_cmap_cmap' (x :: xs) ys        f g IsNonEmpty = IsNonEmpty

  ||| If   the concatenation of two               lists is non-empty,
  ||| then the concatenation of mappings on those lists is non-empty
  total
  export
  nonempty_cmap_cmap : {xs, ys : List a}
                    -> {f, g : a -> b}
                    -> NonEmpty (xs ++ ys)
                    -> NonEmpty (map f xs ++ map g ys)
  nonempty_cmap_cmap {xs, ys, f, g} = nonempty_cmap_cmap' xs ys f g



namespace List1

  ||| Concatenation of non-empty lists os associative
  total
  export
  concat_assoc : (l, l', l'' : List1 a) -> l ++ (l' ++ l'') = (l ++ l') ++ l''
  concat_assoc (x ::: xs) (y ::: ys) (z ::: zs)
    = rewrite List.concat_assoc xs (y :: ys) (z :: zs)
      in Refl

  ||| The mapping of a function on a concatenation of two non-empty lists
  ||| is the concatenation of mappings of that function on those lists
  total
  export
  map_concat : {f : a -> b}
            -> (l, l' : List1 a)
            -> map f (l ++ l') = map f l ++ map f l'
  map_concat {f} (x ::: xs) (y ::: ys)
    = rewrite List.map_concat {f} xs (y :: ys)
      in Refl


  ||| `map_concat` in the case when the right operand is a singleton
  total
  export
  map_append : {f : a -> b}
            -> (l : List1 a)
            -> (x : a)
            -> map f (l ++ (x ::: Nil)) = map f l ++ (f x ::: Nil)
  map_append l x = map_concat l (x ::: Nil)



namespace Tuple

  ||| A tuple consists of its first and second element
  total
  export
  tuple_destruct : (t : (a, b)) -> t = (fst t, snd t)
  tuple_destruct (x, y) = Refl
