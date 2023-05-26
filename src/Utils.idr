module Utils

import Data.List
import Data.List1

public export
deleteAll : Eq a => a -> List a -> List a
deleteAll _ Nil = Nil
deleteAll x (x' :: xs) = if x == x' then deleteAll x xs else x' :: deleteAll x xs



infixr 7 +++
public export
(+++) : List1 a -> List a -> List1 a
(x ::: xs) +++ ys = x ::: xs ++ ys



export
onFirst : (a -> b) -> (a, c) -> (b, c)
onFirst f (x, y) = (f x, y)

export
onSecond : (b -> c) -> (a, b) -> (a, c)
onSecond f (x, y) = (x, f y)


export
curry3 : ((a, b, c) -> d) -> a -> b -> c -> d
curry3 f x y z = f (x, y, z)

export
uncurry3 : (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (x, y, z) = f x y z

export
foldr3 : Foldable t => (e1 -> e2 -> e3 -> acc -> acc) -> acc -> t (e1, e2, e3) -> acc
foldr3 = foldr . uncurry3

export
foldl3 : Foldable t => (acc -> e1 -> e2 -> e3 -> acc) -> acc -> t (e1, e2, e3) -> acc
foldl3 f = foldl (uncurry3 . f)

export
mkSentence : List String -> String
mkSentence = concat . intersperse " "

