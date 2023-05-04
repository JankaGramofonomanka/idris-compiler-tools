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
