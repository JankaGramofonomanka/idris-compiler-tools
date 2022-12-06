module Utils

public export
deleteAll : Eq a => a -> List a -> List a
deleteAll _ Nil = Nil
deleteAll x (x' :: xs) = if x == x' then deleteAll x xs else x' :: deleteAll x xs







