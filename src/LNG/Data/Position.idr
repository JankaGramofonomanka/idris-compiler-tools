module LNG.Data.Position

public export
record Position where
  constructor MkPosition
  line : Int
  column : Int

public export
data Pos

  = Between Position Position
  
  -- used, when the AST tree is artificially constructed in the code, eg. in tests.
  | Fake Int

prefix 10 ^
infix 1 |^
public export
data (^) : Type -> Type where
  (|^) : Pos -> a -> ^ a

export
pos : ^a -> Pos
pos (p |^ x) = p

export
unPos : ^a -> a
unPos (p |^ x) = x

prefix 10 ^^
export
(^^) : ^a -> a
(^^) = unPos

public export
data PosList a = Nil Pos | (::) (^a) (PosList a)

export
length : PosList a -> Nat
length (Nil _) = 0
length (x :: xs) = 1 + length xs

export
headOrNilpos : PosList a -> Pos
headOrNilpos (Nil p) = p
headOrNilpos (x :: xs) = pos x

export
implementation Functor PosList where
  map f (Nil p) = Nil p
  map f ((p |^ x) :: xs) = (p |^ f x) :: map f xs

export
implementation Foldable PosList where
  foldr f acc (Nil p) = acc
  foldr f acc (x :: xs) = f (^^x) (foldr f acc xs)

export
implementation Traversable PosList where
  traverse g (Nil p) = pure (Nil p)
  traverse g ((p |^ x) :: xs) = (::) <$> ((p |^) <$> g x) <*> traverse g xs

export
posTraverse : Applicative f => (^a -> f (^b)) -> PosList a -> f (PosList b)
posTraverse g (Nil p) = pure (Nil p)
posTraverse g (x :: xs) = (::) <$> g x <*> posTraverse g xs

export
unPosList : PosList a -> List a
unPosList l = foldr (::) Nil l

