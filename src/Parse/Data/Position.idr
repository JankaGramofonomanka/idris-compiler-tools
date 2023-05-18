module Parse.Data.Position

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

export
implementation Functor (^) where
  map f (p |^ x) = (p |^ f x)
