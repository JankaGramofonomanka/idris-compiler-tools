module Parse.Data.Position

import Data.Doc

public export
record Position where
  constructor MkPosition
  line : Int
  column : Int

public export
record Pos where
  constructor MkPos
  from, to : Position

export
between : Position -> Position -> Pos
between left right = MkPos { from = left, to = right }

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

export
implementation DocItem Position where
  prt (MkPosition { line, column } ) = concat [show line, ":", show column]

export
implementation DocItem Pos where
  prt (MkPos { from, to }) = concat ["(", prt from, "--", prt to, ")"]
