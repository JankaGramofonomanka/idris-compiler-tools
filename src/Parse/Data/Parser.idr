module Parse.Data.Parser

import Control.Monad.State

import Parse.Data.Position

public export
Parser : Type -> Type -> Type
Parser token a = StateT (Position, List token) List a

public export
SimpleParser : Type -> Type
SimpleParser a = Parser Char a

public export
PosParser : Type -> Type -> Type
PosParser token a = Parser token (^a)

public export
SimplePosParser : Type -> Type
SimplePosParser a = PosParser Char a


export
beginning : Pos -> Position
beginning (Between l r) = l
beginning (Fake _) = assert_total $ idris_crash "fake `Pos`"

export
end : Pos -> Position
end (Between l r) = r
end (Fake _) = assert_total $ idris_crash "fake `Pos`"

export
fromTo : Pos -> Pos -> Pos
fromTo p1 p2 = Between (beginning p1) (end p2)

export
currentPosition : Parser token Position
currentPosition = gets fst



export
parse : Parser token a -> List token -> Maybe a
parse parser tokens = case evalStateT (MkPosition { line = 0, column = 0 }, tokens) parser of
  Nil => Nothing
  (x :: _) => Just x

export
simpleParse : SimpleParser a -> String -> Maybe a
simpleParse parser s = parse parser (unpack s)
