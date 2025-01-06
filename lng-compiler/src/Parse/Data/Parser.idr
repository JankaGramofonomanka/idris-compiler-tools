module Parse.Data.Parser

import Control.Monad.State

import Parse.Data.Position
import Data.List.Lazy

public export
Parser : Type -> Type -> Type
Parser str a = StateT str LazyList a

public export
Parser' : Type -> Type -> Type
Parser' token a = Parser (Position, List token) a

public export
SimpleParser : Type -> Type
SimpleParser a = Parser' Char a

public export
PosParser : Type -> Type -> Type
PosParser token a = Parser' token (^a)

public export
SimplePosParser : Type -> Type
SimplePosParser a = PosParser Char a


export
fromTo : Pos -> Pos -> Pos
fromTo p1 p2 = between p1.from p2.to

export
currentPosition : Parser' token Position
currentPosition = gets fst

export
parse : Parser str a -> str -> Maybe a
parse parser s = case evalStateT s parser of
  Nil => Nothing
  (x :: _) => Just x

export
parse' : Parser' token a -> List token -> Maybe a
parse' parser tokens = parse parser (MkPosition { line = 1, column = 1 }, tokens)

export
simpleParse : SimpleParser a -> String -> Maybe a
simpleParse parser s = parse' parser (unpack s)

export
posParse : PosParser token a -> List token -> Maybe a
posParse parser tokens = (^^) <$> parse parser (MkPosition { line = 1, column = 1 }, tokens)

export
simplePosParse : SimplePosParser a -> String -> Maybe a
simplePosParse parser s = posParse parser (unpack s)
