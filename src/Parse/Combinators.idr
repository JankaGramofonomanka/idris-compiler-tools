module Parse.Combinators

import Control.Monad.State

import Parse.Data.Parser
import Parse.Data.Position


beginning : Pos -> Position
beginning (Between l r) = l
beginning (Fake _) = assert_total $ idris_crash "fake `Pos`"

end : Pos -> Position
end (Between l r) = r
end (Fake _) = assert_total $ idris_crash "fake `Pos`"

export
fromTo : Pos -> Pos -> Pos
fromTo p1 p2 = Between (beginning p1) (end p2)

public export
SimpleParser : Type -> Type
SimpleParser a = Parser Char a

public export
PosParser : Type -> Type
PosParser a = SimpleParser (^a)

export
currentPosition : SimpleParser Position
currentPosition = gets fst

export
nil : PosParser (List a)
nil = do
  p <- currentPosition
  pure (Between p p |^ Nil)

export
eof : PosParser ()
eof = do
  (p, Nil) <- get
            | (p, _ :: _) => empty
  pure (Between p p |^ ())

mutual
  export
  some : PosParser a -> PosParser (List $ ^a)
  some p = do
    px |^ x <- p
    pxs |^ xs <- many p
    let pxxs = fromTo px pxs
    pure (pxxs |^ (px |^ x) :: xs)

  export
  many : PosParser a -> PosParser (List $ ^a)
  many p = nil <|> some p

export
item : PosParser Char
item = do
  (p, s) <- get
  case s of
    Nil => empty
    '\n'  :: xs => put ({ line $= (+1), column := 0     } p, xs) >> pure (Between p p |^ '\n')
    x     :: xs => put ({               column $= (+1)  } p, xs) >> pure (Between p p |^ x)

export
sat : (Char -> Bool) -> PosParser Char
sat isOk = do
  x <- item
  if isOk (^^x) then pure x else empty

export
suchThat : PosParser a -> (a -> Bool) -> PosParser a
parser `suchThat` pred = do
  x <- parser
  if pred (^^x) then pure x else empty

export
theChar : Char -> PosParser Char
theChar c = sat (== c)

export
overwrite : a -> PosParser b -> PosParser a
overwrite x p = map (const x) <$> p

export
theString : String -> PosParser String
theString s = map pack <$> theString' (unpack s) where
  theString' : List Char -> PosParser (List Char)
  theString' Nil = nil
  theString' (c :: cs) = do
    pc |^ c' <- theChar c
    ps |^ cs' <- theString' cs
    pure (fromTo pc ps |^ c' :: cs)


export
digit : PosParser Char
digit = sat isDigit

export
digits : PosParser String
digits = map (pack . map unPos) <$> some digit


export
integer : PosParser Integer
integer = map cast <$> digits

export
boolean : PosParser Bool
boolean = overwrite True (theString "true")
      <|> overwrite False (theString "false")

export
plus : PosParser Char
plus = theChar '+'

export
minus : PosParser Char
minus = theChar '-'

export
star : PosParser Char
star = theChar '*'

export
slash : PosParser Char
slash = theChar '/'

export
space : PosParser Char
space = theChar ' '

export
spaces : PosParser ()
spaces = overwrite () (many spaces)

export
nln : PosParser Char
nln = theChar '\n'

export
whitespace : PosParser ()
whitespace = overwrite () $ many (space <|> nln)

export
ws : PosParser ()
ws = whitespace

export
leftBracket : PosParser Char
leftBracket = theChar '('

export
rightBracket : PosParser Char
rightBracket = theChar ')'

export
leftCurlyBrace : PosParser Char
leftCurlyBrace = theChar '{'

export
rightCurlyBrace : PosParser Char
rightCurlyBrace = theChar '}'

export
leftSquareBracket : PosParser Char
leftSquareBracket = theChar '['

export
rightSquareBracket : PosParser Char
rightSquareBracket = theChar ']'

export
between : PosParser a -> PosParser b -> PosParser c -> PosParser c
between left right parser = do
  lp |^ _ <- left
  _ |^ val <- parser
  rp |^ _ <- right
  pure (fromTo lp rp |^ val)

export
inBrackets : PosParser a -> PosParser a
inBrackets = between leftBracket rightBracket

export
inCurlyBraces : PosParser a -> PosParser a
inCurlyBraces = between leftCurlyBrace rightCurlyBrace

export
inSquareBrackets : PosParser a -> PosParser a
inSquareBrackets = between leftSquareBracket rightSquareBracket

export
colon : PosParser Char
colon = theChar ','

export
semicolon : PosParser Char
semicolon = theChar ';'

export
floor : PosParser Char
floor = theChar '_'

export
inheritPos : (^a -> b) -> PosParser a -> PosParser b
inheritPos f p = do
  x <- p
  pure (pos x |^ f x)

infixr 4 <^$>
export
(<^$>) : (^a -> b) -> PosParser a -> PosParser b
(<^$>) = inheritPos

export
separated : (sep : SimpleParser a) -> (item : PosParser b) -> PosParser (List (^b))
separated sep item = nil <|> (:: Nil) <^$> item <|> do
  x <- item
  _ <- ws *> sep
  xs <- separated sep item
  pure (fromTo (pos x) (pos xs) |^ x :: ^^xs)

export
colonSeparated : (item : PosParser b) -> PosParser (List (^b))
colonSeparated = separated colon

export
parse : SimpleParser a -> String -> Maybe a
parse parser s = case evalStateT (MkPosition { line = 0, column = 0 }, unpack s) parser of
  Nil => Nothing
  (x :: _) => Just x
