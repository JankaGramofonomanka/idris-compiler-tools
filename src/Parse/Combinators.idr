module Parse.Combinators

import Control.Monad.State

import Data.List.Lazy

import Parse.Data.Parser
import Parse.Data.Position
import Parse.Data.Tokenize

export
item : Tokenize str tok => Parser str tok
item = do
  s <- get
  (tok, s') <- lift $ tokenize s
  put s'
  pure tok

namespace Pos
  export
  nil : PosParser token (List a)
  nil = do
    p <- currentPosition
    pure (between p p |^ Nil)

  export
  eof : PosParser token ()
  eof = do
    (p, Nil) <- get
              | (p, _ :: _) => empty
    pure (between p p |^ ())

  mutual
    export
    some : PosParser token a -> PosParser token (List $ ^a)
    some p = do
      px |^ x <- p
      pxs |^ xs <- many p
      let pxxs = fromTo px pxs
      pure (pxxs |^ (px |^ x) :: xs)

    export
    many : PosParser token a -> PosParser token (List $ ^a)
    many p = some p <|> nil

  export
  suchThat : PosParser token a -> (a -> Bool) -> PosParser token a
  parser `suchThat` pred = do
    x <- parser
    if pred (^^x) then pure x else empty

  export
  between : PosParser token a -> PosParser token b -> PosParser token c -> PosParser token c
  between left right parser = do
    lp |^ _ <- left
    _ |^ val <- parser
    rp |^ _ <- right
    pure (fromTo lp rp |^ val)

  export
  inheritPos : (^a -> b) -> PosParser token a -> PosParser token b
  inheritPos f p = do
    x <- p
    pure (pos x |^ f x)

  export
  extendPosLeft : Pos -> PosParser token a -> PosParser token a
  extendPosLeft p parser = do
    p' |^ x <- parser
    pure (fromTo p p' |^ x)

  infixr 4 <<^>
  export
  (<<^>) : Pos -> PosParser token a -> PosParser token a
  (<<^>) = extendPosLeft

  infixr 4 <^$>
  export
  (<^$>) : (^a -> b) -> PosParser token a -> PosParser token b
  (<^$>) = inheritPos

  export
  separated : (sep : Parser' token a) -> (item : PosParser token b) -> PosParser token (List (^b))
  separated sep item = nil <|> (:: Nil) <^$> item <|> do
    x <- item
    _ <- sep
    xs <- separated sep item
    pure (fromTo (pos x) (pos xs) |^ x :: ^^xs)


namespace SimplePos
  {-
  export
  item : SimplePosParser Char
  item = do
    (p, s) <- get
    case s of
      Nil => empty
      '\n'  :: xs => put ({ line $= (+1), column := 0     } p, xs) >> pure (between p p |^ '\n')
      x     :: xs => put ({               column $= (+1)  } p, xs) >> pure (between p p |^ x)
  -}

  export
  sat : (Char -> Bool) -> SimplePosParser Char
  sat isOk = do
    x <- item
    if isOk (^^x) then pure x else empty

  export
  theChar : Char -> SimplePosParser Char
  theChar c = sat (== c)

  export
  overwrite : a -> PosParser token b -> PosParser token a
  overwrite x p = map (const x) <$> p

  export
  theString : String -> SimplePosParser String
  theString s = map pack <$> theString' (unpack s) where
    theString' : List Char -> SimplePosParser (List Char)
    theString' Nil = nil
    theString' (c :: cs) = do
      pc |^ c' <- theChar c
      ps |^ cs' <- theString' cs
      pure (fromTo pc ps |^ c' :: cs)


  export
  digit : SimplePosParser Char
  digit = sat isDigit

  export
  digits : SimplePosParser String
  digits = map (pack . map unPos) <$> some digit


  export
  integer : SimplePosParser Integer
  integer = map cast <$> digits

  export
  boolean : SimplePosParser Bool
  boolean = overwrite True (theString "true")
        <|> overwrite False (theString "false")

  export
  plus : SimplePosParser Char
  plus = theChar '+'

  export
  minus : SimplePosParser Char
  minus = theChar '-'

  export
  star : SimplePosParser Char
  star = theChar '*'

  export
  slash : SimplePosParser Char
  slash = theChar '/'

  export
  space : SimplePosParser Char
  space = theChar ' '

  export
  spaces : SimplePosParser ()
  spaces = overwrite () (many spaces)

  export
  nln : SimplePosParser Char
  nln = theChar '\n'

  export
  whitespace : SimplePosParser ()
  whitespace = overwrite () $ many (item `suchThat` isSpace)

  export
  ws : SimplePosParser ()
  ws = whitespace

  export
  leftBracket : SimplePosParser Char
  leftBracket = theChar '('

  export
  rightBracket : SimplePosParser Char
  rightBracket = theChar ')'

  export
  leftCurlyBrace : SimplePosParser Char
  leftCurlyBrace = theChar '{'

  export
  rightCurlyBrace : SimplePosParser Char
  rightCurlyBrace = theChar '}'

  export
  leftSquareBracket : SimplePosParser Char
  leftSquareBracket = theChar '['

  export
  rightSquareBracket : SimplePosParser Char
  rightSquareBracket = theChar ']'

  export
  inBrackets : SimplePosParser a -> SimplePosParser a
  inBrackets = between leftBracket rightBracket

  export
  inCurlyBraces : SimplePosParser a -> SimplePosParser a
  inCurlyBraces = between leftCurlyBrace rightCurlyBrace

  export
  inSquareBrackets : SimplePosParser a -> SimplePosParser a
  inSquareBrackets = between leftSquareBracket rightSquareBracket

  export
  comma : SimplePosParser Char
  comma = theChar ','

  export
  semicolon : SimplePosParser Char
  semicolon = theChar ';'

  export
  floor : SimplePosParser Char
  floor = theChar '_'

  export
  commaSeparated : (item : SimplePosParser b) -> SimplePosParser (List (^b))
  commaSeparated = separated (ws *> comma *> ws)


