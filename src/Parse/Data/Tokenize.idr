module Parse.Data.Tokenize

import Data.List

import Parse.Data.Parser
import Parse.Data.Position

public export
interface Tokenize str tok where
  tokenize : Alternative f => str -> f (tok, str)

export
implementation Tokenize (List a) a where
  tokenize Nil = empty
  tokenize (ch :: chs) = pure (ch, chs)

export
implementation Tokenize (Position, List Char) (^Char) where
  tokenize (p, s) = case s of
    Nil => empty
    '\n'  :: xs => pure ((between p (moveRight' p) |^ '\n'),  (nextLine    p, xs))
    x     :: xs => pure ((between p (moveRight' p) |^ x),     (moveRight'  p, xs))

export
implementation Tokenize (Position, List (^a)) (^a) where
  tokenize (p, s) = case s of
    Nil => empty
    x :: xs => pure (x, (maybe (pos x).to (from . pos) (head' xs), xs))

