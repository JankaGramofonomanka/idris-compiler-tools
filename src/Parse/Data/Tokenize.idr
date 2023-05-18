module Parse.Data.Tokenize

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
    '\n'  :: xs => pure ((Between p p |^ '\n'), ({ line $= (+1), column := 0     } p, xs))
    x     :: xs => pure ((Between p p |^ x), ({               column $= (+1)  } p, xs))

export
implementation Tokenize (Position, List (^a)) (^a) where
  tokenize (p, s) = case s of
    Nil => empty
    x :: xs => pure (x, (end (pos x), xs))

