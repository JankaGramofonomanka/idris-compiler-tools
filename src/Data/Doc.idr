module Data.Doc

import Data.List

public export
record Line where
  constructor MkLine
  content : String
  comment : Maybe String

export
simple : String -> Line
simple s = MkLine { content = s, comment = Nothing }

export
blankLine : Line
blankLine = simple ""

public export
record Doc where
  constructor MkDoc
  lines : List (Either Doc Line)

export
empty : Doc
empty = MkDoc { lines = [] }

export
fromLines : List Line -> Doc
fromLines lines = MkDoc { lines = map Right lines }

export
blankLines : Nat -> Doc
blankLines n = fromLines (replicate n blankLine)

export
(++) : Doc -> Doc -> Doc
MkDoc { lines } ++ MkDoc { lines = lines' } = MkDoc { lines = lines ++ lines' }

public export
interface Document a where
  print : a -> Doc

public export
interface DocItem a where
  prt : a -> String


