module Data.Doc

import Data.List
import Data.String

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


export
render : (tabLength : Nat) -> (margin : Nat) -> Doc -> String
render tabLength margin doc = unlines (render' 0 doc) where

  prtComment : Nat -> Maybe String -> String
  prtComment spacesTaken Nothing = ""
  -- TODO: the `;` is LLVM specific, generalize this
  prtComment spacesTaken (Just cmt) = replicate (margin `minus` spacesTaken) ' ' ++ ";" ++ cmt

  mutual
    render' : Nat -> Doc -> List String
    render' numTabs doc' = foldl (\lns => \ln => lns ++ renderLine numTabs ln) [] doc'.lines

    renderLine : Nat -> Either Doc Line -> List String
    
    renderLine numTabs (Right line) = let
        indentLength = numTabs * tabLength
      in singleton . concat $ [ replicate indentLength ' '
                              , line.content
                              , prtComment (indentLength + length line.content) line.comment
                              ]
    
    renderLine numTabs (Left doc') = render' (numTabs + 1) doc'

export
implementation [ticks] (base : DocItem a) => DocItem a where
  prt x = "`" ++ prt x @{base} ++ "`"

