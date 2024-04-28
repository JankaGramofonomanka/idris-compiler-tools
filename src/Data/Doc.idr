||| A moduile defining data types and functionality for pretty printing
module Data.Doc

import Data.List
import Data.String

||| A line in a document
public export
record Line where
  constructor MkLine
  ||| The content of the line
  content : String
  ||| A comment next to the line
  comment : Maybe String

||| A simple, comment-free line
export
simple : String -> Line
simple s = MkLine { content = s, comment = Nothing }

||| An empty line
export
blankLine : Line
blankLine = simple ""

||| A document
|||
||| The document consists of lines or sub-documents
||| The purpose of the sub-documents is convenient indentation
public export
record Doc where
  constructor MkDoc
  ||| The content of the document, either a line or a sub-document
  lines : List (Either Doc Line)

||| An empty document
export
empty : Doc
empty = MkDoc { lines = [] }

||| Make a document form a list of lines
export
fromLines : List Line -> Doc
fromLines lines = MkDoc { lines = map Right lines }

||| Make a document by repeating a number of empty lines
export
blankLines : Nat -> Doc
blankLines n = fromLines (replicate n blankLine)

||| Concatenate two documents
export
(++) : Doc -> Doc -> Doc
MkDoc { lines } ++ MkDoc { lines = lines' } = MkDoc { lines = lines ++ lines' }

||| Things that can be rendered into a document
public export
interface Document a where
  print : a -> Doc

||| Things that can be rendered into a pretty string
public export
interface DocItem a where
  prt : a -> String

||| Render a document
||| @ tablLength the length of a single indent
||| @ margin     the width after which comments will appear
||| @ doc        the docmuent to be rendered
|||
||| Starts rendering with indentation 0 and increases the indentation depth for
||| sub-documents
export
render : (tabLength : Nat) -> (margin : Nat) -> (doc : Doc) -> String
render tabLength margin doc = unlines (render' 0 doc) where

  prtComment : Nat -> Maybe String -> String
  prtComment spacesTaken Nothing = ""
  -- TODO: the `;` is LLVM specific, generalize this
  prtComment spacesTaken (Just cmt) = replicate (margin `minus` spacesTaken) ' ' ++ ";" ++ cmt

  mutual
    ||| Render a document with a specified indentation depth
    ||| @ numTabs the number if indents
    ||| @ doc     the rendered document
    render' : (numTabs : Nat) -> (doc : Doc) -> List String
    render' numTabs doc' = foldl (\lns => \ln => lns ++ renderLine numTabs ln) [] doc'.lines

    ||| Render a line or a sub-document
    renderLine : Nat -> Either Doc Line -> List String

    -- Prepend indentation white-space to the comment and append the optional comment
    renderLine numTabs (Right line) = let
        indentLength = numTabs * tabLength
      in singleton . concat $ [ replicate indentLength ' '
                              , line.content
                              , prtComment (indentLength + length line.content) line.comment
                              ]

    -- Render the sub-document with increased indentation depth
    renderLine numTabs (Left doc') = render' (numTabs + 1) doc'

||| Implementation of `DocItem` that wraps the rendered items in ticks (`)
export
implementation [ticks] (base : DocItem a) => DocItem a where
  prt x = "`" ++ prt x @{base} ++ "`"
