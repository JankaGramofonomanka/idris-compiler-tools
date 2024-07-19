module Test.Parse.Tokenize

import Tester
import Tester.Runner

import Parse.Data.Position
import Parse.Data.Token
import Parse.Tokenize

||| Unwraps the LHS list from the `Maybe`, drops the positions of its elements
||| and asserts that after such transformation it is equal to RHS.
assertTokEq : (Eq a, Show a) => (lhs : Maybe (List (^a))) -> (rhs : List a) -> TestFunc ()
assertTokEq (Just x) y = assertEq (map unPos x) y
assertTokEq Nothing _ = throw "the result is `Nothing`"

-- Special words vs Identifiers -----------------------------------------------
-- The following group of tests is supposed to prevent a situation where words
-- like `integral` are parsed as two tokens `int` and `egral`, the first being
-- a type and tyhe other an identifier; or words like `int` being parsed as an
-- identifier or as two identifiers `in` and `t`

-- Keywords
returnParses, whileParses, ifParses, elseParses : Test
returnParses
  = test "`return` is parsed as keyword"
  $ assertTokEq (tokenize "return") [Kw Return]
whileParses
  = test "`if` is parsed as keyword"
  $ assertTokEq (tokenize "if") [Kw If]
ifParses
  = test "`else` is parsed as keyword"
  $ assertTokEq (tokenize "else") [Kw Else]
elseParses
  = test "`while` is parsed as keyword"
  $ assertTokEq (tokenize "while") [Kw While]

keywordsParse : List Test
keywordsParse
  = [ returnParses
    , whileParses
    , ifParses
    , elseParses
    ]

-- Types
intParses, booleanParses, stringParses, voidParses : Test
intParses
  = test "`int` is parsed as type"
  $ assertTokEq (tokenize "int") [Ty TokInt]
booleanParses
  = test "`boolean` is parsed as type"
  $ assertTokEq (tokenize "boolean") [Ty TokBool]
stringParses
  = test "`string` is parsed as type"
  $ assertTokEq (tokenize "string") [Ty TokString]
voidParses
  = test "`void` is parsed as type"
  $ assertTokEq (tokenize "void") [Ty TokVoid]

typesParse : List Test
typesParse
  = [ intParses
    , booleanParses
    , stringParses
    , voidParses
    ]

-- Booleans
trueParses, falseParses : Test
trueParses
  = test "`true` is parsed as boolean"
  $ assertTokEq (tokenize "true") [Boo True]
falseParses
  = test "`false` is parsed as boolean"
  $ assertTokEq (tokenize "false") [Boo False]

booleansParse : List Test
booleansParse
  = [ trueParses
    , falseParses
    ]

-- Identifiers
keywordPrefix, typePrefix, booleanPrefix : Test
keywordPrefix
  = test "`iff` is parsed as an identifier"
  $ assertTokEq (tokenize "iff") [Id "iff"]
typePrefix
  = test "`integral` is parsed as an identifier"
  $ assertTokEq (tokenize "integral") [Id "integral"]
booleanPrefix
  = test "`trueAnswer` is parsed as an identifier"
  $ assertTokEq (tokenize "trueAnswer") [Id "trueAnswer"]

identsParse : List Test
identsParse
  = [ keywordPrefix
    , typePrefix
    , booleanPrefix
    ]

tests : List Test
tests
   = keywordsParse
  ++ typesParse
  ++ booleansParse
  ++ identsParse

export
main : IO ()
main = do
  putStrLn "Testing `Parse.Tokenize`"
  success <- runTests tests
  pure ()
