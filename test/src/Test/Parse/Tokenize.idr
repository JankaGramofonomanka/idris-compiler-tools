module Test.Parse.Tokenize

import Tester
import Tester.Runner

import Parse.Data.Position
import Parse.Data.Token
import Parse.Tokenize

||| Tokenizes the input and asserts the given property while ignorinng the
||| positions of the tokens
assertTokenizeResult : (input : String) -> (prop : List Token -> Bool) -> TestFunc ()
assertTokenizeResult input prop = case tokenize input of
  Nothing => throw "the input does not parse"
  Just actual => assert (prop $ map unPos actual)

assertTokenizeResultEq : (input : String) -> (expected : List Token) -> TestFunc ()
assertTokenizeResultEq input expected
  = assertTokenizeResult input (== expected)

||| The following group of tests is supposed to prevent a situation where words
||| like `integral` are parsed as two tokens `int` and `egral`, the first being
||| a type and tyhe other an identifier; or words like `int` being parsed as an
||| identifier or as two identifiers `in` and `t`
namespace IdentsVSSpecialWords

  -- Keywords
  returnParses, whileParses, ifParses, elseParses : Test
  returnParses
    = test "`return` is parsed as keyword"
    $ assertTokenizeResultEq "return" [Kw Return]
  whileParses
    = test "`if` is parsed as keyword"
    $ assertTokenizeResultEq "if" [Kw If]
  ifParses
    = test "`else` is parsed as keyword"
    $ assertTokenizeResultEq "else" [Kw Else]
  elseParses
    = test "`while` is parsed as keyword"
    $ assertTokenizeResultEq "while" [Kw While]

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
    $ assertTokenizeResultEq "int" [Ty TokInt]
  booleanParses
    = test "`boolean` is parsed as type"
    $ assertTokenizeResultEq "boolean" [Ty TokBool]
  stringParses
    = test "`string` is parsed as type"
    $ assertTokenizeResultEq "string" [Ty TokString]
  voidParses
    = test "`void` is parsed as type"
    $ assertTokenizeResultEq "void" [Ty TokVoid]

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
    $ assertTokenizeResultEq "true" [Boo True]
  falseParses
    = test "`false` is parsed as boolean"
    $ assertTokenizeResultEq "false" [Boo False]

  booleansParse : List Test
  booleansParse
    = [ trueParses
      , falseParses
      ]

  -- Identifiers
  keywordPrefix, typePrefix, booleanPrefix : Test
  keywordPrefix
    = test "`iff` is parsed as an identifier"
    $ assertTokenizeResultEq "iff" [Id "iff"]
  typePrefix
    = test "`integral` is parsed as an identifier"
    $ assertTokenizeResultEq "integral" [Id "integral"]
  booleanPrefix
    = test "`trueAnswer` is parsed as an identifier"
    $ assertTokenizeResultEq "trueAnswer" [Id "trueAnswer"]

  identsParse : List Test
  identsParse
    = [ keywordPrefix
      , typePrefix
      , booleanPrefix
      ]

  export
  tests : List Test
  tests
     = keywordsParse
    ++ typesParse
    ++ booleansParse
    ++ identsParse

namespace Ident
  floorPrefix : Test
  floorPrefix
    = test "identifiers can start with a `_`"
    $ assertTokenizeResultEq "_x" [Id "_x"]
  snakeCase : Test
  snakeCase
    = test "identifiers can contain a `_`"
    $ assertTokenizeResultEq "snake_case" [Id "snake_case"]
  camelCase : Test
  camelCase
    = test "identifiers can contain capital leters"
    $ assertTokenizeResultEq "camelCase" [Id "camelCase"]
  numbers : Test
  numbers
    = test "identifiers can contain numbers"
    $ assertTokenizeResultEq "x1" [Id "x1"]
  singleChar : Test
  singleChar
    = test "identifiers can consist one character"
    $ assertTokenizeResultEq "x" [Id "x"]

  export
  tests : List Test
  tests
    = [ floorPrefix
      , snakeCase
      , camelCase
      , numbers
      , singleChar
      ]

namespace String
  string : Test
  string
    = test "quotes are not included in the token data"
    $ assertTokenizeResultEq "\"str\"" [Str "str"]

  -- TODO: escape characters and stuff

  export
  tests : List Test
  tests = [ string ]

namespace Whitespace
  spaces : Test
  spaces
    = test "words separated by spaces are parsed as two tokens"
    $ assertTokenizeResultEq "int x" [Ty TokInt, Id "x"]

  newlines : Test
  newlines
    = test "words separated by newlines are parsed as two tokens"
    $ assertTokenizeResultEq "{\n}" [Br LeftCurlyBrace, Br RightCurlyBrace]

  newlinesAndSpaces : Test
  newlinesAndSpaces
    = test "words separated by newlines and spaces are parsed as two tokens"
    $ assertTokenizeResultEq "{ \n }" [Br LeftCurlyBrace, Br RightCurlyBrace]

  brackets : Test
  brackets
    = test "brackets don't require whitespace"
    $ assertTokenizeResultEq "(x)" [Br LeftBracket, Id "x", Br RightBracket]

  semicolon : Test
  semicolon
    = test "semicolon doesn't require whitespace"
    $ assertTokenizeResultEq "return;" [Kw Return, Sp Semicolon]

  operators : Test
  operators
    = test "operators don't require whitespace"
    $ assertTokenizeResultEq "2+2" [Num 2, Sp Plus, Num 2]

  comma : Test
  comma
    = test "commas don't require whitespace"
    $ assertTokenizeResultEq "x,y" [Id "x", Sp Comma, Id "y"]

  export
  tests : List Test
  tests
    = [ spaces
      , newlines
      , newlinesAndSpaces
      , brackets
      , semicolon
      , operators
      , comma
      ]

allTests : List Test
allTests
   = IdentsVSSpecialWords.tests
  ++ Ident.tests
  ++ String.tests
  ++ Whitespace.tests

export
main : IO ()
main = do
  putStrLn "Testing `Parse.Tokenize`"
  True <- runTests allTests
        | False => assert_total (idris_crash "tests failed")

  pure ()
