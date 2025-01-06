module Parse.Data.Token

import Derive.Prelude

%language ElabReflection

public export
data Keyword
  = Return
  | If
  | Else
  | While

%runElab derive "Keyword" [Eq, Show]

public export
data SpecialSign
  = Plus
  | Minus
  | Star
  | Slash
  | Percent
  | PlusPlus
  | AndAnd
  | OrOr
  | Equals
  | ExclamationEquals
  | DoubleEquals
  | LesserEquals
  | Lesser
  | GreaterEquals
  | Greater
  | Exclamation
  | Comma
  | Semicolon

%runElab derive "SpecialSign" [Eq, Show]

public export
data Bracket
  = LeftBracket
  | RightBracket
  | LeftCurlyBrace
  | RightCurlyBrace
  | LeftSquareBracket
  | RightSquareBracket

%runElab derive "Bracket" [Eq, Show]

public export
data TokType
  = TokInt
  | TokBool
  | TokString
  | TokVoid

%runElab derive "TokType" [Eq, Show]

public export
data Token
  = Kw Keyword
  | Sp SpecialSign
  | Br Bracket
  | Ty TokType
  | Id String
  | Num Integer
  | Boo Bool
  | Str String

%runElab derive "Token" [Eq, Show]
