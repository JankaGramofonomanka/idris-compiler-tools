module Parse.Data.Token

public export
data Keyword
  = Return
  | If
  | Else
  | While

public export
data SpecialSign
  = Plus
  | Minus
  | Star
  | Slash
  | Percent
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

public export
data Bracket
  = LeftBracket
  | RightBracket
  | LeftCurlyBrace
  | RightCurlyBrace
  | LeftSquareBracket
  | RightSquareBracket

public export
data TokType
  = TokInt
  | TokBool
  | TokVoid

public export
data Token
  = Kw Keyword
  | Sp SpecialSign
  | Br Bracket
  | Ty TokType
  | Id String
  | Num Integer
  | Boo Bool
  --| Str String
  

