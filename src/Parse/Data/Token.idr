module Parse.Data.Token

public export
data Keyword
  = Return
  | If
  | Else
  | While

export
implementation Eq Keyword where

  Return  == Return = True
  If      == If     = True
  Else    == Else   = True
  While   == While  = True
  _       == _      = False

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

export
implementation Eq SpecialSign where
  Plus              == Plus               = True
  Minus             == Minus              = True
  Star              == Star               = True
  Slash             == Slash              = True
  Percent           == Percent            = True
  AndAnd            == AndAnd             = True
  OrOr              == OrOr               = True
  Equals            == Equals             = True
  ExclamationEquals == ExclamationEquals  = True
  DoubleEquals      == DoubleEquals       = True
  LesserEquals      == LesserEquals       = True
  Lesser            == Lesser             = True
  GreaterEquals     == GreaterEquals      = True
  Greater           == Greater            = True
  Exclamation       == Exclamation        = True
  Comma             == Comma              = True
  Semicolon         == Semicolon          = True
  _                 == _                  = False

public export
data Bracket
  = LeftBracket
  | RightBracket
  | LeftCurlyBrace
  | RightCurlyBrace
  | LeftSquareBracket
  | RightSquareBracket

export
implementation Eq Bracket where
  LeftBracket         == LeftBracket        = True
  RightBracket        == RightBracket       = True
  LeftCurlyBrace      == LeftCurlyBrace     = True
  RightCurlyBrace     == RightCurlyBrace    = True
  LeftSquareBracket   == LeftSquareBracket  = True
  RightSquareBracket  == RightSquareBracket = True
  _                   == _                  = False

public export
data TokType
  = TokInt
  | TokBool
  | TokVoid

export
implementation Eq TokType where
  TokInt  == TokInt   = True
  TokBool == TokBool  = True
  TokVoid == TokVoid  = True
  _       == _        = False

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

export
implementation Eq Token where
  Kw kw1    == Kw kw2   = kw1   == kw2
  Sp sp1    == Sp sp2   = sp1   == sp2
  Br br1    == Br br2   = br1   == br2
  Ty ty1    == Ty ty2   = ty1   == ty2
  Id id1    == Id id2   = id1   == id2
  Num num1  == Num num2 = num1  == num2
  Boo boo1  == Boo boo2 = boo1  == boo2
  _         == _        = False
  

