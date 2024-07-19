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

export
implementation Show Keyword where
  show Return = "Return"
  show If     = "If"
  show Else   = "Else"
  show While  = "While"

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

export
implementation Eq SpecialSign where
  Plus              == Plus               = True
  Minus             == Minus              = True
  Star              == Star               = True
  Slash             == Slash              = True
  Percent           == Percent            = True
  PlusPlus          == PlusPlus           = True
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

export
implementation Show SpecialSign where
  show Plus              = "Plus"
  show Minus             = "Minus"
  show Star              = "Star"
  show Slash             = "Slash"
  show Percent           = "Percent"
  show PlusPlus          = "PlusPlus"
  show AndAnd            = "AndAnd"
  show OrOr              = "OrOr"
  show Equals            = "Equals"
  show ExclamationEquals = "ExclamationEquals"
  show DoubleEquals      = "DoubleEquals"
  show LesserEquals      = "LesserEquals"
  show Lesser            = "Lesser"
  show GreaterEquals     = "GreaterEquals"
  show Greater           = "Greater"
  show Exclamation       = "Exclamation"
  show Comma             = "Comma"
  show Semicolon         = "Semicolon"

public export
data Bracket
  = LeftBracket
  | RightBracket
  | LeftCurlyBrace
  | RightCurlyBrace
  | LeftSquareBracket
  | RightSquareBracket

export
implementation Show Bracket where
  show LeftBracket        = "LeftBracket"
  show RightBracket       = "RightBracket"
  show LeftCurlyBrace     = "LeftCurlyBrace"
  show RightCurlyBrace    = "RightCurlyBrace"
  show LeftSquareBracket  = "LeftSquareBracket"
  show RightSquareBracket = "RightSquareBracket"

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
  | TokString
  | TokVoid

export
implementation Eq TokType where
  TokInt    == TokInt     = True
  TokBool   == TokBool    = True
  TokString == TokString  = True
  TokVoid   == TokVoid    = True
  _         == _          = False

export
implementation Show TokType where
  show TokInt    = "TokInt"
  show TokBool   = "TokBool"
  show TokString = "TokString"
  show TokVoid   = "TokVoid"

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
  
export
implementation Show Token where
  show (Kw kw) = "Kw " ++ show kw
  show (Sp sp) = "Sp " ++ show sp
  show (Br br) = "Br " ++ show br
  show (Ty ty) = "Ty " ++ show ty
  show (Id id) = "Id " ++ show id
  show (Num num) = "Num " ++ show num
  show (Boo boo) = "Boo " ++ show boo
  show (Str str) = "Str " ++ show str
