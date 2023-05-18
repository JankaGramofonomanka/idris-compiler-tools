module Parse.Tokenize

import Control.Monad.State

import Parse.Combinators
import Parse.Data.Parser
import Parse.Data.Position
import Parse.Data.Token



-- Keyword --------------------------------------------------------------------
returnKW, whileKW, ifKW, elseKW : String
returnKW  = "return"
ifKW      = "if"
elseKW    = "else"
whileKW   = "while"

keywords : List String
keywords = [returnKW, ifKW, elseKW, whileKW]

kwReturn, kwWhile, kwIf, kwElse : SimplePosParser Keyword
kwReturn  = overwrite Return  (theString returnKW)
kwIf      = overwrite If      (theString ifKW)
kwElse    = overwrite Else    (theString elseKW)
kwWhile   = overwrite While   (theString whileKW)

keyword' : SimplePosParser Keyword
keyword' = kwReturn <|> kwWhile <|> kwIf <|> kwElse

keyword : SimplePosParser Token
keyword = map Kw <$> keyword'

-- SpecialSign ----------------------------------------------------------------
plus, minus, star, slash, percent, andand, oror, equals : SimplePosParser SpecialSign
exclamationEquals, doubleEquals, lesserEquals, lesser   : SimplePosParser SpecialSign
greaterEquals, greater, exclamation, comma, semicolon   : SimplePosParser SpecialSign

plus              = overwrite Plus              (theString "+")
minus             = overwrite Minus             (theString "-")
star              = overwrite Star              (theString "*")
slash             = overwrite Slash             (theString "/")
percent           = overwrite Percent           (theString "%")
andand            = overwrite AndAnd            (theString "&&")
oror              = overwrite OrOr              (theString "||")
equals            = overwrite Equals            (theString "=")
exclamationEquals = overwrite ExclamationEquals (theString "!=")
doubleEquals      = overwrite DoubleEquals      (theString "==")
lesserEquals      = overwrite LesserEquals      (theString "<=")
lesser            = overwrite Lesser            (theString "<")
greaterEquals     = overwrite GreaterEquals     (theString ">=")
greater           = overwrite Greater           (theString ">")
exclamation       = overwrite Exclamation       (theString "!")
comma             = overwrite Comma             (theString ",")
semicolon         = overwrite Semicolon         (theString ";")

specialSign' : SimplePosParser SpecialSign
specialSign'
    = plus <|> minus <|> star <|> slash <|> percent <|> andand <|> oror
  <|> equals <|> exclamationEquals <|> doubleEquals <|> lesserEquals
  <|> lesser <|> greaterEquals <|> greater <|> exclamation <|> comma
  <|> semicolon

specialSign : SimplePosParser Token
specialSign = map Sp <$> specialSign'

-- Bracket --------------------------------------------------------------------
leftBracket, rightBracket, leftCurlyBrace, rightCurlyBrace, leftSquareBracket, rightSquareBracket : SimplePosParser Bracket
leftBracket         = overwrite LeftBracket        (theChar '(')
rightBracket        = overwrite RightBracket       (theChar ')')
leftCurlyBrace      = overwrite LeftCurlyBrace     (theChar '{')
rightCurlyBrace     = overwrite RightCurlyBrace    (theChar '}')
leftSquareBracket   = overwrite LeftSquareBracket  (theChar '[')
rightSquareBracket  = overwrite RightSquareBracket (theChar ']')

bracket' : SimplePosParser Bracket
bracket' = leftBracket <|> rightBracket <|> leftCurlyBrace <|> rightCurlyBrace <|> leftSquareBracket <|> rightSquareBracket

bracket : SimplePosParser Token
bracket = map Br <$> bracket'

-- TokType --------------------------------------------------------------------
tint, tbool, tvoid : SimplePosParser TokType
tint  = overwrite TokInt  (theString "int")
tbool = overwrite TokBool (theString "bool")
tvoid = overwrite TokVoid (theString "void")

tokType' : SimplePosParser TokType
tokType' = tint <|> tbool <|> tvoid

tokType : SimplePosParser Token
tokType = map Ty <$> tokType'

-- Num ------------------------------------------------------------------------
num : SimplePosParser Token
num = map Num <$> integer

-- Boo ------------------------------------------------------------------------
true, false : SimplePosParser Bool
true  = overwrite True  (theString "true")
false = overwrite False (theString "false")

bool' : SimplePosParser Bool
bool' = true <|> false

bool : SimplePosParser Token
bool = map Boo <$> bool'

-- Id -------------------------------------------------------------------------
ident : SimplePosParser Token
ident = map Id <$> (ident' `suchThat` not . (`elem` keywords)) where
  ident' : SimplePosParser String
  ident' = do
    pfst  |^ first  <- sat isLower <|> floor
    prest |^ rest   <- many (sat isAlphaNum <|> floor)
    pure (fromTo pfst prest |^ (pack $ first :: map unPos rest))

-- Token ----------------------------------------------------------------------
token : SimplePosParser Token
token = keyword <|> specialSign <|> bracket <|> tokType <|> num <|> bool <|> ident

tokens : SimpleParser (List $ ^Token)
tokens = (^^) <$> many (ws *> token) <* token

export
tokenize : String -> Maybe (List (^Token))
tokenize = simpleParse tokens
