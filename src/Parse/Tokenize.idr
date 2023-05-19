module Parse.Tokenize

import Control.Monad.State

import Data.List.Lazy

import Parse.Combinators
import Parse.Data.Parser
import Parse.Data.Position
import Parse.Data.Token
import Parse.Data.Tokenize

Tokenizer : Type -> Type
Tokenizer = SimplePosParser

-- Keyword --------------------------------------------------------------------
returnKW, whileKW, ifKW, elseKW : String
returnKW  = "return"
ifKW      = "if"
elseKW    = "else"
whileKW   = "while"

keywords : List String
keywords = [returnKW, ifKW, elseKW, whileKW]

kwReturn, kwWhile, kwIf, kwElse : Tokenizer Keyword
kwReturn  = overwrite Return  (theString returnKW)
kwIf      = overwrite If      (theString ifKW)
kwElse    = overwrite Else    (theString elseKW)
kwWhile   = overwrite While   (theString whileKW)

keyword' : Tokenizer Keyword
keyword' = kwReturn <|> kwWhile <|> kwIf <|> kwElse

keyword : Tokenizer Token
keyword = map Kw <$> keyword'

-- SpecialSign ----------------------------------------------------------------
plusplus, andand, oror, exclamationEquals, doubleEquals, greaterEquals, 
lesserEquals, plus, minus, star, slash, percent, equals, lesser, greater, 
exclamation, comma, semicolon : Tokenizer SpecialSign

plusplus          = overwrite PlusPlus          (theString "++")
andand            = overwrite AndAnd            (theString "&&")
oror              = overwrite OrOr              (theString "||")
exclamationEquals = overwrite ExclamationEquals (theString "!=")
doubleEquals      = overwrite DoubleEquals      (theString "==")
greaterEquals     = overwrite GreaterEquals     (theString ">=")
lesserEquals      = overwrite LesserEquals      (theString "<=")
plus              = overwrite Plus              (theString "+")
minus             = overwrite Minus             (theString "-")
star              = overwrite Star              (theString "*")
slash             = overwrite Slash             (theString "/")
percent           = overwrite Percent           (theString "%")
equals            = overwrite Equals            (theString "=")
lesser            = overwrite Lesser            (theString "<")
greater           = overwrite Greater           (theString ">")
exclamation       = overwrite Exclamation       (theString "!")
comma             = overwrite Comma             (theString ",")
semicolon         = overwrite Semicolon         (theString ";")

-- Double character signs should be first
specialSign' : Tokenizer SpecialSign
specialSign'
    = plusplus <|> andand <|> oror <|> exclamationEquals <|> doubleEquals
  <|> greaterEquals <|> lesserEquals <|> plus <|> minus <|> star <|> slash
  <|> percent <|> equals <|> lesser <|> greater <|> exclamation <|> comma
  <|> semicolon

specialSign : Tokenizer Token
specialSign = map Sp <$> specialSign'

-- Bracket --------------------------------------------------------------------
leftBracket, rightBracket, leftCurlyBrace, rightCurlyBrace, leftSquareBracket, rightSquareBracket : Tokenizer Bracket
leftBracket         = overwrite LeftBracket        (theChar '(')
rightBracket        = overwrite RightBracket       (theChar ')')
leftCurlyBrace      = overwrite LeftCurlyBrace     (theChar '{')
rightCurlyBrace     = overwrite RightCurlyBrace    (theChar '}')
leftSquareBracket   = overwrite LeftSquareBracket  (theChar '[')
rightSquareBracket  = overwrite RightSquareBracket (theChar ']')

bracket' : Tokenizer Bracket
bracket' = leftBracket <|> rightBracket <|> leftCurlyBrace <|> rightCurlyBrace <|> leftSquareBracket <|> rightSquareBracket

bracket : Tokenizer Token
bracket = map Br <$> bracket'

-- TokType --------------------------------------------------------------------
tint, tbool, tvoid : Tokenizer TokType
tint    = overwrite TokInt    (theString "int")
tbool   = overwrite TokBool   (theString "bool")
tstring = overwrite TokString (theString "string")
tvoid   = overwrite TokVoid   (theString "void")

tokType' : Tokenizer TokType
tokType' = tint <|> tbool <|> tstring <|> tvoid

tokType : Tokenizer Token
tokType = map Ty <$> tokType'

-- Num ------------------------------------------------------------------------
num : Tokenizer Token
num = map Num <$> integer

-- Boo ------------------------------------------------------------------------
true, false : Tokenizer Bool
true  = overwrite True  (theString "true")
false = overwrite False (theString "false")

bool' : Tokenizer Bool
bool' = true <|> false

bool : Tokenizer Token
bool = map Boo <$> bool'

-- Str ------------------------------------------------------------------------
string' : Tokenizer String
string' = do
  lp |^ lquote <- theChar '"'
  rp |^ s <-map  pack <$> stopOnRQuote
  pure (fromTo lp rp |^ s)

  where
    stopOnRQuote : Tokenizer (List Char)
    stopOnRQuote = do
      p |^ ch <- the (Tokenizer Char) item
      case ch of
        '\\' => do
          p' |^ ch' <- the (Tokenizer Char) item
          case ch' of
            '"' => p <<^> map ('"' ::) <$> stopOnRQuote
            ch' => p <<^> map (\l => ch :: ch' :: l) <$> stopOnRQuote
          
        '"'   => pure (p |^ Nil)
        ch    => p <<^> map (ch ::) <$> stopOnRQuote

string : Tokenizer Token
string = map Str <$> string'      

-- Id -------------------------------------------------------------------------
ident : Tokenizer Token
ident = map Id <$> (ident' `suchThat` not . (`elem` keywords)) where
  ident' : Tokenizer String
  ident' = do
    pfst  |^ first  <- sat isLower <|> floor
    prest |^ rest   <- many (sat isAlphaNum <|> floor)
    pure (fromTo pfst prest |^ (pack $ first :: map unPos rest))

-- Token ----------------------------------------------------------------------
token : Tokenizer Token
token = keyword <|> specialSign <|> bracket <|> tokType <|> num <|> bool <|> string <|> ident

tokens : SimpleParser (List $ ^Token)
tokens = (^^) <$> many (ws *> token) <* ws <* eof

export
tokenize : String -> Maybe (List (^Token))
tokenize = simpleParse tokens
