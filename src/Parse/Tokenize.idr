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
returnS, whileS, ifS, elseS : String
returnS = "return"
ifS     = "if"
elseS   = "else"
whileS  = "while"

keywords : List String
keywords = [returnS, ifS, elseS, whileS]

kwReturn, kwWhile, kwIf, kwElse : Tokenizer Keyword
kwReturn = overwrite Return  (theString returnS)
kwIf     = overwrite If      (theString ifS)
kwElse   = overwrite Else    (theString elseS)
kwWhile  = overwrite While   (theString whileS)

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
leftBracket        = overwrite LeftBracket        (theChar '(')
rightBracket       = overwrite RightBracket       (theChar ')')
leftCurlyBrace     = overwrite LeftCurlyBrace     (theChar '{')
rightCurlyBrace    = overwrite RightCurlyBrace    (theChar '}')
leftSquareBracket  = overwrite LeftSquareBracket  (theChar '[')
rightSquareBracket = overwrite RightSquareBracket (theChar ']')

bracket' : Tokenizer Bracket
bracket' = leftBracket <|> rightBracket <|> leftCurlyBrace <|> rightCurlyBrace <|> leftSquareBracket <|> rightSquareBracket

bracket : Tokenizer Token
bracket = map Br <$> bracket'

-- TokType --------------------------------------------------------------------
intS, booleanS, stringS, voidS : String
intS     = "int"
booleanS = "boolean"
stringS  = "string"
voidS    = "void"

types : List String
types = [intS, booleanS, stringS, voidS]

tint, tbool, tvoid : Tokenizer TokType
tint    = overwrite TokInt    (theString intS)
tbool   = overwrite TokBool   (theString booleanS)
tstring = overwrite TokString (theString stringS)
tvoid   = overwrite TokVoid   (theString voidS)

tokType' : Tokenizer TokType
tokType' = tint <|> tbool <|> tstring <|> tvoid

tokType : Tokenizer Token
tokType = map Ty <$> tokType'

-- Num ------------------------------------------------------------------------
num : Tokenizer Token
num = map Num <$> integer

-- Boo ------------------------------------------------------------------------
trueS, falseS : String
trueS  = "true"
falseS = "false"

booleans : List String
booleans = [trueS, falseS]

true, false : Tokenizer Bool
true  = overwrite True  (theString trueS)
false = overwrite False (theString falseS)

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
            'a'  => p <<^> map ('\a'   ::) <$> stopOnRQuote
            'b'  => p <<^> map ('\b'   ::) <$> stopOnRQuote
            'e'  => p <<^> map ('\ESC' ::) <$> stopOnRQuote
            'f'  => p <<^> map ('\f'   ::) <$> stopOnRQuote
            'n'  => p <<^> map ('\n'   ::) <$> stopOnRQuote
            'r'  => p <<^> map ('\r'   ::) <$> stopOnRQuote
            't'  => p <<^> map ('\t'   ::) <$> stopOnRQuote
            'v'  => p <<^> map ('\v'   ::) <$> stopOnRQuote
            '\\' => p <<^> map ('\\'   ::) <$> stopOnRQuote
            '\'' => p <<^> map ('\''   ::) <$> stopOnRQuote
            '"'  => p <<^> map ('\"'   ::) <$> stopOnRQuote
            '?'  => p <<^> map ('\?'   ::) <$> stopOnRQuote
            ch'  => p <<^> map (ch'    ::) <$> stopOnRQuote
          
        '"' => pure (p |^ Nil)
        ch  => p <<^> map (ch ::) <$> stopOnRQuote

string : Tokenizer Token
string = map Str <$> string'      

-- Id -------------------------------------------------------------------------
reservedWords : List String
reservedWords = keywords ++ types ++ booleans

ident : Tokenizer Token
ident = map Id <$> (ident' `suchThat` not . (`elem` reservedWords)) where
  ident' : Tokenizer String
  ident' = do
    pfst  |^ first  <- sat isLower <|> floor
    prest |^ rest   <- many (sat isAlphaNum <|> floor)
    pure (fromTo pfst prest |^ (pack $ first :: map unPos rest))

-- Token ----------------------------------------------------------------------
token : Tokenizer Token
token = ident <|> keyword <|> specialSign <|> bracket <|> tokType <|> num <|> bool <|> string

tokens : SimpleParser (List $ ^Token)
tokens = (^^) <$> many (ws *> token) <* ws <* eof

||| Convert a string into a list of tokens
export
tokenize : String -> Maybe (List (^Token))
tokenize = simpleParse tokens
