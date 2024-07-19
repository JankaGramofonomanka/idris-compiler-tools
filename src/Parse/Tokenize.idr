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

-- Num ------------------------------------------------------------------------
num : Tokenizer Token
num = map Num <$> integer

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

-- Words: Kewywords, Booleans, Types, Identifiers -----------------------------
word : Tokenizer Token
word = map toToken <$> word' where
  word' : Tokenizer String
  word' = do
    pfst  |^ first  <- sat isLower <|> floor
    prest |^ rest   <- many (sat isAlphaNum <|> floor)
    pure (fromTo pfst prest |^ (pack $ first :: map unPos rest))

  toToken : String -> Token
  toToken s = case s of
    "return"  => Kw Return
    "if"      => Kw If
    "else"    => Kw Else
    "while"   => Kw While

    "int"     => Ty TokInt
    "boolean" => Ty TokBool
    "string"  => Ty TokString
    "void"    => Ty TokVoid

    "true"    => Boo True
    "false"   => Boo False

    s         => Id s

-- Token ----------------------------------------------------------------------
token : Tokenizer Token
token = word <|> specialSign <|> bracket <|> num <|> string

tokens : SimpleParser (List $ ^Token)
tokens = (^^) <$> many (ws *> token) <* ws <* eof

||| Convert a string into a list of tokens
export
tokenize : String -> Maybe (List (^Token))
tokenize = simpleParse tokens
