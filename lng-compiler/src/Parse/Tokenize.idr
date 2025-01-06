module Parse.Tokenize

import Data.List
import Data.String.Extra
import Text.Lexer
import Parse.Data.Position
import Parse.Data.Token

myTokenMap : TokenMap Token
myTokenMap = [(is 'a', Str)]

implementation [tokenMap] Functor TokenMap where
  map f tokenMap = map (map (f .)) tokenMap

-- SpecialSign ----------------------------------------------------------------
specialSigns : TokenMap SpecialSign
specialSigns
  = [ (exact "++", const PlusPlus)
    , (exact "&&", const AndAnd)
    , (exact "||", const OrOr)
    , (exact "!=", const ExclamationEquals)
    , (exact "==", const DoubleEquals)
    , (exact ">=", const GreaterEquals)
    , (exact "<=", const LesserEquals)
    , (exact "+",  const Plus)
    , (exact "-",  const Minus)
    , (exact "*",  const Star)
    , (exact "/",  const Slash)
    , (exact "%",  const Percent)
    , (exact "=",  const Equals)
    , (exact "<",  const Lesser)
    , (exact ">",  const Greater)
    , (exact "!",  const Exclamation)
    , (exact ",",  const Comma)
    , (exact ";",  const Semicolon)
    ]

-- Bracket --------------------------------------------------------------------
brackets : TokenMap Bracket
brackets
  = [ (is '(', const LeftBracket)
    , (is ')', const RightBracket)
    , (is '{', const LeftCurlyBrace)
    , (is '}', const RightCurlyBrace)
    , (is '[', const LeftSquareBracket)
    , (is ']', const RightSquareBracket)
    ]

-- Num ------------------------------------------------------------------------
num : TokenMap Integer
num = [ (intLit, cast) ]

-- Str ------------------------------------------------------------------------
string : TokenMap String
string = [ (stringLit, shrink 1) ]

-- Words: Kewywords, Booleans, Types, Identifiers -----------------------------
word : Lexer
word = (lower <|> is '_') <+> many (alphaNum <|> is '_')

words : TokenMap Token
words = [ (word, toToken)] where
  toToken : String -> Token
  toToken s = case s of

    -- Keywords
    "return"  => Kw Return
    "if"      => Kw If
    "else"    => Kw Else
    "while"   => Kw While

    -- Types
    "int"     => Ty TokInt
    "boolean" => Ty TokBool
    "string"  => Ty TokString
    "void"    => Ty TokVoid

    -- Booleans
    "true"    => Boo True
    "false"   => Boo False

    -- Idents
    s         => Id s

-- Token ----------------------------------------------------------------------
tokens : TokenMap Token
tokens
   = map @{tokenMap} Sp specialSigns
  ++ map @{tokenMap} Br brackets
  ++ map @{tokenMap} Num num
  ++ map @{tokenMap} Str string
  ++ words

whitespace : TokenMap (Maybe Token)
whitespace = [ (some (space <|> newline), const Nothing)]

tokensAndWhitespace : TokenMap (Maybe Token)
tokensAndWhitespace
   = map @{tokenMap} Just tokens
  ++ whitespace

boundsToPos : Bounds -> Pos
boundsToPos bounds
  = MkPos
  { from = MkPosition { line = 1 + bounds.startLine, column = 1 + bounds.startCol }
  , to   = MkPosition { line = 1 + bounds.endLine,   column = 1 + bounds.endCol   }
  }

toPosToken : WithBounds Token -> ^Token
toPosToken token = boundsToPos token.bounds |^ token.val

export
tokenize : String -> Maybe (List (^Token))
tokenize s = case lex tokensAndWhitespace s of
  -- Ensure that the entire string parses, by checking that the remainer is empty
  (tokens, (_, _, ""))
    => Just
     . map toPosToken
     . catMaybes
     
     -- this convertes the `WithBounds (Maybe a)` to `Maybe (WithBoounds a)`
     . map sequence
     $ tokens
  _ => Nothing
