module Parse.Parse

import Control.Monad.State

import Data.List.Lazy

import Parse.Combinators
import Parse.Data.Parser
import Parse.Data.Position
import Parse.Data.Token
import Parse.Data.Tokenize
import LNG.Parsed

public export
LNGParser : Type -> Type
LNGParser = PosParser (^Token)

theToken : Token -> LNGParser Token
theToken t = item `suchThat` (== t)

comma, semicolon, equals : LNGParser Token
comma = theToken (Sp Comma)
semicolon = theToken (Sp Semicolon)
equals = theToken (Sp Equals)


commaSeparated : (item : LNGParser b) -> LNGParser (List (^b))
commaSeparated = separated comma

inCurlyBraces : LNGParser a -> LNGParser a
inCurlyBraces = between (theToken $ Br LeftCurlyBrace) (theToken $ Br RightCurlyBrace)

inBrackets : LNGParser a -> LNGParser a
inBrackets = between (theToken $ Br LeftBracket) (theToken $ Br RightBracket)

-- Keywords -------------------------------------------------------------------
kwReturn, kwWhile, kwIf, kwElse : LNGParser ()
kwReturn  = overwrite () (theToken $ Kw Return)
kwWhile   = overwrite () (theToken $ Kw While)
kwIf      = overwrite () (theToken $ Kw If)
kwElse    = overwrite () (theToken $ Kw Else)


-- LNGType --------------------------------------------------------------------
tint, tbool, tvoid : LNGParser LNGType
tint    = overwrite TInt    (theToken $ Ty TokInt)
tbool   = overwrite TBool   (theToken $ Ty TokBool)
tstring = overwrite TString (theToken $ Ty TokString)
tvoid   = overwrite TVoid   (theToken $ Ty TokVoid)

lngType : LNGParser LNGType
lngType = tint <|> tbool <|> tstring <|> tvoid

-- Literal --------------------------------------------------------------------
integer : LNGParser Integer
integer = do
  p |^ Num i <- the (LNGParser Token) item
              | _ => empty
  pure (p |^ i)

boolean : LNGParser Bool
boolean = do
  p |^ Boo b <- the (LNGParser Token) item
              | _ => empty
  pure (p |^ b)

string : LNGParser String
string = do
  p |^ Str s <- the (LNGParser Token) item
              | _ => empty

  pure (p |^ s)

literal : LNGParser Literal
literal = (map LitInt <$> integer) <|> (map LitBool <$> boolean) <|> (map LitString <$> string)

-- Ident ----------------------------------------------------------------------
ident : LNGParser Ident
ident = do
  p |^ Id id <- the (LNGParser Token) item
              | _ => empty
  pure (p |^ MkId id)

-- BinOperator ----------------------------------------------------------------
addOp, subOp, mulOp, divOp, modOp : LNGParser BinOperator
addOp = overwrite Add $ theToken (Sp Plus)
subOp = overwrite Sub $ theToken (Sp Minus)
mulOp = overwrite Mul $ theToken (Sp Star)
divOp = overwrite Div $ theToken (Sp Slash)
modOp = overwrite Mod $ theToken (Sp Percent)

andOp, orOp : LNGParser BinOperator
andOp = overwrite And $ theToken (Sp AndAnd)
orOp  = overwrite Or  $ theToken (Sp OrOr)

eqOp, neOp, leOp, ltOp, geOp, gtOp : LNGParser BinOperator
eqOp = overwrite EQ $ theToken (Sp DoubleEquals)
neOp = overwrite NE $ theToken (Sp ExclamationEquals)
leOp = overwrite LE $ theToken (Sp LesserEquals)
ltOp = overwrite LT $ theToken (Sp Lesser)
geOp = overwrite GE $ theToken (Sp GreaterEquals)
gtOp = overwrite GT $ theToken (Sp Greater)

concatOp : LNGParser BinOperator
concatOp = overwrite Concat $ theToken (Sp PlusPlus)

binOp0, binOp1, binOp2, binOp3, binOp4 : LNGParser BinOperator
binOp0 = orOp
binOp1 = andOp
binOp2 = eqOp <|> neOp <|> leOp <|> ltOp <|> geOp <|> gtOp
binOp3 = addOp <|> subOp <|> concatOp
binOp4 = mulOp <|> divOp <|> modOp

-- UnOperator -----------------------------------------------------------------
negOp, notOp : LNGParser UnOperator
negOp = overwrite Neg $ theToken (Sp Minus)
notOp = overwrite Not $ theToken (Sp Exclamation)

unOp : LNGParser UnOperator
unOp = negOp <|> notOp

-- Expr -----------------------------------------------------------------------
binOperation : LNGParser Expr -> LNGParser BinOperator -> LNGParser Expr -> LNGParser Expr
binOperation lhs op rhs = do
  lhs'  <- lhs
  op'   <- op
  rhs'  <- rhs
  pure (fromTo (pos lhs') (pos rhs') |^ BinOperation op' lhs' rhs')

unOperation : LNGParser UnOperator -> LNGParser Expr -> LNGParser Expr
unOperation op expr = do
  op' <- op
  expr' <- expr
  pure (fromTo (pos op') (pos expr') |^ UnOperation op' expr')

call : LNGParser Expr -> LNGParser Expr
call expr = do
  fun   <- ident
  args  <- inBrackets (commaSeparated expr)
  pure (fromTo (pos fun) (pos args) |^ Call fun args)

lit : LNGParser Expr
lit = Lit <^$> literal

var : LNGParser Expr
var = Var <^$> ident

mutual
  expr6, expr5, expr4, expr3, expr2, expr1, expr0 : LNGParser Expr
  expr6 = lit <|> var <|> call expr0 <|> inBrackets expr0
  expr5 = expr6 <|> unOperation unOp expr6
  expr4 = expr5 <|> binOperation expr5 binOp4 expr4
  expr3 = expr4 <|> binOperation expr4 binOp3 expr3
  expr2 = expr3 <|> binOperation expr3 binOp2 expr2
  expr1 = expr2 <|> binOperation expr2 binOp1 expr1
  expr0 = expr1 <|> binOperation expr1 binOp0 expr0

  expression : LNGParser Expr
  expression = expr0

-- Instr ----------------------------------------------------------------------
declare : LNGParser Instr
declare = do
  ty    <- lngType
  var   <- ident
  _     <- equals
  expr  <- expression
  _     <- semicolon
  
  pure $ fromTo (pos ty) (pos expr) |^ Declare ty var expr

assign : LNGParser Instr
assign = do
  var   <- ident
  _     <- equals
  expr  <- expression
  _     <- semicolon
  pure (fromTo (pos var) (pos expr) |^ Assign var expr) 

exec : LNGParser Instr
exec = Exec <^$> expression <* semicolon

return : LNGParser Instr
return = do
  kwp |^ _  <- kwReturn
  expr      <- expression
  _         <- semicolon
  pure (fromTo kwp (pos expr) |^ Return expr)

retvoid : LNGParser Instr
retvoid = overwrite RetVoid kwReturn <* semicolon

mutual
  block : LNGParser Instr
  block = Block <^$> inCurlyBraces (many instruction)

  ifthenelse : LNGParser Instr
  ifthenelse = do
    ifP |^ _  <- kwIf
    cond      <- inBrackets expression
    thn       <- instruction
    elseBLK ifP cond thn <|> pure (fromTo ifP (pos thn) |^ If cond thn)

    where
      elseBLK : Pos -> ^Expr -> ^Instr -> LNGParser Instr
      elseBLK p cond thn = do
        _   <- kwElse
        els <- instruction
        pure (fromTo p (pos els) |^ IfElse cond thn els)


  while : LNGParser Instr
  while = do
    kwp |^ _ <- kwWhile
    cond <- inBrackets expression
    body <- instruction
    pure (fromTo kwp (pos body) |^ While cond body)

  

  instruction : LNGParser Instr
  instruction = return <|> retvoid <|> declare <|> assign <|> ifthenelse <|> while <|> block <|> exec

-- FunDef ---------------------------------------------------------------------
singleParam : LNGParser (^LNGType, ^Ident)
singleParam = do
  ty    <- lngType
  param <- ident
  pure $ fromTo (pos ty) (pos param) |^ (ty, param)

funParams : LNGParser (List (^LNGType, ^Ident))
funParams = map (map (^^)) <$> commaSeparated singleParam

funDecl : LNGParser FunDef
funDecl = do
  retT    <- lngType
  funId   <- ident
  params  <- inBrackets funParams
  body    <- block
  pure (fromTo (pos retT) (pos body) |^ MkFunDef { funId, retType = retT, params, body })


-- Program --------------------------------------------------------------------
export
program : LNGParser Program
program = MkProgram <^$> many (funDecl) <* eof


