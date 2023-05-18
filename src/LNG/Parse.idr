module LNG.Parse

import Control.Monad.State

import Parse.Combinators
import Parse.Data.Parser
import Parse.Data.Position
import LNG.Parsed

-- Keywords -------------------------------------------------------------------
returnKW, whileKW, ifKW, elseKW : String
returnKW  = "return"
whileKW   = "while"
ifKW      = "if"
elseKW    = "else"

keywords : List String
keywords = [returnKW, whileKW, ifKW, elseKW]

kwReturn, kwWhile, kwIf, kwElse : SimplePosParser ()
kwReturn  = overwrite () (theString returnKW)
kwWhile   = overwrite () (theString whileKW)
kwIf      = overwrite () (theString ifKW)
kwElse    = overwrite () (theString elseKW)


-- LNGType --------------------------------------------------------------------
tint : SimplePosParser LNGType
tint = overwrite TInt (theString "int")

tbool : SimplePosParser LNGType
tbool = overwrite TBool (theString "boolean")

tvoid : SimplePosParser LNGType
tvoid = overwrite TVoid (theString "void")

lngType : SimplePosParser LNGType
lngType = tint <|> tbool <|> tvoid

-- Literal --------------------------------------------------------------------
literal : SimplePosParser Literal
literal = (map LitInt <$> integer) <|> (map LitBool <$> boolean)

-- Ident ----------------------------------------------------------------------
ident : SimplePosParser Ident
ident = map MkId <$> (ident' `suchThat` not . (`elem` keywords)) where
  ident' : SimplePosParser String
  ident' = do
    pfst |^ first <- sat isLower <|> floor
    prest |^ rest <- many (sat isAlphaNum <|> floor)
    pure (fromTo pfst prest |^ (pack $ first :: map unPos rest))

-- BinOperator ----------------------------------------------------------------
addOp : SimplePosParser BinOperator
addOp = overwrite Add plus

subOp : SimplePosParser BinOperator
subOp = overwrite Sub minus

mulOp : SimplePosParser BinOperator
mulOp = overwrite Mul star

divOp : SimplePosParser BinOperator
divOp = overwrite Div slash

-- TODO
--modOp : SimplePosParser BinOperator
--modOp = overwrite Mod (theChar '%')

andOp : SimplePosParser BinOperator
andOp = overwrite And (theString "&&")

orOp : SimplePosParser BinOperator
orOp = overwrite Or (theString "||")

eqOp : SimplePosParser BinOperator
eqOp = overwrite EQ (theString "==")

-- TODO
--neOp : SimplePosParser BinOperator
--neOp = overwrite NE (theString "!=")

leOp : SimplePosParser BinOperator
leOp = overwrite LE (theString "<=")

ltOp : SimplePosParser BinOperator
ltOp = overwrite LT (theString "<")

geOp : SimplePosParser BinOperator
geOp = overwrite GE (theString ">=")

gtOp : SimplePosParser BinOperator
gtOp = overwrite GT (theString ">")

binOp0 : SimplePosParser BinOperator
binOp0 = orOp

binOp1 : SimplePosParser BinOperator
binOp1 = andOp

binOp2 : SimplePosParser BinOperator
binOp2 = eqOp {- TODO <|> neOp -} <|> leOp <|> ltOp <|> geOp <|> gtOp

binOp3 : SimplePosParser BinOperator
binOp3 = addOp <|> subOp

binOp4 : SimplePosParser BinOperator
binOp4 = mulOp <|> divOp {- TODO <|> modOp -}


-- UnOperator -----------------------------------------------------------------
negOp : SimplePosParser UnOperator
negOp = overwrite Neg minus

notOp : SimplePosParser UnOperator
notOp = overwrite Not (theChar '!')

unOp : SimplePosParser UnOperator
unOp = negOp <|> notOp

-- Expr -----------------------------------------------------------------------
binOperation : SimplePosParser Expr -> SimplePosParser BinOperator -> SimplePosParser Expr -> SimplePosParser Expr
binOperation lhs op rhs = do
  lhs'  <- lhs
  op'   <- ws *> op
  rhs'  <- ws *> rhs
  pure (fromTo (pos lhs') (pos rhs') |^ BinOperation op' lhs' rhs')

unOperation : SimplePosParser UnOperator -> SimplePosParser Expr -> SimplePosParser Expr
unOperation op expr = do
  op' <- op
  expr' <- expr
  pure (fromTo (pos op') (pos expr') |^ UnOperation op' expr')

call : SimplePosParser Expr -> SimplePosParser Expr
call expr = do
  fun   <- ident
  args  <- ws *> inCurlyBraces (commaSeparated expr)
  pure (fromTo (pos fun) (pos args) |^ Call fun args)

lit : SimplePosParser Expr
lit = Lit <^$> literal

var : SimplePosParser Expr
var = Var <^$> ident

mutual
  expr6, expr5, expr4, expr3, expr2, expr1, expr0 : SimplePosParser Expr
  expr6 = lit <|> var <|> call expr0 <|> inBrackets expr0
  expr5 = expr6 <|> unOperation unOp expr6
  expr4 = expr5 <|> binOperation expr5 binOp4 expr4
  expr3 = expr4 <|> binOperation expr4 binOp3 expr3
  expr2 = expr3 <|> binOperation expr3 binOp2 expr2
  expr1 = expr2 <|> binOperation expr2 binOp1 expr1
  expr0 = expr1 <|> binOperation expr1 binOp0 expr0

  expression : SimplePosParser Expr
  expression = expr0

-- Instr ----------------------------------------------------------------------
declare : SimplePosParser Instr
declare = do
  ty    <- lngType
  var   <- ws *> ident
  _     <- ws *> theChar '='
  expr  <- ws *> expression
  _     <- ws *> semicolon
  
  pure $ fromTo (pos ty) (pos expr) |^ Declare ty var expr

assign : SimplePosParser Instr
assign = do
  var   <- ident
  _     <- ws *> theChar '='
  expr  <- ws *> expression
  _     <- ws *> semicolon
  pure (fromTo (pos var) (pos expr) |^ Assign var expr) 


return : SimplePosParser Instr
return = do
  kwp |^ _  <- kwReturn
  expr      <- ws *> expression
  _         <- ws *> semicolon
  pure (fromTo kwp (pos expr) |^ Return expr)

retvoid : SimplePosParser Instr
retvoid = overwrite RetVoid kwReturn <* ws <* semicolon

mutual
  block : SimplePosParser Instr
  block = Block <^$> inCurlyBraces (many (ws *> instruction) <* ws)

  ifthenelse : SimplePosParser Instr
  ifthenelse = do
    ifP |^ _  <- kwIf
    cond      <- ws *> inBrackets (ws *> expression <* ws)
    thn       <- ws *> instruction
    elseBLK ifP cond thn <|> pure (fromTo ifP (pos thn) |^ If cond thn)

    where
      elseBLK : Pos -> ^Expr -> ^Instr -> SimplePosParser Instr
      elseBLK p cond thn = do
        _   <- ws *> kwElse
        els <- ws *> instruction
        pure (fromTo p (pos els) |^ IfElse cond thn els)


  while : SimplePosParser Instr
  while = do
    kwp |^ _ <- kwWhile
    cond <- ws *> inBrackets (ws *> expression <* ws)
    body <- ws *> instruction
    pure (fromTo kwp (pos body) |^ While cond body)

  

  instruction : SimplePosParser Instr
  instruction = return <|> retvoid <|> declare <|> assign <|> ifthenelse <|> while <|> block

-- FunDecl --------------------------------------------------------------------
singleParam : SimplePosParser (^LNGType, ^Ident)
singleParam = do
  ty    <- lngType
  param <- ws *> ident
  pure $ fromTo (pos ty) (pos param) |^ (ty, param)

funParams : SimplePosParser (List (^LNGType, ^Ident))
funParams = map (map (^^)) <$> commaSeparated singleParam

funDecl : SimplePosParser FunDecl
funDecl = do
  retT    <- lngType
  funId   <- ws *> ident
  params  <- ws *> inBrackets funParams
  body    <- ws *> block
  pure (fromTo (pos retT) (pos body) |^ MkFunDecl { funId, retType = retT, params, body })


-- Program --------------------------------------------------------------------
export
program : SimplePosParser Program
program = MkProgram <^$> many (ws *> funDecl) <* ws <* eof



