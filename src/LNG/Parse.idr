module LNG.Parse

import Control.Monad.State

import ParserCombinators
import LNG.Data.Position
import LNG.Parsed

-- Keywords -------------------------------------------------------------------
returnKW, whileKW, ifKW, elseKW : String
returnKW  = "return"
whileKW   = "while"
ifKW      = "if"
elseKW    = "else"

keywords : List String
keywords = [returnKW, whileKW, ifKW, elseKW]

kwReturn, kwWhile, kwIf, kwElse : PosParser ()
kwReturn  = overwrite () (theString returnKW)
kwWhile   = overwrite () (theString whileKW)
kwIf      = overwrite () (theString ifKW)
kwElse    = overwrite () (theString elseKW)


-- LNGType --------------------------------------------------------------------
tint : PosParser LNGType
tint = overwrite TInt (theString "int")

tbool : PosParser LNGType
tbool = overwrite TBool (theString "boolean")

tvoid : PosParser LNGType
tvoid = overwrite TVoid (theString "void")

lngType : PosParser LNGType
lngType = tint <|> tbool <|> tvoid

-- Literal --------------------------------------------------------------------
literal : PosParser Literal
literal = (map LitInt <$> integer) <|> (map LitBool <$> boolean)

-- Ident ----------------------------------------------------------------------
ident : PosParser Ident
ident = map MkId <$> (ident' `suchThat` not . (`elem` keywords)) where
  ident' : PosParser String
  ident' = do
    pfst |^ first <- sat isLower <|> floor
    prest |^ rest <- many (sat isAlphaNum <|> floor)
    pure (fromTo pfst prest |^ (pack $ first :: map unPos rest))

-- BinOperator ----------------------------------------------------------------
addOp : PosParser BinOperator
addOp = overwrite Add plus

subOp : PosParser BinOperator
subOp = overwrite Sub minus

mulOp : PosParser BinOperator
mulOp = overwrite Mul star

divOp : PosParser BinOperator
divOp = overwrite Div slash

-- TODO
--modOp : PosParser BinOperator
--modOp = overwrite Mod (theChar '%')

andOp : PosParser BinOperator
andOp = overwrite And (theString "&&")

orOp : PosParser BinOperator
orOp = overwrite Or (theString "||")

eqOp : PosParser BinOperator
eqOp = overwrite EQ (theString "==")

-- TODO
--neOp : PosParser BinOperator
--neOp = overwrite NE (theString "!=")

leOp : PosParser BinOperator
leOp = overwrite LE (theString "<=")

ltOp : PosParser BinOperator
ltOp = overwrite LT (theString "<")

geOp : PosParser BinOperator
geOp = overwrite GE (theString ">=")

gtOp : PosParser BinOperator
gtOp = overwrite GT (theString ">")

binOp0 : PosParser BinOperator
binOp0 = orOp

binOp1 : PosParser BinOperator
binOp1 = andOp

binOp2 : PosParser BinOperator
binOp2 = eqOp {- TODO <|> neOp -} <|> leOp <|> ltOp <|> geOp <|> gtOp

binOp3 : PosParser BinOperator
binOp3 = addOp <|> subOp

binOp4 : PosParser BinOperator
binOp4 = mulOp <|> divOp {- TODO <|> modOp -}


-- UnOperator -----------------------------------------------------------------
negOp : PosParser UnOperator
negOp = overwrite Neg minus

notOp : PosParser UnOperator
notOp = overwrite Not (theChar '!')

unOp : PosParser UnOperator
unOp = negOp <|> notOp

-- Expr -----------------------------------------------------------------------
binOperation : PosParser Expr -> PosParser BinOperator -> PosParser Expr -> PosParser Expr
binOperation lhs op rhs = do
  lhs'  <- lhs
  op'   <- ws *> op
  rhs'  <- ws *> rhs
  pure (fromTo (pos lhs') (pos rhs') |^ BinOperation op' lhs' rhs')

unOperation : PosParser UnOperator -> PosParser Expr -> PosParser Expr
unOperation op expr = do
  op' <- op
  expr' <- expr
  pure (fromTo (pos op') (pos expr') |^ UnOperation op' expr')

call : PosParser Expr -> PosParser Expr
call expr = do
  fun   <- ident
  args  <- ws *> inCurlyBraces (colonSeparated expr)
  pure (fromTo (pos fun) (pos args) |^ Call fun args)

lit : PosParser Expr
lit = Lit <^$> literal

var : PosParser Expr
var = Var <^$> ident

mutual
  expr6, expr5, expr4, expr3, expr2, expr1, expr0 : PosParser Expr
  expr6 = lit <|> var <|> call expr0 <|> inBrackets expr0
  expr5 = expr6 <|> unOperation unOp expr6
  expr4 = expr5 <|> binOperation expr5 binOp4 expr4
  expr3 = expr4 <|> binOperation expr4 binOp3 expr3
  expr2 = expr3 <|> binOperation expr3 binOp2 expr2
  expr1 = expr2 <|> binOperation expr2 binOp1 expr1
  expr0 = expr1 <|> binOperation expr1 binOp0 expr0

  expression : PosParser Expr
  expression = expr0

-- Instr ----------------------------------------------------------------------
declare : PosParser Instr
declare = do
  ty    <- lngType
  var   <- ws *> ident
  _     <- ws *> theChar '='
  expr  <- ws *> expression
  _     <- ws *> semicolon
  
  pure $ fromTo (pos ty) (pos expr) |^ Declare ty var expr

assign : PosParser Instr
assign = do
  var   <- ident
  _     <- ws *> theChar '='
  expr  <- ws *> expression
  _     <- ws *> semicolon
  pure (fromTo (pos var) (pos expr) |^ Assign var expr) 


return : PosParser Instr
return = do
  kwp |^ _  <- kwReturn
  expr      <- ws *> expression
  _         <- ws *> semicolon
  pure (fromTo kwp (pos expr) |^ Return expr)

retvoid : PosParser Instr
retvoid = overwrite RetVoid kwReturn <* ws <* semicolon

mutual
  block : PosParser Instr
  block = Block <^$> inCurlyBraces (many (ws *> instruction) <* ws)

  ifthenelse : PosParser Instr
  ifthenelse = do
    ifP |^ _  <- kwIf
    cond      <- ws *> inBrackets (ws *> expression <* ws)
    thn       <- ws *> instruction
    elseBLK ifP cond thn <|> pure (fromTo ifP (pos thn) |^ If cond thn)

    where
      elseBLK : Pos -> ^Expr -> ^Instr -> PosParser Instr
      elseBLK p cond thn = do
        _   <- ws *> kwElse
        els <- ws *> instruction
        pure (fromTo p (pos els) |^ IfElse cond thn els)


  while : PosParser Instr
  while = do
    kwp |^ _ <- kwWhile
    cond <- ws *> inBrackets (ws *> expression <* ws)
    body <- ws *> instruction
    pure (fromTo kwp (pos body) |^ While cond body)

  

  instruction : PosParser Instr
  instruction = return <|> retvoid <|> declare <|> assign <|> ifthenelse <|> while <|> block

-- FunDecl --------------------------------------------------------------------
singleParam : PosParser (^LNGType, ^Ident)
singleParam = do
  ty    <- lngType
  param <- ws *> ident
  pure $ fromTo (pos ty) (pos param) |^ (ty, param)

funParams : PosParser (List (^LNGType, ^Ident))
funParams = map (map (^^)) <$> colonSeparated singleParam

funDecl : PosParser FunDecl
funDecl = do
  retT    <- lngType
  funId   <- ws *> ident
  params  <- ws *> inBrackets funParams
  body    <- ws *> block
  pure (fromTo (pos retT) (pos body) |^ MkFunDecl { funId, retType = retT, params, body })


-- Program --------------------------------------------------------------------
export
program : PosParser Program
program = MkProgram <^$> many (ws *> funDecl) <* ws <* eof



