module Interpreter.Expr

import Control.Monad.Either
import Control.Monad.State

import Data.SortedMap

import Data.DList
import Interpreter.InterpreterT
import Interpreter.Semantics
import LNG.Data.Position
import LNG.Parsed

assertType : Monad m => Pos -> (t, t' : LNGType) -> Value t' -> InterpreterT m (Value t)
assertType p TInt     TInt    val = pure val
assertType p TBool    TBool   val = pure val
assertType p TVoid    TVoid   val = pure val
assertType p expected actual  val = throwError $ typeError p expected actual

interpretLit : Monad m => ^Literal -> InterpreterT m (t ** Value t)
interpretLit (_ |^ LitInt i) = pure (TInt ** cast i)
interpretLit (_ |^ LitBool b) = pure (TBool ** b)

mutual
  export
  interpretExpr : Monad m => ^Expr -> InterpreterT m (t ** Value t)
  
  interpretExpr (_ |^ Lit lit) = interpretLit lit

  interpretExpr (_ |^ Var var) = getVar var
  
  interpretExpr (_ |^ BinOperation op lhs rhs) = case ^^op of
    Add => interpretAritmOp Semantics.add lhs rhs
    Sub => interpretAritmOp Semantics.sub lhs rhs
    Mul => interpretAritmOp Semantics.mul lhs rhs
    Div => interpretAritmOp Semantics.div lhs rhs
    And => interpretLogOp Semantics.and lhs rhs
    Or  => interpretLogOp Semantics.or lhs rhs
    EQ  => interpretEQOp lhs rhs
    LE  => interpretCMPOp Semantics.le lhs rhs
    LT  => interpretCMPOp Semantics.lt lhs rhs
    GE  => interpretCMPOp Semantics.ge lhs rhs
    GT  => interpretCMPOp Semantics.gt lhs rhs

  interpretExpr (_ |^ UnOperation op expr) = case ^^op of
    Neg => do
      val <- interpretExprOfType TInt expr
      pure (TInt ** Semantics.neg val)

    Not => do
      val <- interpretExprOfType TBool expr
      pure (TBool ** Semantics.not val)

  interpretExpr (_ |^ Call funId args) = do
    (t ** ts ** fun) <- getFun funId
    retVal <- interpretFun t ts fun args
    pure (t ** retVal)

  export
  interpretExprOfType : Monad m => (t : LNGType) -> ^Expr -> InterpreterT m (Value t)
  interpretExprOfType t expr = do
    (t' ** val) <- interpretExpr expr
    assertType (pos expr) t t' val

  interpretAritmOp : Monad m => (Value TInt -> Value TInt -> Value TInt) -> ^Expr -> ^Expr -> InterpreterT m (t ** Value t)
  interpretAritmOp fun lhs rhs = do
    lval <- interpretExprOfType TInt lhs
    rval <- interpretExprOfType TInt rhs
    pure (TInt ** fun lval rval)

  interpretLogOp : Monad m => (Value TBool -> Value TBool -> Value TBool) -> ^Expr -> ^Expr -> InterpreterT m (t ** Value t)
  interpretLogOp fun lhs rhs = do
    lval <- interpretExprOfType TBool lhs
    rval <- interpretExprOfType TBool rhs
    pure (TBool ** fun lval rval)

  interpretEQOp : Monad m => ^Expr -> ^Expr -> InterpreterT m (t ** Value t)
  interpretEQOp lhs rhs = do
    (lt ** lval) <- interpretExpr lhs
    case lt of
      TInt => do
        rval <- interpretExprOfType TInt rhs
        pure (TBool ** ieq lval rval)

      TBool => do
        rval <- interpretExprOfType TBool rhs
        pure (TBool ** beq lval rval)

      TVoid => throwError $ typeError' (pos lhs) [TInt, TBool] TVoid

  interpretCMPOp : Monad m => (Value TInt -> Value TInt -> Value TBool) -> ^Expr -> ^Expr -> InterpreterT m (t ** Value t)
  interpretCMPOp fun lhs rhs = do
    lval <- interpretExprOfType TInt lhs
    rval <- interpretExprOfType TInt rhs
    pure (TBool ** fun lval rval)


  interpretFun : Monad m
              => (t : LNGType)
              -> (ts : List LNGType)
              -> Fun t ts (InterpreterT m)
              -> ^(List $ ^Expr)
              -> InterpreterT m (Value t)
  interpretFun t ts fun args = let
    
      expected, actual : Nat
      expected = length ts
      actual = length (^^args)

      argsPos : Pos
      argsPos = pos args

      interpretArgs : (ts : List LNGType) -> List (^Expr) -> InterpreterT m (DList Value ts)
      interpretArgs Nil Nil = pure Nil
      interpretArgs (t :: ts) (arg :: args) = do
        arg' <- interpretExprOfType t arg
        args' <- interpretArgs ts args
        pure (arg' :: args')
      
      interpretArgs Nil (arg :: args) = throwError $ numParamsMismatch (pos arg) expected actual
      interpretArgs (t :: ts) Nil = throwError $ numParamsMismatch argsPos expected actual

    in do
      args' <- interpretArgs ts (^^args)
      -- TODO: take builtins into account
      st <- gets { ctx := empty }
      lift $ evalStateT st (fun args')


