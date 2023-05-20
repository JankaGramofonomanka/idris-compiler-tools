module TypeCheck.Expr

import Control.Monad.State
import Control.Monad.Either

import Data.SortedMap
import Data.Zippable

import Data.DList
import LNG.Parsed                 as LNG
import LNG.TypeChecked            as TC
import Parse.Data.Position
import TypeCheck.Data.Context
import TypeCheck.Data.TypeCheckM
import TypeCheck.Utils

public export
TypeCheckM' : Type -> Type
TypeCheckM' = StateT VarCTX TypeCheckM

getVarType : ^LNG.Ident -> TypeCheckM' TC.LNGType
getVarType id = do
  m <- get
  case lookup (^^id) m of
    Just (p, t) => pure t
    Nothing => throwError (noSuchVariable id)




decideEq : (t, t' : TC.LNGType) -> Maybe (t = t')
decideEq TInt   TInt  = Just Refl
decideEq TBool  TBool = Just Refl
decideEq TVoid  TVoid = Just Refl
decideEq _ _ = Nothing



tcBinOp : BinOperator -> (t1, t2 : TC.LNGType) -> Maybe (t3 ** TC.BinOperator t1 t2 t3)

tcBinOp Add TInt  TInt  = Just (TInt  ** TC.Add)
tcBinOp Sub TInt  TInt  = Just (TInt  ** TC.Sub)
tcBinOp Mul TInt  TInt  = Just (TInt  ** TC.Mul)
tcBinOp Div TInt  TInt  = Just (TInt  ** TC.Div)
tcBinOp Mod TInt  TInt  = Just (TInt  ** TC.Mod)

tcBinOp And TBool TBool = Just (TBool ** TC.And)
tcBinOp Or  TBool TBool = Just (TBool ** TC.Or )

tcBinOp EQ TInt    TInt    = Just (TBool ** TC.EQ)
tcBinOp EQ TBool   TBool   = Just (TBool ** TC.EQ)
tcBinOp EQ TString TString = Just (TBool ** TC.EQ)

tcBinOp NE TInt    TInt    = Just (TBool ** TC.NE)
tcBinOp NE TBool   TBool   = Just (TBool ** TC.NE)
tcBinOp NE TString TString = Just (TBool ** TC.NE)

tcBinOp LE TInt TInt = Just (TBool ** TC.LE)
tcBinOp LT TInt TInt = Just (TBool ** TC.LT)
tcBinOp GE TInt TInt = Just (TBool ** TC.GE)
tcBinOp GT TInt TInt = Just (TBool ** TC.GT)

tcBinOp Concat TString TString  = Just (TString ** TC.Concat)

tcBinOp _ _ _ = Nothing

tcUnOp : UnOperator -> (t1 : TC.LNGType) -> Maybe (t2 ** TC.UnOperator t1 t2)
tcUnOp Neg TInt   = Just (TInt  ** TC.Neg)
tcUnOp Not TBool  = Just (TBool ** TC.Not)
tcUnOp _ _ = Nothing



getBinOp : (binOpExprPos : Pos) -> ^BinOperator -> (lt, rt : TC.LNGType) -> TypeCheckM' (t ** TC.BinOperator lt rt t)
getBinOp p op lt rt = do
  let Just op' = tcBinOp (^^op) lt rt
               | Nothing => throwError $ binOpTypeError p lt rt
  pure op'

getUnOp : (unOpExprPos : Pos) -> ^UnOperator -> (t : TC.LNGType) -> TypeCheckM' (t' ** TC.UnOperator t t')
getUnOp p op t = do
  let Just op' = tcUnOp (^^op) t
               | Nothing => throwError $ unOpTypeError p t
  pure op'



assertType : Pos -> (t, t' : TC.LNGType) -> TC.Expr t' -> TypeCheckM' (TC.Expr t)
assertType p t t' expr' = case decideEq t t' of
  Just prf => pure (rewrite prf in expr')
  Nothing => throwError $ typeError p t t'






mutual

  export
  typeCheckExpr : ^LNG.Expr -> TypeCheckM' (t ** TC.Expr t)

  typeCheckExpr (_ |^ Lit lit) = case ^^lit of
    LitBool   b => pure (TC.TBool   ** TC.Lit (TC.LitBool   b))
    LitInt    i => pure (TC.TInt    ** TC.Lit (TC.LitInt    i))
    LitString s => pure (TC.TString ** TC.Lit (TC.LitString s))

  typeCheckExpr (_ |^ Var id) = do
    t <- getVarType id
    pure (t ** TC.Var (mkVar t $ ^^id))

  typeCheckExpr (p |^ BinOperation op lhs rhs) = do
    (lt ** lhs') <- typeCheckExpr lhs
    (rt ** rhs') <- typeCheckExpr rhs
    (retT ** op') <- getBinOp p op lt rt
    pure (retT ** TC.BinOperation op' lhs' rhs')

  typeCheckExpr (p |^ UnOperation op expr) = do
    (t ** expr') <- typeCheckExpr expr
    (retT ** op') <- getUnOp p op t
    pure (retT ** TC.UnOperation op' expr')

  typeCheckExpr (_ |^ Call fun args) = do
    (retT, paramTs) <- lift $ getFunTypes fun
    args <- typeCheckArgs paramTs args
    
    let fun' = mkFun retT paramTs (^^fun)
    pure (retT ** TC.Call fun' args)

    where

      typeCheckArgs  : (ts : List TC.LNGType) -> ^(List (^Expr)) -> TypeCheckM' (DList TC.Expr ts)
      typeCheckArgs ts (argsPos |^ args) = typeCheckArgs' ts args where

        expected, actual : Nat
        expected = length ts
        actual = length args

        typeCheckArgs' : (ts : List TC.LNGType) -> List (^Expr) -> TypeCheckM' (DList TC.Expr ts)
        typeCheckArgs' Nil Nil = pure Nil
        typeCheckArgs' (t :: ts) (arg :: args) = do
          arg' <- typeCheckExprOfType t arg
          args' <- typeCheckArgs' ts args
          pure (arg' :: args')
        
        typeCheckArgs' Nil (arg :: _) = throwError $ numParamsMismatch (pos arg) expected actual
        typeCheckArgs' (t :: ts) Nil = throwError $ numParamsMismatch argsPos expected actual


  export
  typeCheckExprOfType : (t : TC.LNGType) -> ^LNG.Expr -> TypeCheckM' (TC.Expr t)
  typeCheckExprOfType t expr = do
    (t' ** expr') <- typeCheckExpr expr
    assertType (pos expr) t t' expr'

