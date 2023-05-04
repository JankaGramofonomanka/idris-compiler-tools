module TypeCheck.Expr

import Control.Monad.State
import Control.Monad.Either

import Data.SortedMap
import Data.Zippable

import Data.DList
import LNG.Parsed                 as LNG
import LNG.TypeChecked            as TC
import TypeCheck.Tools.CTX
import TypeCheck.Tools.TypeCheckM

public export
TypeCheckM' : Type -> Type
TypeCheckM' = StateT VarCTX TypeCheckM

getVarType : LNG.Ident -> TypeCheckM' TC.LNGType
getVarType id = do
  m <- get
  case lookup id m of
    Just t => pure t
    Nothing => throwError (NoSuchVariable id)




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

tcBinOp And TBool TBool = Just (TBool ** TC.And)
tcBinOp Or  TBool TBool = Just (TBool ** TC.Or )

tcBinOp EQ  TBool TBool = Just (TBool ** TC.EQ)
tcBinOp EQ  TInt  TInt  = Just (TBool ** TC.EQ)
tcBinOp LE  TInt  TInt  = Just (TBool ** TC.LE)
tcBinOp LT  TInt  TInt  = Just (TBool ** TC.LT)
tcBinOp GE  TInt  TInt  = Just (TBool ** TC.GE)
tcBinOp GT  TInt  TInt  = Just (TBool ** TC.GT)

tcBinOp _ _ _ = Nothing

tcUnOp : UnOperator -> (t1 : TC.LNGType) -> Maybe (t2 ** TC.UnOperator t1 t2)
tcUnOp Neg TInt   = Just (TInt  ** TC.Neg)
tcUnOp Not TBool  = Just (TBool ** TC.Not)
tcUnOp _ _ = Nothing



getBinOp : BinOperator -> (lt, rt : TC.LNGType) -> TypeCheckM' (t ** TC.BinOperator lt rt t)
getBinOp op lt rt = do
  let Just op' = tcBinOp op lt rt
               -- TODO: make the error contain more info
               | Nothing => throwError TypeError
  pure op'

getUnOp : UnOperator -> (t : TC.LNGType) -> TypeCheckM' (t' ** TC.UnOperator t t')
getUnOp op t = do
  let Just op' = tcUnOp op t
               -- TODO: make the error contain more info
               | Nothing => throwError TypeError
  pure op'



assertType : (t, t' : TC.LNGType) -> TC.Expr t' -> TypeCheckM' (TC.Expr t)
assertType t t' expr' = case decideEq t t' of
  Just prf => pure (rewrite prf in expr')

  -- TODO: make the error contain more info
  Nothing => throwError TypeError






mutual

  export
  typeCheckExpr : LNG.Expr -> TypeCheckM' (t ** TC.Expr t)

  typeCheckExpr (Lit lit) = case lit of
    LitBool b => pure (TC.TBool ** TC.Lit (TC.LitBool b))
    LitInt  i => pure (TC.TInt  ** TC.Lit (TC.LitInt  i))

  typeCheckExpr (Var id) = do
    t <- getVarType id
    pure (t ** TC.Var (MkVar t (MkVarId $ unIdent id)))

  typeCheckExpr (BinOperation op lhs rhs) = do
    (lt ** lhs') <- typeCheckExpr lhs
    (rt ** rhs') <- typeCheckExpr rhs
    (retT ** op') <- getBinOp op lt rt
    pure (retT ** TC.BinOperation op' lhs' rhs')

  typeCheckExpr (UnOperation op expr) = do
    (t ** expr') <- typeCheckExpr expr
    (retT ** op') <- getUnOp op t
    pure (retT ** TC.UnOperation op' expr')

  typeCheckExpr (Call fun args) = do
    (retT, paramTs) <- lift $ getFunTypes fun
    args <- typeCheckArgs paramTs args
    
    let fun' = MkFun retT paramTs (MkFunId $ unIdent fun)
    pure (retT ** TC.Call fun' args)

    where
      typeCheckArgs : (ts : List TC.LNGType) -> List Expr -> TypeCheckM' (DList TC.Expr ts)
      typeCheckArgs Nil Nil = pure Nil
      typeCheckArgs (t :: ts) (arg :: args) = do
        arg' <- typeCheckExprOfType t arg
        args' <- typeCheckArgs ts args
        pure (arg' :: args')
      
      -- TODO: make the error contain more info
      typeCheckArgs _ _ = throwError NumParamsMismatch


  export
  typeCheckExprOfType : (t : TC.LNGType) -> Expr -> TypeCheckM' (TC.Expr t)
  typeCheckExprOfType t expr = do
    (t' ** expr') <- typeCheckExpr expr
    assertType t t' expr'

