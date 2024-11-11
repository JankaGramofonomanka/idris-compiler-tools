module TypeCheck.Program

import Control.Monad.Either
import Control.Monad.State

import Data.DList
import LNG.Parsed                 as LNG
import LNG.TypeChecked            as TC
import Parse.Data.Position
import TypeCheck.Data.Context
import TypeCheck.Data.Error
import TypeCheck.Data.TypeCheckM
import TypeCheck.FunDef
import TypeCheck.Utils

mkFunMap : List (^LNG.FunDef) -> TypeCheckM FunCTX
mkFunMap l = foldlM declare FunCTX.empty l where

  declare : FunCTX -> ^LNG.FunDef -> TypeCheckM FunCTX
  declare ctx (p |^ decl) = do
  let Nothing = FunCTX.lookup (^^decl.funId) ctx
              | Just (p, _, _) => throwError $ fuctionAlreadyDefined decl.funId p

  pure (FunCTX.declare (tc' decl.retType) (map (tc' . fst) $ ^^decl.params) decl.funId ctx)


assertMain : (funcsPos : Pos)
          -> (funcs : List (^LNG.FunDef))
          -> TypeCheckM ()
assertMain p Nil = throwError $ noMainFunction p
assertMain p ((funPos |^ decl) :: funcs) = case ^^decl.funId of

  MkId "main" => do
    assertInt decl.retType
    assertEmptyParams decl.params
    pure ()

  _ => do
    assertMain p funcs
    pure ()

  where
    assertInt : ^LNG.LNGType -> TypeCheckM ()
    assertInt (p |^ TInt) = pure ()
    assertInt (p |^ t) = throwError $ typeError p TInt (tc t)

    assertEmptyParams : ^(List (^LNG.LNGType, ^Ident)) -> TypeCheckM ()
    assertEmptyParams (p |^ Nil) = pure ()
    assertEmptyParams (p |^ params) = throwError $ numParamsMismatch p 0 (length params)

export
typeCheckProgram : LNG.Program -> TypeCheckM TC.Program
typeCheckProgram prog = do

  assertMain (pos prog.funcs) (^^prog.funcs)

  funMap <- mkFunMap (^^prog.funcs)

  modify { funcs $= (`union` funMap)}

  funcs <- traverse typeCheckFunDecl (^^prog.funcs)

  pure $ TC.MkProgram { funcs  }

