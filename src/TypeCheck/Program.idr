module TypeCheck.Program

import Control.Monad.Either
import Control.Monad.State

import Data.SortedMap

import LNG.Parsed                 as LNG
import LNG.TypeChecked            as TC
import Parse.Data.Position
import TypeCheck.Data.Context
import TypeCheck.Data.Error
import TypeCheck.Data.TypeCheckM
import TypeCheck.FunDecl
import TypeCheck.Utils

import Utils

mkFunMap : List (^LNG.FunDecl) -> TypeCheckM FunCTX
mkFunMap l = foldlM declare FunCTX.empty l where
  
  declare : FunCTX -> ^FunDecl -> TypeCheckM FunCTX
  declare ctx (p |^ decl) = do
  let Nothing = FunCTX.lookup (^^decl.funId) ctx
              | Just (p, _, _) => throwError $ fuctionAlreadyDefined decl.funId p
  
  pure (FunCTX.declare (tc' decl.retType) (map (tc' . fst) $ ^^decl.params) decl.funId ctx)


typeCheckFunDecl' : ^LNG.FunDecl -> TypeCheckM (^(t ** ts ** fun ** TC.FunDecl t ts fun))
typeCheckFunDecl' decl = do
  decl' <- typeCheckFunDecl decl
  pure (pos decl |^ decl')

findMain : (funcsPos : Pos)
        -> (funcs : List (^(t ** ts ** fun ** FunDecl t ts fun)))
        -> TypeCheckM ( FunDecl TVoid [] (MkFunId "main")
                      , List (t ** ts ** fun ** FunDecl t ts fun)
                      )
findMain p Nil = throwError $ noMainFunction p
findMain p ((funPos |^ (t ** ts ** fun ** decl)) :: funcs) = case fun of
  MkFunId "main" => case t of
  
    TVoid => case ts of
      [] => pure {f = TypeCheckM} (decl, map (^^) funcs)
      _ => throwError $ numParamsMismatch funPos 0 (length ts)
  
    _ => throwError $ typeError funPos TVoid t
  
  _ => do
    (main, funcs') <- findMain p funcs
    pure (main, (t ** ts ** fun ** decl) :: funcs')

export
typeCheckProgram : LNG.Program -> TypeCheckM TC.Program
typeCheckProgram prog = do

  funMap <- mkFunMap (^^prog.funcs)

  funcs' <- traverse typeCheckFunDecl' (^^prog.funcs)

  (main, funcs'') <- findMain (pos prog.funcs) funcs'

  pure $ TC.MkProgram { main, funcs = funcs'' }

