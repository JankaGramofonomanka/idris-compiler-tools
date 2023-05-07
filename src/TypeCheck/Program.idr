module TypeCheck.Program

import Control.Monad.Either
import Control.Monad.State

import Data.SortedMap

import LNG.Data.Position
import LNG.Parsed                 as LNG
import LNG.TypeChecked            as TC
import TypeCheck.Data.Context
import TypeCheck.Data.TypeCheckM
import TypeCheck.FunDecl
import TypeCheck.Utils

import Utils

mkFunMap : PosList LNG.FunDecl -> TypeCheckM FunCTX
mkFunMap l = posFoldlM declare FunCTX.empty l where
  
  declare : FunCTX -> ^FunDecl -> TypeCheckM FunCTX
  declare ctx (p |^ decl) = do
  let Nothing = FunCTX.lookup (^^decl.funId) ctx
              | Just (p, _, _) => throwError $ fuctionAlreadyDefined decl.funId p
  
  pure (FunCTX.declare (tc' decl.retType) (map (tc' . fst) decl.params) decl.funId ctx)


typeCheckFunDecl' : ^LNG.FunDecl -> TypeCheckM (^(t ** ts ** fun ** TC.FunDecl t ts fun))
typeCheckFunDecl' decl = do
  decl' <- typeCheckFunDecl decl
  pure (pos decl |^ decl')

findMain : PosList (t ** ts ** fun ** FunDecl t ts fun)
        -> TypeCheckM ( FunDecl TVoid [] (MkFunId "main")
                      , List (t ** ts ** fun ** FunDecl t ts fun)
                      )
findMain (Nil p) = throwError $ noMainFunction p
findMain ((funPos |^ (t ** ts ** fun ** decl)) :: funcs) = case fun of
  MkFunId "main" => case t of
  
    TVoid => case ts of
      [] => pure {f = TypeCheckM} (decl, unPosList funcs)
      _ => throwError $ numParamsMismatch funPos 0 (length ts)
  
    _ => throwError $ typeError funPos TVoid t
  
  _ => do
    (main, funcs') <- findMain funcs
    pure (main, (t ** ts ** fun ** decl) :: funcs')

export
typeCheckProgram : LNG.Program -> TypeCheckM TC.Program
typeCheckProgram prog = do

  funMap <- mkFunMap prog.funcs

  funcs' <- posTraverse typeCheckFunDecl' prog.funcs

  (main, funcs'') <- findMain funcs'

  pure $ TC.MkProgram { main, funcs = funcs'' }


