module TypeCheck.Program

import Control.Monad.Either
import Control.Monad.State

import Data.SortedMap

import LNG.Parsed                 as LNG
import LNG.TypeChecked            as TC
import TypeCheck.Data.Context
import TypeCheck.Data.TypeCheckM
import TypeCheck.FunDecl
import TypeCheck.Utils

import Utils

mkFunMap : List (^LNG.FunDecl) -> FunCTX
mkFunMap = foldr (uncurry3 FunCTX.declare . idAndTypes) FunCTX.empty where
  idAndTypes : ^LNG.FunDecl -> (TC.LNGType, List TC.LNGType, ^Ident)
  idAndTypes (p |^ decl) = (tc' decl.retType, map (tc' . fst) decl.params, decl.funId)

findMain : List (t ** ts ** fun ** FunDecl t ts fun)
        -> TypeCheckM ( FunDecl TVoid [] (MkFunId "main")
                      , List (t ** ts ** fun ** FunDecl t ts fun)
                      )
findMain Nil = throwError NoMainFunction
findMain ((t ** ts ** fun ** decl) :: funcs) = case fun of
  MkFunId "main" => case t of
  
    TVoid => case ts of
  
      [] => pure (decl, funcs)
  
      -- TODO: make the error contain more info
      _ => throwError TypeError
  
    -- TODO: make the error contain more info
    _ => throwError TypeError
  
  _ => do
    (main, funcs') <- findMain funcs
    pure (main, (t ** ts ** fun ** decl) :: funcs')

export
typeCheckProgram : LNG.Program -> TypeCheckM TC.Program
typeCheckProgram prog = do

  let funMap = mkFunMap prog.funcs

  funcs' <- traverse typeCheckFunDecl prog.funcs

  (main, funcs'') <- findMain funcs'

  pure $ TC.MkProgram { main, funcs = funcs'' }


