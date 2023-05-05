module TypeCheck.Program

import Control.Monad.Either
import Control.Monad.State

import Data.SortedMap

import LNG.Parsed                 as LNG
import LNG.TypeChecked            as TC
import TypeCheck.FunDecl
import TypeCheck.Tools.Context
import TypeCheck.Tools.Other
import TypeCheck.Tools.TypeCheckM

mkFunMap : List LNG.FunDecl -> FunCTX
mkFunMap = foldr (uncurry insert . idAndTypes) SortedMap.empty where
  idAndTypes decl = (decl.funId, (tc decl.retType, map (tc . fst) decl.params))

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

typeCheckProgram : LNG.Program -> TypeCheckM TC.Program
typeCheckProgram prog = do

  let funMap = mkFunMap prog.funcs

  funcs' <- traverse typeCheckFunDecl prog.funcs

  (main, funcs'') <- findMain funcs'

  pure $ TC.MkProgram { main, funcs = funcs'' }


