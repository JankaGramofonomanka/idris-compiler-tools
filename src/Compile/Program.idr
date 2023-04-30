module Compile.Program

import Control.Monad.State

import Data.DList
import Data.DMap
import Data.GCompare
import LNG
import LLVM
import Compile.FunDecl
import Compile.Tools
import Compile.Tools.CompM


mkFunMap : List (t ** ts ** fun ** FunDecl t ts fun) -> DMap FunKey FunVal
mkFunMap l = foldr insertFun DMap.empty l where

  mkFunPtr : FunId t ts -> LLValue (Ptr $ FunType (GetLLType t) (map GetLLType ts))
  -- TODO: was there any requirement about how to name functions in LLVM?
  mkFunPtr (MkFunId funId) = ConstPtr (MkConst funId)

  insertFun : (t ** ts ** fun ** FunDecl t ts fun)
           -> DMap FunKey FunVal
           -> DMap FunKey FunVal
  insertFun (t ** ts ** funId ** _) = DMap.insert {v = (t, ts)} (MkFun t ts funId) (mkFunPtr funId)

  

compileFunDecl' : (t ** ts ** fun ** FunDecl t ts fun)
               -> CompM (retType ** paramTypes ** FunDecl retType paramTypes)
compileFunDecl' (t ** ts ** fun ** decl) = do
  decl' <- compileFunDecl decl
  pure (GetLLType t ** map GetLLType ts ** decl')

export
compileProgram : LNG.Program -> CompM LLVM.Program
compileProgram (MkProgram { main, funcs }) = do

  let funMap = mkFunMap ((TVoid ** [] ** MkFunId "main" ** main) :: funcs)
  modify { funcs := funMap }

  mainDecl <- compileFunDecl main
  funcDecls <- traverse compileFunDecl' funcs

  let mainDecl' = (Void ** [] ** mainDecl)
  pure (MkProgram { funcs = (mainDecl' :: funcDecls) })
