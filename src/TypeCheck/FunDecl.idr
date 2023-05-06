module TypeCheck.FunDecl

import Control.Monad.State
import Control.Monad.Either

import Data.List
import Data.SortedMap

import Data.DList
import Data.The
import LNG.Data.Position
import LNG.Parsed as LNG
import LNG.TypeChecked as TC
import TypeCheck.Data.Context
import TypeCheck.Data.TypeCheckM
import TypeCheck.Instr
import TypeCheck.Utils

import Utils

mkVar' : (^LNG.LNGType, ^Ident) -> (t ** TC.Variable t)
mkVar' (t, id) = (tc' t ** mkVar (tc' t) (^^id))

export
typeCheckFunDecl : ^LNG.FunDecl -> TypeCheckM (t ** ts ** fun ** TC.FunDecl t ts fun)
typeCheckFunDecl (_ |^ funDecl) = do
  
  let retType = tc' funDecl.retType
  let (paramTypes ** paramIds) = dunzipWith mkVar' funDecl.params
  let funId = mkFunId (^^funDecl.funId)

  let initCtx = foldr (uncurry $ VarCTX.declare . tc') empty funDecl.params

  (_, (bk ** body)) <- typeCheckInstr retType initCtx funDecl.body
  let Returning retType = bk
                        | Simple => throwError $ missingReturnInstr (pos funDecl.body)

  let decl = TC.MkFunDecl { theId       = MkThe funId
                          , theRetType  = MkThe retType
                          , params      = paramIds
                          , body        = body
                          }

  pure (retType ** paramTypes ** funId ** decl)
  

