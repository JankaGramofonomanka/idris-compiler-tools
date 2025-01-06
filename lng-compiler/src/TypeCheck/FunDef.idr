module TypeCheck.FunDef

import Control.Monad.State
import Control.Monad.Either

import Data.List
import Data.SortedMap

import Data.DList
import LNG.Parsed as LNG
import LNG.TypeChecked as TC
import Parse.Data.Position
import TypeCheck.Data.Context
import TypeCheck.Data.Error
import TypeCheck.Data.TypeCheckM
import TypeCheck.Instr
import TypeCheck.Utils

mkVar' : (^LNG.LNGType, ^Ident) -> (t ** TC.Variable t)
mkVar' (t, id) = (tc' t ** mkVar (tc' t) (^^id))

export
typeCheckFunDecl : ^LNG.FunDef -> TypeCheckM TC.FunDef
typeCheckFunDecl (_ |^ funDecl) = do

  let retType = tc' funDecl.retType
  let (paramTypes ** paramIds) = unzipParamsWith mkVar' (^^funDecl.params)
  let funId = MkFun retType paramTypes $ mkFunId (^^funDecl.funId)

  let initCtx = foldr (uncurry $ VarCTX.declare . tc') empty (^^funDecl.params)

  (_, (bk ** body)) <- typeCheckInstr retType initCtx funDecl.body
  let Returning = bk
                | Simple => throwError $ missingReturnInstr (pos funDecl.body)

  let decl = TC.MkFunDef { funId   = funId
                         , retType = retType
                         , params  = paramIds
                         , body    = body
                         }

  pure decl


