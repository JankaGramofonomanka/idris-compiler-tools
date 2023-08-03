module Compile.Phase2.Expr

import Control.Monad.Either
import Control.Monad.State

import Data.DList

import Compile.Data.CompM
import Compile.Data.CBlock
import Compile.Data.Error
import Compile.Data.LLVM
import Compile.Phase2.Data.VarContext
import Compile.Utils
import LLVM
import LLVM.Generalized
import Utils

genRegsVal : VarCTX -> LLValue Reg' t -> CompM (LLValue Reg t)
genRegsVal ctx (Var (R reg)) = pure (Var reg)
genRegsVal ctx (Var (Placeholder var)) = do
  let Just val = VarCTX.lookup var ctx
               | Nothing => throwError (NoSuchVariable var)
  pure val

genRegsVal ctx (Lit lit)      = pure (Lit lit)
genRegsVal ctx (ConstPtr cst) = pure (ConstPtr cst)
genRegsVal ctx (Null t)       = pure (Null t)
  

genRegsExpr : VarCTX -> LLExpr Reg' t -> CompM (LLExpr Reg t)

genRegsExpr ctx (BinOperation op lhs rhs)
  = BinOperation op <$> genRegsVal ctx lhs <*> genRegsVal ctx rhs

genRegsExpr ctx (Call fun args)
  = Call <$> genRegsVal ctx fun <*> dtraverse (genRegsVal ctx) args

genRegsExpr ctx (GetElementPtr arr idx1 idx2)
  = GetElementPtr <$> genRegsVal ctx arr <*> genRegsVal ctx idx1 <*> genRegsVal ctx idx2

genRegsExpr ctx (ICMP cmp lhs rhs)
  = ICMP cmp <$> genRegsVal ctx lhs <*> genRegsVal ctx rhs

genRegsExpr ctx (Load ptr)
  = Load <$> genRegsVal ctx ptr

genRegsExpr ctx (BitCast val t2) = do
  val' <- genRegsVal ctx val
  pure (BitCast val' t2)


genRegsPhiExpr : VarCTX -> PhiExpr Reg' ins t -> CompM (PhiExpr Reg ins t)
genRegsPhiExpr ctx (Phi t Nil) = pure (Phi t Nil)
genRegsPhiExpr ctx (Phi t ((lbl, val) :: kvs)) = do

  val' <- genRegsVal ctx val
  phi <- genRegsPhiExpr ctx (Phi t kvs)
  
  pure (addInput lbl val' phi)
