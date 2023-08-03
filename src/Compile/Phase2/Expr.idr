module Compile.Phase2.Expr

import Control.Monad.Either
import Control.Monad.State

import Data.DList

import Compile.Data.CompM
import Compile.Data.CBlock
import Compile.Data.Error
import Compile.Data.LLVM
import Compile.Phase2.Data.VarContext
import Compile.Phase2.Data.CompM'
import Compile.Utils
import LLVM
import LLVM.Generalized
import Utils

export
genRegsVal : LLValue Reg' t -> CompM' (LLValue Reg t)
genRegsVal (Var (R reg)) = pure (Var reg)
genRegsVal (Var (Placeholder var)) = getValue var

genRegsVal (Lit lit)      = pure (Lit lit)
genRegsVal (ConstPtr cst) = pure (ConstPtr cst)
genRegsVal (Null t)       = pure (Null t)
  
export
genRegsExpr : LLExpr Reg' t -> CompM' (LLExpr Reg t)

genRegsExpr (BinOperation op lhs rhs)
  = BinOperation op <$> genRegsVal lhs <*> genRegsVal rhs

genRegsExpr (Call fun args)
  = Call <$> genRegsVal fun <*> dtraverse (genRegsVal) args

genRegsExpr (GetElementPtr arr idx1 idx2)
  = GetElementPtr <$> genRegsVal arr <*> genRegsVal idx1 <*> genRegsVal idx2

genRegsExpr (ICMP cmp lhs rhs)
  = ICMP cmp <$> genRegsVal lhs <*> genRegsVal rhs

genRegsExpr (Load ptr)
  = Load <$> genRegsVal ptr

genRegsExpr (BitCast val t2) = do
  val' <- genRegsVal val
  pure (BitCast val' t2)

export
genRegsPhiExpr : PhiExpr Reg' ins t -> CompM' (PhiExpr Reg ins t)
genRegsPhiExpr (Phi t Nil) = pure (Phi t Nil)
genRegsPhiExpr (Phi t ((lbl, val) :: kvs)) = do

  val' <- genRegsVal val
  phi <- genRegsPhiExpr (Phi t kvs)
  
  pure (addInput lbl val' phi)
