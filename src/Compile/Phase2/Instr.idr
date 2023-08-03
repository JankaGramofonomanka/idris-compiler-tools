module Compile.Phase2.Instr


import Control.Monad.Either
import Control.Monad.State

import Data.DList
import Data.Typed

import Compile.Data.CompM
import Compile.Data.CBlock
import Compile.Data.Error
import Compile.Data.LLVM
import Compile.Phase2.Data.CompM'
import Compile.Phase2.Data.VarContext
import Compile.Phase2.Expr
import Compile.Utils
import LLVM
import LLVM.Generalized
import Utils


-- TODO Is this needed?
export
genRegsPhiInstr : PhiInstr Reg' ins -> CompM' (PhiInstr Reg ins)
genRegsPhiInstr (AssignPhi reg phi) = do
  phi' <- genRegsPhiExpr phi
  let Placeholder var = reg | R reg' => pure (AssignPhi reg' phi')

  reg' <- freshRegisterFor var
  pure (AssignPhi reg' phi')

export
genRegsSTInstr : STInstr Reg' -> CompM' (STInstr Reg)
genRegsSTInstr (Assign reg expr) = do
  expr' <- genRegsExpr expr
  let Placeholder var = reg | R reg' => pure (Assign reg' expr')

  reg' <- freshRegisterFor var
  pure (Assign reg' expr')

genRegsSTInstr (Exec expr) = Exec <$> genRegsExpr expr
genRegsSTInstr (Store val ptr) = Store <$> genRegsVal val <*> genRegsVal ptr
genRegsSTInstr Empty = pure Empty

export
genRegsCFInstr : CFInstr Reg' rt cfk -> CompM' (CFInstr Reg rt cfk)

genRegsCFInstr (Branch lbl) = pure (Branch lbl)

genRegsCFInstr (CondBranch cond thn els) = do
  cond' <- genRegsVal cond
  pure (CondBranch cond' thn els)

genRegsCFInstr (Ret val) = Ret <$> genRegsVal val

genRegsCFInstr RetVoid = pure RetVoid



