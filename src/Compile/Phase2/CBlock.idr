module Compile.Phase2.CBlock

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
import Compile.Phase2.Instr
import Compile.Utils
import CFG
import LLVM
import LLVM.Generalized
import Utils

genRegsCBlock : VarCTX -> CBlock' Reg' rt lbl (Just ins) (Just outs) -> CompM (CBlock' Reg rt lbl (Just ins) (Just outs))
genRegsCBlock ctx (MkBB { theLabel, phis, body, term }) = do
  (ctx, phis') <- runStateT ctx $ traverse (onFirstM genRegsPhiInstr) phis
  (ctx, body') <- runStateT ctx $ traverse (onFirstM genRegsSTInstr) body
  (ctx, term') <- runStateT ctx $ genRegsCFInstr term

  pure $ MkBB { theLabel, phis = phis', body = body', term = term' }

