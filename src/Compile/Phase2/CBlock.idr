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

export
genRegsCBlock : CBlock' Reg' rt lbl (Just ins) (Just outs) -> CompM' (CBlock' Reg rt lbl (Just ins) (Just outs))
genRegsCBlock (MkBB { theLabel, phis, body, term }) = do
  phis' <- traverse (onFirstM genRegsPhiInstr) phis
  body' <- traverse (onFirstM genRegsSTInstr) body
  term' <- genRegsCFInstr term

  pure $ MkBB { theLabel, phis = phis', body = body', term = term' }

export
genRegsCBlockU : CBlock' Reg' rt lbl Nothing (Just outs) -> CompM' (CBlock' Reg rt lbl Nothing (Just outs))
genRegsCBlockU (MkBB { theLabel, phis, body, term }) = do
  body' <- traverse (onFirstM genRegsSTInstr) body
  term' <- genRegsCFInstr term

  pure $ MkBB { theLabel, phis = (), body = body', term = term' }

