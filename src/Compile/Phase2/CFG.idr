module Compile.Phase2.CFG

import Control.Monad.Either
import Control.Monad.State

import Data.Attached
import Data.DList
import Data.Typed

import Compile.Data.CompM
import Compile.Data.CBlock
import Compile.Data.Error
import Compile.Data.LLVM
import Compile.Phase2.Data.CompM'
import Compile.Phase2.Data.VarContext
import Compile.Phase2.Data.VarContext.Utils
import Compile.Phase2.CBlock
import Compile.Utils
import CFG
import LLVM
import LLVM.Generalized
import Utils

attachToEdges : (outs : List BlockLabel) -> VarCTX -> DList (:~: VarCTX) (lbl ~>> outs)
attachToEdges outs ctx = replicate' (lbl ~>) outs (\l => attach (lbl ~> l) ctx)

genRegsCBlock' : {ins, outs : List BlockLabel}
              -> (ctxs : DList (:~: VarCTX) (ins ~~> lbl))
              -> CBlock' Reg' rt lbl (Just ins) (Just outs)
              -> CompM (CBlock' Reg rt lbl (Just ins) (Just outs), DList (:~: VarCTX) (lbl ~>> outs))
genRegsCBlock' {lbl, ins, outs} ctxs blk = do
  SG ctx phis <- segregate ctxs
  (ctx', blk') <- runStateT (detach ctx) $ genRegsCBlock blk
  let ctxs' = attachToEdges outs ctx'
  pure (phis ++:| blk', ctxs')

genRegsCBlockU' : {outs : List BlockLabel}
               -> (ctx : (lbl :~: VarCTX))
               -> CBlock' Reg' rt lbl Nothing (Just outs)
               -> CompM (CBlock' Reg rt lbl Nothing (Just outs), DList (:~: VarCTX) (lbl ~>> outs))
genRegsCBlockU' {lbl, outs} ctx blk = do
  (ctx', blk') <- runStateT (detach ctx) $ genRegsCBlockU blk
  let ctxs' = attachToEdges outs ctx'
  pure (blk', ctxs')




export
genRegsCFG : (ctxs : DList (:~: VarCTX) ins)
          -> CFG (CBlock' Reg' rt) (Defined ins) (Defined outs)
          -> CompM (CFG (CBlock' Reg rt) (Defined ins) (Defined outs), DList (:~: VarCTX) outs)

genRegsCFG ctxs (SingleVertex v {vins = Nothing,  vouts = Just outs}) impossible
genRegsCFG ctxs (SingleVertex v {vins = Just ins, vouts = Nothing})   impossible
genRegsCFG ctxs (SingleVertex v {vins = Nothing,  vouts = Nothing})   impossible

genRegsCFG ctxs (SingleVertex v {vins = Just ins, vouts = Just outs}) = do
  (v', ctxs') <- genRegsCBlock' ctxs v
  let cfg = SingleVertex v' {vins = Just ins, vouts = Just outs}
  pure (cfg, ctxs')

genRegsCFG ctxs (Cycle node loop) = do

  pure ?hgr02

genRegsCFG ctxs (Series pre suc) = do
  (pre', ctxs') <- genRegsCFG ctxs pre
  (suc', ctxs'') <- genRegsCFG ctxs' suc
  pure (Series pre' suc', ctxs'')

genRegsCFG ctxs (LBranch node branch) = do
  (node', ctxs') <- genRegsCFG ctxs node
  let (lctxs, rctxs) = split ctxs'
  (branch', lctxs') <- genRegsCFG lctxs branch
  pure (LBranch node' branch', lctxs' ++ rctxs)

genRegsCFG ctxs (RBranch node branch) = do
  (node', ctxs') <- genRegsCFG ctxs node
  let (lctxs, rctxs) = split ctxs'
  (branch', rctxs') <- genRegsCFG rctxs branch
  pure (RBranch node' branch', lctxs ++ rctxs')

genRegsCFG ctxs (LMerge branch joint) = do
  let (lctxs, rctxs) = split ctxs
  (branch', lctxs') <- genRegsCFG lctxs branch
  (joint',  ctxs')  <- genRegsCFG (lctxs' ++ rctxs) joint
  pure (LMerge branch' joint', ctxs')

genRegsCFG ctxs (RMerge branch joint) = do
  let (lctxs, rctxs) = split ctxs
  (branch', rctxs') <- genRegsCFG rctxs branch
  (joint',  ctxs')  <- genRegsCFG (lctxs ++ rctxs') joint
  pure (RMerge branch' joint', ctxs')

genRegsCFG ctxs (Parallel left right) = do
  let (lctxs, rctxs) = split ctxs
  (left',  lctxs') <- genRegsCFG lctxs left
  (right', rctxs') <- genRegsCFG rctxs right
  pure (Parallel left' right', lctxs' ++ rctxs')

genRegsCFG ctxs (IFlip cfg) = do
  let (lctxs, rctxs) = split ctxs
  (cfg', ctxs') <- genRegsCFG (rctxs ++ lctxs) cfg
  pure (IFlip cfg', ctxs')

genRegsCFG ctxs (OFlip cfg) = do
  (cfg', ctxs') <- genRegsCFG ctxs cfg
  let (lctxs, rctxs) = split ctxs'
  pure (OFlip cfg', rctxs ++ lctxs)







export
genRegsCFGU : (ctx : (lbl :~: VarCTX))
          -> CFG (CBlock' Reg' rt) (Undefined lbl) (Defined outs)
          -> CompM (CFG (CBlock' Reg rt) (Undefined lbl) (Defined outs), DList (:~: VarCTX) outs)

genRegsCFGU ctx (SingleVertex v {vins = Nothing,  vouts = Just outs}) = do
  (v', ctxs') <- genRegsCBlockU' ctx v
  let cfg = SingleVertex v' {vins = Nothing, vouts = Just outs}
  pure (cfg, ctxs')

genRegsCFGU ctx (SingleVertex v {vins = Just ins})                 impossible
genRegsCFGU ctx (SingleVertex v {vins = Nothing, vouts = Nothing}) impossible
genRegsCFGU ctx (Cycle node loop)                                  impossible
genRegsCFGU ctx (LMerge branch joint)                              impossible
genRegsCFGU ctx (RMerge branch joint)                              impossible
genRegsCFGU ctx (Parallel left right)                              impossible
genRegsCFGU ctx (IFlip cfg)                                        impossible

genRegsCFGU ctx (Series pre suc) = do
  (pre', ctxs') <- genRegsCFGU ctx pre
  (suc', ctxs'') <- genRegsCFG ctxs' suc
  pure (Series pre' suc', ctxs'')

genRegsCFGU ctx (LBranch node branch) = do
  (node', ctxs') <- genRegsCFGU ctx node
  let (lctxs, rctxs) = split ctxs'
  (branch', lctxs') <- genRegsCFG lctxs branch
  pure (LBranch node' branch', lctxs' ++ rctxs)

genRegsCFGU ctx (RBranch node branch) = do
  (node', ctxs') <- genRegsCFGU ctx node
  let (lctxs, rctxs) = split ctxs'
  (branch', rctxs') <- genRegsCFG rctxs branch
  pure (RBranch node' branch', lctxs ++ rctxs')

genRegsCFGU ctx (OFlip cfg) = do
  (cfg', ctxs') <- genRegsCFGU ctx cfg
  let (lctxs, rctxs) = split ctxs'
  pure (OFlip cfg', rctxs ++ lctxs)

