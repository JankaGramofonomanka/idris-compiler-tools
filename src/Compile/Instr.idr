module Compile.Instr

import Control.Monad.State

import Data.Some

import LNG
import LLVM

import Compile.Tools
import Compile.Expr



{-
Add phi assignments and a terminating instruction if necessary to the blocks
that are a result of compilation of a sub instruction and add the blocks to the
control flow graph
-}
-- TODO: why do we need `labelIn`?
-- Perhaps, to lookup values to assign in phis instructions
handleBranchResult : CompileResult os
                  -> Some BlockLabel
                  -> BlockLabel NonEntry
                  -> CompM ()
handleBranchResult res labelIn labelOut = case res of
  SingleBLKC (cfk ** blk) => do

    -- TODO: phis
    addBlock $ ?hbr_phis1 |++> blk

  SingleBLKO blk => do
  
    -- TODO: phis
    addBlock $ ?hbr_phis2 |++> blk <+| Branch labelOut
    
  DoubleBLK (cfk ** blkIn) (ik ** lbl ** ins ** blkOut) => do
  
    -- TODO: phis
    addBlock $ ?hbr_phis3 |++> blkIn
    addBlock $ blkOut <+| Branch labelOut

















-- Instr  * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
mutual
  InstrOutStatus : Instr -> OutStatus'
  InstrOutStatus (Block is)     = InstrsOutStatus is

  InstrOutStatus (Assign v e)   = Open
  InstrOutStatus (If c t)       = Open
  InstrOutStatus (IfElse c t e) = OpenOr (InstrOutStatus t) (InstrOutStatus e)

  InstrOutStatus (Return e)     = Closed
  InstrOutStatus RetVoid        = Closed



  InstrsOutStatus : List Instr -> OutStatus'
  InstrsOutStatus [] = Open
  InstrsOutStatus (instr :: instrs) = ClosedOr (InstrOutStatus instr) (InstrsOutStatus instrs)




compileInstr : (labelIn : Some BlockLabel)
            -> (instr : Instr)
            -> let
                status = InstrOutStatus instr
              in CompM (LabelResult status, CompileResult status)


-- Block ----------------------------------------------------------------------
compileInstr labelIn (Block instrs) = compile' labelIn instrs where

  mutual

    compile' : Some BlockLabel
            -> (instrs : List Instr)
            -> CompM (LabelResult $ InstrsOutStatus instrs, CompileResult $ InstrsOutStatus instrs)

    compile' labelIn [] = pure (LastLabel labelIn, initCR)

    compile' labelIn (instr :: instrs) = do
      (labelRes, res) <- compileInstr labelIn instr
      handleRes labelRes res instrs
    
      
    handleRes : LabelResult os
             -> CompileResult os
             -> (instrs : List Instr)
             -> CompM ( LabelResult $ ClosedOr os (InstrsOutStatus instrs)
                      , CompileResult $ ClosedOr os (InstrsOutStatus instrs)
                      )
    handleRes NoLabel res instrs = pure (NoLabel, res)
    handleRes (LastLabel lbl) res instrs = do
      (labelRes, res') <- compile' lbl instrs
      res'' <- combineCR res res'
      pure (labelRes, res'')
    



-- Assign ---------------------------------------------------------------------
compileInstr labelIn (Assign var expr) = do
  (labelRes, res, val) <- compileExpr labelIn expr
  
  let res' = mapOO (assign var val) res

  pure (labelRes, res')
  

-- If -------------------------------------------------------------------------
compileInstr labelIn (If cond instrThen) = do

  -- TODO: use `ifology`
  (LastLabel lastCondLabel, condRes, val) <- compileExpr labelIn cond
  labelThen <- freshLabel
  labelPost <- freshLabel

  SingleBLKC inBLK <- closeCR (CondBranch val labelThen labelPost) condRes

  (thenLabelRes, thenRes) <- compileInstr (MkSome labelThen) instrThen
  
  handleBranchResult thenRes lastCondLabel labelPost
  
  let inputs = MkInputs $ lastCondLabel :: listify thenLabelRes

  -- TODO: phis
  let postBLK : CBlock (InClosed NonEntry labelPost inputs) OutOpen
      postBLK = ?phis0 |++> initCBlock

  pure
    $ ( LastLabel $ MkSome labelPost
      , DoubleBLK inBLK (NonEntry ** labelPost ** inputs ** postBLK)
      )
  



-- IfElse ---------------------------------------------------------------------
compileInstr labelIn (IfElse cond instrThen instrElse) = do

  -- TODO: use `ifology`
  (LastLabel lastCondLabel, condRes, val) <- compileExpr labelIn cond
  labelThen <- freshLabel
  labelElse <- freshLabel
  labelPost <- freshLabel

  SingleBLKC inBLK <- closeCR (CondBranch val labelThen labelElse) condRes

  (thenLabelRes, thenRes) <- compileInstr (MkSome labelThen) instrThen
  (elseLabelRes, elseRes) <- compileInstr (MkSome labelElse) instrElse

  handleBranchResult thenRes lastCondLabel labelPost
  handleBranchResult elseRes lastCondLabel labelPost


  pure $ finishIfThenElse inBLK thenLabelRes elseLabelRes labelPost
  
  where
    
    finishIfThenElse : (cfk ** CBlock InOpen $ OutClosed cfk)
                    -> LabelResult os
                    -> LabelResult os'
                    -> BlockLabel NonEntry
                    -> (LabelResult (OpenOr os os'), CompileResult (OpenOr os os'))
    
    finishIfThenElse inBLK NoLabel NoLabel labelPost = (NoLabel, SingleBLKC inBLK)
    
    finishIfThenElse inBLK NoLabel (LastLabel lbl) labelPost = let
      
      -- TODO: phis
      inputs = MkInputs [lbl]
      postBLK : CBlock (InClosed NonEntry labelPost inputs) OutOpen
      postBLK = ?hphis1 |++> initCBlock
      
      in (LastLabel $ MkSome labelPost, DoubleBLK inBLK (NonEntry ** labelPost ** inputs ** postBLK))

    finishIfThenElse inBLK (LastLabel lbl) NoLabel labelPost = let
      
      -- TODO: phis
      inputs = MkInputs [lbl]
      postBLK : CBlock (InClosed NonEntry labelPost inputs) OutOpen
      postBLK = ?hphis2 |++> initCBlock
      
      in (LastLabel $ MkSome labelPost, DoubleBLK inBLK (NonEntry ** labelPost ** inputs ** postBLK))

    finishIfThenElse inBLK (LastLabel labelThen) (LastLabel labelElse) labelPost = let
      
      -- TODO: phis
      inputs = MkInputs [labelThen, labelElse]
      postBLK : CBlock (InClosed NonEntry labelPost inputs) OutOpen
      postBLK = ?hphis3 |++> initCBlock
      
      in (LastLabel $ MkSome labelPost, DoubleBLK inBLK (NonEntry ** labelPost ** inputs ** postBLK))

-- Return ---------------------------------------------------------------------
compileInstr labelIn (Return expr) = do
  (_, res, val) <- compileExpr labelIn expr
  
  res' <- closeCR (Ret val) res
  pure (NoLabel, res')

-- RetVoid --------------------------------------------------------------------
compileInstr labelIn RetVoid = do
  res <- closeCR RetVoid initCR
  pure (NoLabel, res)

