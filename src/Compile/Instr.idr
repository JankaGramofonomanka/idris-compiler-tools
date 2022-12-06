module Compile.Instr

import Control.Monad.State

import Data.Some

import LNG
import LLVM

import Compile.Tools
import Compile.Tools.CBlock
import Compile.Tools.CompileResult
import Compile.Tools.CompM
import Compile.Expr

{-
Add phi assignments and a terminating instruction if necessary to the blocks
that are a result of compilation of a sub instruction and add the blocks to the
control flow graph
-}
-- TODO: why do we need `labelIn`?
-- Perhaps, to lookup values to assign in phis instructions
handleBranchResult : CompileResult' lbl os
                  -> BlockLabel
                  -> BlockLabel
                  -> CompM ()
handleBranchResult (CRC res) labelIn labelOut = case res of
  
  SingleBLKC (cfk ** blk) => do

    -- TODO: phis
    addBlock $ ?hbr_phis1 |++> blk


handleBranchResult (CRO (lbl ** res)) labelIn labelOut = case res of
  
  SingleBLKO blk => do
  
    -- TODO: phis
    addBlock $ ?hbr_phis2 |++> blk <+| Branch labelOut
    
  DoubleBLK (cfk ** blkIn) (ins ** blkOut) => do
  
    -- TODO: phis
    addBlock $ ?hbr_phis3 |++> blkIn
    addBlock $ blkOut <+| Branch labelOut















mutual
  InstrCR : Instr -> CRType
  InstrCR (Block is)     = InstrsCR is

  InstrCR (Assign v e)   = Open
  InstrCR (If c t)       = Open
  InstrCR (IfElse c t e) = OpenOr (InstrCR t) (InstrCR e)

  InstrCR (Return e)     = Closed
  InstrCR RetVoid        = Closed



  InstrsCR : List Instr -> CRType
  InstrsCR [] = Open
  InstrsCR (instr :: instrs) = ClosedOr (InstrCR instr) (InstrsCR instrs)



compileInstr : (labelIn : BlockLabel)
            -> (instr : Instr)
            -> CompM (CompileResult' labelIn $ InstrCR instr)


-- Block ----------------------------------------------------------------------
compileInstr labelIn (Block instrs) = compile' labelIn instrs where

  mutual

    compile' : (labelIn : BlockLabel)
            -> (instrs : List Instr)
            -> CompM (CompileResult' labelIn $ InstrsCR instrs)
    
    compile' labelIn [] = pure (initCR' labelIn)
    compile' labelIn (instr :: instrs) = do
      res <- compileInstr labelIn instr
      handleRes res instrs
      
    handleRes : {labelIn : BlockLabel}
             -> CompileResult' labelIn os
             -> (instrs : List Instr)
             -> CompM (CompileResult' labelIn $ ClosedOr os (InstrsCR instrs))
    handleRes (CRC res) instrs = pure (CRC res)
    handleRes (CRO (lbl ** res)) instrs = do
      res' <- compile' lbl instrs
      combineCR' res res'
    


-- Assign ---------------------------------------------------------------------
compileInstr labelIn (Assign var expr) = do
  ((lbl ** res), val) <- compileExpr labelIn expr
  
  let res' = mapOO (assign var val) res

  pure $ CRO (lbl ** res')
  
  





-- If -------------------------------------------------------------------------
compileInstr labelIn (If cond instrThen) = do

  -- TODO: use `ifology`
  ((lastCondLabel ** condRes), val) <- compileExpr labelIn cond
  labelThen <- freshLabel
  labelPost <- freshLabel

  SingleBLKC inBLK <- closeCR (CondBranch val labelThen labelPost) condRes

  thenRes <- compileInstr labelThen instrThen
  
  handleBranchResult thenRes lastCondLabel labelPost
  
  let postInputs = MkInputs $ lastCondLabel :: getOutputs thenRes
  let PostIS : InStatus; PostIS = InClosed postInputs

  ---- TODO: phis
  let postBLK : CBlock labelPost PostIS OutOpen
      postBLK = ?phis0 |++> initCBlock

  pure $ CRO (labelPost ** DoubleBLK inBLK (postInputs ** postBLK))

  


-- IfElse ---------------------------------------------------------------------
compileInstr labelIn (IfElse cond instrThen instrElse) = do

  -- TODO: use `ifology`
  ((lastCondLabel ** condRes), val) <- compileExpr labelIn cond
  labelThen <- freshLabel
  labelElse <- freshLabel
  labelPost <- freshLabel

  SingleBLKC inBLK <- closeCR (CondBranch val labelThen labelElse) condRes

  thenRes <- compileInstr labelThen instrThen
  elseRes <- compileInstr labelElse instrElse

  handleBranchResult thenRes lastCondLabel labelPost
  handleBranchResult elseRes lastCondLabel labelPost

  pure $ finishIfThenElse inBLK (getOutLabel thenRes) (getOutLabel elseRes) labelPost
  
  where
    
    finishIfThenElse : (cfk ** CBlock lbl InOpen $ OutClosed cfk)
                    -> (thenOutLabel : MLabel os)
                    -> (elseOutLabel : MLabel os')
                    -> (labelPost : BlockLabel)
                    -> CompileResult' lbl (OpenOr os os')

    finishIfThenElse inBLK NoLabel NoLabel labelPost = CRC $ SingleBLKC inBLK

    finishIfThenElse inBLK NoLabel (YesLabel lbl) labelPost = let
      
      -- TODO: phis
      inputs = MkInputs [lbl]
      postBLK : CBlock labelPost (InClosed inputs) OutOpen
      postBLK = ?hphis1 |++> initCBlock
      
      in CRO (labelPost ** DoubleBLK inBLK (inputs ** postBLK))
    
    finishIfThenElse inBLK (YesLabel lbl) NoLabel labelPost = let
      
      -- TODO: phis
      inputs = MkInputs [lbl]
      postBLK : CBlock labelPost (InClosed inputs) OutOpen
      postBLK = ?hphis2 |++> initCBlock
      
      in CRO (labelPost ** DoubleBLK inBLK (inputs ** postBLK))

    finishIfThenElse inBLK (YesLabel labelThen) (YesLabel labelElse) labelPost = let
      
      -- TODO: phis
      inputs = MkInputs [labelThen, labelElse]
      postBLK : CBlock labelPost (InClosed inputs) OutOpen
      postBLK = ?hphis3 |++> initCBlock
      
      in CRO (labelPost ** DoubleBLK inBLK (inputs ** postBLK))




-- Return ---------------------------------------------------------------------
compileInstr labelIn (Return expr) = do
  ((_ ** res), val) <- compileExpr labelIn expr
  
  res' <- closeCR (Ret val) res
  pure (CRC res')

-- RetVoid --------------------------------------------------------------------
compileInstr labelIn RetVoid = do
  res <- closeCR RetVoid initCR
  pure (CRC res)




compileInstr labelIn instr = ?hinstr









