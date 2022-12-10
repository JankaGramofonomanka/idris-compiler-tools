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

import CFG
import Utils



{-
Add phi assignments and a terminating instruction if necessary to the blocks
that are a result of compilation of a sub instruction and add the blocks to the
control flow graph
-}
handleBranchResult : CompileResult lbl crt
                  -> (labelIn : BlockLabel)
                  -> (labelPost : BlockLabel)
                  -> CompM (  outs
                           ** ( CFG CBlock (Ends [labelIn ~> lbl]) (Ends $ map (~> labelPost) outs)
                              , Compatible crt outs
                              )
                           )

handleBranchResult (CRC g) labelIn labelPost = let

  -- TODO: phis
  g' = mapIn {ins = Just [labelIn]} (?hbr_phis1 |++>) g

  in pure ([] ** (g', CompatClosed))

handleBranchResult (CRO (lbl' ** g)) labelIn labelPost = let

  -- TODO: phis
  g' = mapOut {outs = Just [labelPost]} (<+| Branch labelPost)
     $ mapIn  {ins  = Just [labelIn]}   (?hbr_phis2 |++>)
     $ g
  
  
  in pure ([lbl'] ** (g', CompatOpen))











mutual
  InstrCR : Instr -> CRType
  InstrCR (Block is)      = InstrsCR is

  InstrCR (Assign v e)    = Open
  InstrCR (If c t)        = Open
  InstrCR (IfElse c t e)  = OpenOr (InstrCR t) (InstrCR e)
  InstrCR (While c l)     = Open

  InstrCR (Return e)      = Closed
  InstrCR RetVoid         = Closed



  InstrsCR : List Instr -> CRType
  InstrsCR [] = Open
  InstrsCR (instr :: instrs) = ClosedOr (InstrCR instr) (InstrsCR instrs)



compileInstr : (labelIn : BlockLabel)
            -> (instr : Instr)
            -> CompM (CompileResult labelIn $ InstrCR instr)


-- Block ----------------------------------------------------------------------
compileInstr labelIn (Block instrs) = compile' labelIn instrs where

  mutual

    compile' : (labelIn : BlockLabel)
            -> (instrs : List Instr)
            -> CompM (CompileResult labelIn $ InstrsCR instrs)
    compile' labelIn [] = pure (initCR labelIn)
    compile' labelIn (instr :: instrs) = do
      res <- compileInstr labelIn instr
      handleRes res instrs
      
    handleRes : {0 labelIn : BlockLabel}
             -> CompileResult labelIn crt
             -> (instrs : List Instr)
             -> CompM (CompileResult labelIn $ ClosedOr crt (InstrsCR instrs))
    handleRes (CRC g) instrs = pure (CRC g)
    handleRes (CRO (lbl ** g)) instrs = do
      res <- compile' lbl instrs
      pure $ combineCR g res
    


-- Assign ---------------------------------------------------------------------
compileInstr labelIn (Assign var expr) = do
  ((lbl ** g), val) <- compileExpr labelIn expr
  
  let g' = mapOut {outs = Undefined} (assign var val) g

  pure $ CRO (lbl ** g')
  
  





-- If -------------------------------------------------------------------------
compileInstr labelIn (If cond instrThen) = do

  -- TODO: use `ifology`
  ((condLabel ** condG), val) <- compileExpr labelIn cond
  labelThen <- freshLabel
  labelPost <- freshLabel

  let condG' = mapOut {outs = Just [labelThen, labelPost]} (<+| CondBranch val labelThen labelPost) condG
  
  thenRes <- compileInstr labelThen instrThen
  (thenOuts ** (thenG, _)) <- handleBranchResult thenRes condLabel labelPost

  let branches : CFG CBlock
                  (Ends [condLabel ~> labelThen, condLabel ~> labelPost])
                  (Ends $ map (~> labelPost) (thenOuts ++ [condLabel]))

      branches = rewrite map_append {f = (~> labelPost)} thenOuts condLabel
                 in Parallel thenG Empty

  -- TODO: phis
  let postBLK : CBlock labelPost (Just $ thenOuts ++ [condLabel]) Undefined
      postBLK = ?phis0 |++> initCBlock
  
  let postG : CFG CBlock (Ends $ map (~> labelPost) (thenOuts ++ [condLabel])) (Undefined labelPost)
      postG = SingleVertex {vins = Just (thenOuts ++ [condLabel]), vouts = Undefined} postBLK
  
  let final = Connect condG' (Connect branches postG)
  
  pure $ CRO (labelPost ** final)
  



-- IfElse ---------------------------------------------------------------------
compileInstr labelIn (IfElse cond instrThen instrElse) = do

  -- TODO: use `ifology`
  ((condLabel ** condG), val) <- compileExpr labelIn cond
  labelThen <- freshLabel
  labelElse <- freshLabel
  labelPost <- freshLabel

  let condG' = mapOut {outs = Just [labelThen, labelElse]} (<+| CondBranch val labelThen labelElse) condG
  thenRes <- compileInstr labelThen instrThen
  elseRes <- compileInstr labelElse instrElse

  (thenOuts ** (thenG, compatT)) <- handleBranchResult thenRes condLabel labelPost
  (elseOuts ** (elseG, compatE)) <- handleBranchResult elseRes condLabel labelPost

  let branches : CFG CBlock
                  (Ends [condLabel ~> labelThen, condLabel ~> labelElse])
                  (Ends $ map (~> labelPost) (thenOuts ++ elseOuts))
      branches = rewrite map_concat {f = (~> labelPost)} thenOuts elseOuts
                 in Parallel thenG elseG

  let condAndBranches = Connect condG' branches

  finishIfThenElse thenOuts compatT elseOuts compatE labelPost condAndBranches
  
  where
    finishIfThenElse : (thenOuts : List BlockLabel)
                    -> (0 compatT : Compatible crt thenOuts)
                    -> (elseOuts : List BlockLabel)
                    -> (0 compatE : Compatible crt' elseOuts)
                    -> (labelPost : BlockLabel)
                    -> CFG CBlock (Undefined lbl) (Ends $ map (~> labelPost) (thenOuts ++ elseOuts))
                    -> CompM (CompileResult lbl (OpenOr crt crt'))

    finishIfThenElse [] CompatClosed [] CompatClosed labelPost g = pure (CRC g)

    finishIfThenElse [] CompatClosed [l'] CompatOpen labelPost g = do
      
      let postBLK : CBlock labelPost (Just [l']) Undefined
          postBLK = ?hphis1 |++> initCBlock

      let postG : CFG CBlock (Ends [l' ~> labelPost]) (Undefined labelPost)
          postG = SingleVertex {vins = Just [l'], vouts = Undefined} postBLK

      let final = Connect g postG

      pure $ CRO (labelPost ** final)
      
    finishIfThenElse [l] CompatOpen elseOuts _ labelPost g = do

      let postBLK : CBlock labelPost (Just $ [l] ++ elseOuts) Undefined
          postBLK = ?hphis2 |++> initCBlock

      
      let postG : CFG CBlock (Ends $ map (~> labelPost) (l :: elseOuts)) (Undefined labelPost)
          postG = SingleVertex {vins = Just $ l :: elseOuts, vouts = Undefined} postBLK

      let final = Connect g postG

      pure $ CRO (labelPost ** final)



-- Return ---------------------------------------------------------------------
compileInstr labelIn (While cond loop) = do

  condLabelIn <- freshLabel

  let incoming : CFG CBlock (Undefined labelIn) (Ends [labelIn ~> condLabelIn])
      incoming = SingleVertex {vouts = Just [condLabelIn]}
               $ initCBlock <+| Branch condLabelIn

  ((condLabelOut ** condG), val) <- compileExpr condLabelIn cond
  labelLoop <- freshLabel
  labelPost <- freshLabel

  let condG' = mapOut {outs = Just [labelLoop, labelPost]} (<+| CondBranch val labelLoop labelPost) condG

  loopRes <- compileInstr labelLoop loop
  (loopOuts ** (loopG, compat)) <- handleBranchResult loopRes condLabelOut condLabelIn

  whileG <- handleWhile labelIn loopOuts compat condG' loopG

  let post : CFG CBlock (Ends [condLabelOut ~> labelPost]) (Undefined labelPost)
      post = SingleVertex {vins = Just [condLabelOut]} $ ?hphis3 |++> initCBlock

  let final = Connect incoming (Connect whileG post)
  
  pure $ CRO (labelPost ** final)

  where
    handleWhile : (labelIn : BlockLabel)
               -> (loopOuts : List BlockLabel)
               -> (compat : Compatible crt loopOuts)
               -> (node : CFG CBlock (Undefined lbl) (Ends [lbl' ~> labelLoop, lbl' ~> labelPost]))
               -> (loop : CFG CBlock (Ends [lbl' ~> labelLoop]) (Ends $ map (~> lbl) loopOuts))
               -> CompM $ CFG CBlock (Ends [labelIn ~> lbl]) (Ends [lbl' ~> labelPost])
    handleWhile labelIn [] CompatClosed node loop = do
      
      let node' = mapIn {ins = Just [labelIn]} (?hphis4 |++>) node
      
      let final = Connect node' (Parallel loop Empty)

      pure final

    handleWhile labelIn [labelLoopOut] CompatOpen node loop = do

      let node' = mapIn {ins = Just [labelLoopOut, labelIn]} (?hphis5 |++>) node
      
      let final = Cycle node' loop
      
      pure final
  



-- Return ---------------------------------------------------------------------
compileInstr labelIn (Return expr) = do
  ((_ ** g), val) <- compileExpr labelIn expr
  
  let g' = mapOut {outs = Closed} (<+| Ret val) g
  pure (CRC g')


-- RetVoid --------------------------------------------------------------------
compileInstr labelIn RetVoid = do
  let g = mapOut {outs = Closed} (<+| RetVoid) initCFG
  pure (CRC g)













