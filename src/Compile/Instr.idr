module Compile.Instr

import Control.Monad.State

import Data.Some
import Data.Attached

import LNG
import LLVM

import Compile.Tools
import Compile.Tools.CBlock
import Compile.Tools.CompileResult
import Compile.Tools.CompM
import Compile.Tools.VariableCTX
import Compile.Expr

import CFG
import Utils



{-
Add phi assignments and a terminating instruction if necessary to the blocks
that are a result of compilation of a sub instruction and add the blocks to the
control flow graph
-}
handleBranchResult : (labelIn : BlockLabel)
                  -> (labelPost : BlockLabel)
                  -> CompileResult lbl crt
                  -> CompM (outs ** CFG CBlock (Ends [labelIn ~> lbl]) (Ends $ map (~> labelPost) outs))

handleBranchResult labelIn labelPost (CRC g) = let

  -- TODO: phis
  g' = mapIn {ins = Just [labelIn]} (?hbr_phis1 |++>) g

  in pure ([] ** g')

handleBranchResult labelIn labelPost (CRO (lbl' ** (g, ctx))) = let

  -- TODO: phis
  g' = mapIn  {ins  = Just [labelIn]}   (?hbr_phis2 |++>)
     $ mapOut {outs = Just [labelPost]} (<+| Branch labelPost)
     $ g
  
  
  in pure ([lbl'] ** g')











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
            -> Attached labelIn VarCTX
            -> (instr : Instr)
            -> CompM (CompileResult labelIn $ InstrCR instr)




-- Block ----------------------------------------------------------------------
compileInstr labelIn ctx (Block instrs) = compile' labelIn ctx instrs where

  mutual

    compile' : (labelIn : BlockLabel)
            -> Attached labelIn VarCTX
            -> (instrs : List Instr)
            -> CompM (CompileResult labelIn $ InstrsCR instrs)
    compile' labelIn ctx [] = pure (initCR labelIn)
    compile' labelIn ctx (instr :: instrs) = do
      res <- compileInstr labelIn ctx instr
      handleRes res instrs
      
    handleRes : {0 labelIn : BlockLabel}
             -> CompileResult labelIn crt
             -> (instrs : List Instr)
             -> CompM (CompileResult labelIn $ ClosedOr crt (InstrsCR instrs))
    handleRes (CRC g) instrs = pure (CRC g)
    handleRes (CRO (lbl ** (g, ctx))) instrs = do
      --let ctx = getContext g
      res <- compile' lbl ctx instrs
      pure $ combineCR g res
    



-- Assign ---------------------------------------------------------------------
compileInstr labelIn ctx (Assign var expr) = do

  -- TODO: consider having attached context in the state
  ((lbl ** g), val) <- evalStateT (detach ctx) $ compileExpr labelIn expr
  
  let g' = mapOut {outs = Undefined} (assign var val) g

  let ctx' = getContext g'
  pure $ CRO (lbl ** (g', ctx'))
  
  


-- If -------------------------------------------------------------------------
compileInstr labelIn ctx (If cond instrThen) = do

  -- TODO: use `ifology`
  ((condLabel ** condG), val) <- evalStateT (detach ctx) $ compileExpr labelIn cond
  labelThen <- freshLabel
  labelPost <- freshLabel

  let condG' = mapOut {outs = Just [labelThen, labelPost]} (<+| CondBranch val labelThen labelPost) condG
  
  thenRes <- compileInstr labelThen (reattach labelThen ctx) instrThen
  (thenOuts ** thenG) <- handleBranchResult condLabel labelPost thenRes

  let branches : CFG CBlock
                  (Ends [condLabel ~> labelThen, condLabel ~> labelPost])
                  (Ends $ map (~> labelPost) (thenOuts ++ [condLabel]))

      branches = rewrite map_append {f = (~> labelPost)} thenOuts condLabel
                 in Parallel thenG Empty
  
  -- TODO: here one has to segregate arbitrary number of contexts
  --SG postCTX postPhis <- segregate ctx (getContexts branches)

  -- TODO: phis
  -- TODO: add context
  let postBLK : CBlock labelPost (Just $ thenOuts ++ [condLabel]) Undefined
      postBLK = ?h_if_phis |++> initCBlock
  
  let postG : CFG CBlock (Ends $ map (~> labelPost) (thenOuts ++ [condLabel])) (Undefined labelPost)
      postG = SingleVertex {vins = Just (thenOuts ++ [condLabel]), vouts = Undefined} postBLK
  
  let final = Connect condG' (Connect branches postG)
  
  pure $ CRO (labelPost ** (final, ?hctxIf))
  



-- IfElse ---------------------------------------------------------------------
compileInstr labelIn ctx (IfElse cond instrThen instrElse) = do

  -- TODO: use `ifology`
  ((condLabel ** condG), val) <- evalStateT (detach ctx) $ compileExpr labelIn cond
  labelThen <- freshLabel
  labelElse <- freshLabel
  labelPost <- freshLabel

  let condG' = mapOut {outs = Just [labelThen, labelElse]} (<+| CondBranch val labelThen labelElse) condG
  thenRes <- compileInstr labelThen (reattach labelThen ctx) instrThen
  elseRes <- compileInstr labelElse (reattach labelElse ctx) instrElse

  handleBranchResults labelIn condLabel condG' thenRes elseRes
  
  where

    mkOpenCFG : (node : CFG CBlock (Undefined nodeIn) (Ends [nodeOut ~> labelThen, nodeOut ~> labelElse]))
                        
             -> (thenOuts : List BlockLabel)
             -> (thenG : CFG CBlock (Ends [nodeOut ~> labelThen]) (Ends $ map (~> labelPost) thenOuts))
             
             -> (elseOuts : List BlockLabel)
             -> (elseG : CFG CBlock (Ends [nodeOut ~> labelElse]) (Ends $ map (~> labelPost) elseOuts))
             
             -> CompM (CFG CBlock (Undefined nodeIn) (Undefined labelPost))

    mkOpenCFG node thenOuts thenG elseOuts elseG = do

      -- TODO: phis
      -- TODO: add context
      let postG : CFG CBlock (Ends $ map (~> labelPost) (thenOuts ++ elseOuts)) (Undefined labelPost)
          postG = SingleVertex {vins = Just (thenOuts ++ elseOuts), vouts = Undefined} 
                $ ?h_if_else_phis |++> initCBlock
      
      let final = Connect (node `Connect` (Parallel thenG elseG)) 
                $ rewrite revEq $ map_concat {f = (~> labelPost)} thenOuts elseOuts
                  in postG

      pure final


    
    handleBranchResults : (nodeIn, nodeOut : BlockLabel)
                       -> (node : CFG CBlock (Undefined nodeIn) (Ends [nodeOut ~> labelThen, nodeOut ~> labelElse]))
                       -> (thenRes : CompileResult labelThen crtT)
                       -> (elseRes : CompileResult labelElse crtE)
                       -> CompM (CompileResult nodeIn (OpenOr crtT crtE))

    handleBranchResults nodeIn nodeOut node (CRC thenG) (CRC elseG) = do
      
      let thenG' = mapIn {ins = Just [nodeOut]} (?hbrs_phis0 |++>) thenG
      let elseG' = mapIn {ins = Just [nodeOut]} (?hbrs_phis1 |++>) elseG
      
      let final = Connect node (Parallel thenG' elseG')
      
      pure (CRC final)

    handleBranchResults nodeIn nodeOut node thenRes@(CRC thenG) elseRes@(CRO (elseOut ** elseG)) = do

      labelPost <- freshLabel

      (thenOuts ** thenG') <- handleBranchResult nodeOut labelPost thenRes
      (elseOuts ** elseG') <- handleBranchResult nodeOut labelPost elseRes

      final <- mkOpenCFG node thenOuts thenG' elseOuts elseG'
      pure $ CRO (labelPost ** (final, ?hctxIfElse1))

    handleBranchResults nodeIn nodeOut node thenRes@(CRO (thenOut ** thenG)) elseRes = do

      labelPost <- freshLabel

      (thenOuts ** thenG') <- handleBranchResult nodeOut labelPost thenRes
      (elseOuts ** elseG') <- handleBranchResult nodeOut labelPost elseRes

      final <- mkOpenCFG node thenOuts thenG' elseOuts elseG'
      pure $ CRO (labelPost ** (final, ?hctxIfElse2))


    

-- Return ---------------------------------------------------------------------
compileInstr labelIn ctx (While cond loop) = do

  condLabelIn <- freshLabel

  -- TODO: add context
  let incoming : CFG CBlock (Undefined labelIn) (Ends [labelIn ~> condLabelIn])
      incoming = SingleVertex {vouts = Just [condLabelIn]}
               $ initCBlock <+| Branch condLabelIn

  ((condLabelOut ** condG), val) <- evalStateT (detach ctx) $ compileExpr condLabelIn cond
  labelLoop <- freshLabel
  labelPost <- freshLabel

  let condG' = mapOut {outs = Just [labelLoop, labelPost]} (<+| CondBranch val labelLoop labelPost) condG

  loopRes <- compileInstr labelLoop ?hctxWhileLoop loop
  
  whileG <- handleLoopResult labelIn condLabelIn condLabelOut condG' loopRes

  -- TODO: phis
  -- TODO: add context
  let post : CFG CBlock (Ends [condLabelOut ~> labelPost]) (Undefined labelPost)
      post = SingleVertex {vins = Just [condLabelOut]} $ ?h_while_phis |++> initCBlock

  let final = Connect incoming (Connect whileG post)
  
  pure $ CRO (labelPost ** (final, ?hctxWhile))

  where
    
    handleLoopResult : (labelIn, nodeIn, nodeOut : BlockLabel)
                    -> (node : CFG CBlock (Undefined nodeIn) (Ends [nodeOut ~> labelLoop, nodeOut ~> labelPost]))
                    -> (loopRes : CompileResult labelLoop crt)
                    -> CompM $ CFG CBlock (Ends [labelIn ~> nodeIn]) (Ends [nodeOut ~> labelPost])
    
    handleLoopResult labelIn nodeIn nodeOut node (CRC loop) = do
      
      let node' = mapIn {ins = Just [labelIn]} (?hlr_phis0 |++>) node
      let loop' = mapIn {ins = Just [nodeOut]} (?hlr_phis1 |++>) loop
      let final = Connect node' (Parallel loop' Empty)
      
      pure final

    handleLoopResult labelIn nodeIn nodeOut node (CRO (loopOut ** (loop, ctx))) = do
      
      let node' = mapIn {ins = Just [loopOut, labelIn]} (?hlr_phis2 |++>) node
      let loop' = mapIn  {ins  = Just [nodeOut]}  (?hlr_phis3 |++>)
                $ mapOut {outs = Just [nodeIn]}   (<+| Branch nodeIn)
                $ loop
      
      let final = Cycle node' loop'
      
      pure final




-- Return ---------------------------------------------------------------------
compileInstr labelIn ctx (Return expr) = do
  ((_ ** g), val) <- evalStateT (detach ctx) $ compileExpr labelIn expr
  
  let g' = mapOut {outs = Closed} (<+| Ret val) g
  pure (CRC g')




-- RetVoid --------------------------------------------------------------------
compileInstr labelIn ctx RetVoid = do
  let g = mapOut {outs = Closed} (<+| RetVoid) initCFG
  pure (CRC g)













