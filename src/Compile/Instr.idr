module Compile.Instr

import Control.Monad.State
import Control.Monad.Either

import Data.Some
import Data.Attached
import Data.DList
import Data.DMap

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
Complete a control flow graph by adding phi assignments and a terminating
instruction if necessary
-}
handleBranchResult : (labelIn : BlockLabel)
                  -> (labelPost : BlockLabel)
                  -> CompileResult lbl crt
                  -> CompM (outs ** ( CFG CBlock (Ends [labelIn ~> lbl]) (Ends $ map (~> labelPost) outs)
                                    , DList (\lbl => Attached lbl VarCTX) outs
                                    ))

handleBranchResult labelIn labelPost (CRC g) = let

  -- there is only one input so phi instructions make no sense
  g' = mapIn {ins = Just [labelIn]} ([] |++>) g

  in pure ([] ** (g', []))

handleBranchResult labelIn labelPost (CRO (lbl' ** (g, ctx))) = let

  -- there is only one input so phi instructions make no sense
  g' = mapIn  {ins  = Just [labelIn]}   ([] |++>)
     $ mapOut {outs = Just [labelPost]} (<+| Branch labelPost)
     $ g
  
  
  in pure ([lbl'] ** (g', [ctx]))











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


{-
Returns a control flow graph that executes the instruction `instr`.
The graph starts in a block labeled `labelIn` with `ctx` describing values of
variables at the start of the graph.
-}
compileInstr : (labelIn : BlockLabel)
            -> (ctx : Attached labelIn VarCTX)
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
  (thenOuts ** (thenG, thenCTXs)) <- handleBranchResult condLabel labelPost thenRes

  let branches : CFG CBlock
                  (Ends [condLabel ~> labelThen, condLabel ~> labelPost])
                  (Ends $ map (~> labelPost) (thenOuts ++ [condLabel]))

      branches = rewrite map_append {f = (~> labelPost)} thenOuts condLabel
                 in Parallel thenG Empty
  
  let ctx' = reattach condLabel ctx
  SG postCTX postPhis <- segregate (thenCTXs ++ [ctx'])
  
  let postBLK : CBlock labelPost (Just $ thenOuts ++ [condLabel]) Undefined
      postBLK = postPhis |++> emptyCBlock postCTX
  
  let postG : CFG CBlock (Ends $ map (~> labelPost) (thenOuts ++ [condLabel])) (Undefined labelPost)
      postG = SingleVertex {vins = Just (thenOuts ++ [condLabel]), vouts = Undefined} postBLK
  
  let final = Connect condG' (Connect branches postG)
  
  pure $ CRO (labelPost ** (final, attach labelPost postCTX))
  



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
             -> (thenCTXs : DList (\lbl => Attached lbl VarCTX) thenOuts)
             
             -> (elseOuts : List BlockLabel)
             -> (elseG : CFG CBlock (Ends [nodeOut ~> labelElse]) (Ends $ map (~> labelPost) elseOuts))
             -> (elseCTXs : DList (\lbl => Attached lbl VarCTX) elseOuts)
             
             -> CompM ( CFG CBlock (Undefined nodeIn) (Undefined labelPost)
                      , Attached labelPost VarCTX
                      )

    mkOpenCFG node thenOuts thenG thenCTXs elseOuts elseG elseCTXs = do

      SG postCTX postPhis <- segregate (thenCTXs ++ elseCTXs)

      let postG : CFG CBlock (Ends $ map (~> labelPost) (thenOuts ++ elseOuts)) (Undefined labelPost)
          postG = SingleVertex {vins = Just (thenOuts ++ elseOuts), vouts = Undefined} 
                $ postPhis |++> emptyCBlock postCTX
      
      let final = Connect (node `Connect` (Parallel thenG elseG)) 
                $ rewrite revEq $ map_concat {f = (~> labelPost)} thenOuts elseOuts
                  in postG

      pure (final, attach labelPost postCTX)


    
    handleBranchResults : (nodeIn, nodeOut : BlockLabel)
                       -> (node : CFG CBlock (Undefined nodeIn) (Ends [nodeOut ~> labelThen, nodeOut ~> labelElse]))
                       -> (thenRes : CompileResult labelThen crtT)
                       -> (elseRes : CompileResult labelElse crtE)
                       -> CompM (CompileResult nodeIn (OpenOr crtT crtE))

    handleBranchResults nodeIn nodeOut node (CRC thenG) (CRC elseG) = do
      
      -- there is only one input so phi instructions make no sense
      let thenG' = mapIn {ins = Just [nodeOut]} ([] |++>) thenG
      let elseG' = mapIn {ins = Just [nodeOut]} ([] |++>) elseG
      
      let final = Connect node (Parallel thenG' elseG')
      
      pure (CRC final)

    handleBranchResults nodeIn nodeOut node thenRes@(CRC thenG) elseRes@(CRO (elseOut ** elseG)) = do

      labelPost <- freshLabel

      (thenOuts ** (thenG', thenCTXs)) <- handleBranchResult nodeOut labelPost thenRes
      (elseOuts ** (elseG', elseCTXs)) <- handleBranchResult nodeOut labelPost elseRes

      final <- mkOpenCFG node thenOuts thenG' thenCTXs elseOuts elseG' elseCTXs
      pure $ CRO (labelPost ** final)

    handleBranchResults nodeIn nodeOut node thenRes@(CRO (thenOut ** thenG)) elseRes = do

      labelPost <- freshLabel

      (thenOuts ** (thenG', thenCTXs)) <- handleBranchResult nodeOut labelPost thenRes
      (elseOuts ** (elseG', elseCTXs)) <- handleBranchResult nodeOut labelPost elseRes

      final <- mkOpenCFG node thenOuts thenG' thenCTXs elseOuts elseG' elseCTXs
      pure $ CRO (labelPost ** final)




-- While ----------------------------------------------------------------------
compileInstr labelIn ctxIn (While cond loop) = do

  labelNodeIn <- freshLabel

  let incoming : CFG CBlock (Undefined labelIn) (Ends [labelIn ~> labelNodeIn])
      incoming = SingleVertex {vouts = Just [labelNodeIn]}
               $ emptyCBlock (detach ctxIn) <+| Branch labelNodeIn
  
  -- TODO: get rid of unnecessary assignments
  ctxNode' <- reattach labelNodeIn <$> newRegForAll ctxIn
  let ctxNode = Prelude.map (DMap.map Var) ctxNode'

  ((labelNodeOut ** nodeG), val) <- evalStateT (detach ctxNode) $ compileExpr labelNodeIn cond
  labelLoop <- freshLabel
  labelPost <- freshLabel

  let nodeG' = mapOut {outs = Just [labelLoop, labelPost]} (<+| CondBranch val labelLoop labelPost) nodeG

  let ctxLoopIn = reattach labelLoop ctxNode
  loopRes <- compileInstr labelLoop ctxLoopIn loop
  
  loopG <- handleLoopResult ctxNode' ctxIn nodeG' loopRes

  let ctxPost = reattach labelPost ctxNode

  -- there is only one input so phi instructions make no sense
  let post : CFG CBlock (Ends [labelNodeOut ~> labelPost]) (Undefined labelPost)
      post = SingleVertex {vins = Just [labelNodeOut]} $ [] |++> emptyCBlock (detach ctxPost)

  let final = Connect incoming (Connect loopG post)
  
  pure $ CRO (labelPost ** (final, ctxPost))

  where
    
    handleLoopResult : {labelIn, nodeIn, nodeOut : BlockLabel}
                    -> (ctxNode : Attached nodeIn VarCTX')
                    -> (ctxIn : Attached labelIn VarCTX)
                    -> (node : CFG CBlock (Undefined nodeIn) (Ends [nodeOut ~> labelLoop, nodeOut ~> labelPost]))
                    -> (loopRes : CompileResult labelLoop crt)
                    -> CompM $ CFG CBlock (Ends [labelIn ~> nodeIn]) (Ends [nodeOut ~> labelPost])
    
    handleLoopResult {labelIn, nodeIn, nodeOut} ctxNode ctxIn node (CRC loop) = do

      {-
      TODO: take care of the fact that, new registers were assigned to every
      variable, but nothing represents that in the generated code.
      -}
      
      -- there is only one input so phi instructions make no sense
      let node' = mapIn {ins = Just [labelIn]} ([] |++>) node
      let loop' = mapIn {ins = Just [nodeOut]} ([] |++>) loop
      let final = Connect node' (Parallel loop' Empty)
      
      pure final

    handleLoopResult {labelIn, nodeIn, nodeOut} ctxNode ctxIn node (CRO (loopOut ** (loop, ctxLoop))) = do

      phis <- mkPhis (detach ctxNode) ctxLoop ctxIn
      
      let node' = mapIn {ins = Just [loopOut, labelIn]} (phis |++>) node
      
      -- there is only one input so phi instructions make no sense
      let loop' = mapIn  {ins  = Just [nodeOut]}  ([] |++>)
                $ mapOut {outs = Just [nodeIn]}   (<+| Branch nodeIn)
                $ loop
      
      let final = Cycle node' loop'
      
      pure final

      where

        mkPhis : VarCTX'
              -> {lbl, lbl' : BlockLabel}
              -> Attached lbl VarCTX
              -> Attached lbl' VarCTX
              -> CompM $ List (PhiInstr (MkInputs [lbl, lbl']))
        mkPhis ctx ctx' ctx'' = traverse mkPhi' (DMap.toList ctx) where
          
          mkPhi' : (t ** Item Variable (Reg . GetLLType) t)
                -> CompM $ PhiInstr (MkInputs [lbl, lbl'])

          mkPhi' (t ** MkItem key reg) = do
            let Just val'   = lookup key (detach ctx')
                            | Nothing => throwError $ Impossible "variable non existent in loop body or node context"
            
            let Just val''  = lookup key (detach ctx'')
                            | Nothing => throwError $ Impossible "variable non existent in loop body or node context"

            pure $ AssignPhi reg $ Phi [(lbl, val'), (lbl', val')]
            




-- Return ---------------------------------------------------------------------
compileInstr labelIn ctx (Return expr) = do
  ((_ ** g), val) <- evalStateT (detach ctx) $ compileExpr labelIn expr
  
  let g' = mapOut {outs = Closed} (<+| Ret val) g
  pure (CRC g')




-- RetVoid --------------------------------------------------------------------
compileInstr labelIn ctx RetVoid = do
  let g = mapOut {outs = Closed} (<+| RetVoid) initCFG
  pure (CRC g)













