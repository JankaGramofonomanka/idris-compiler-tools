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
TODO: Figure out how to reduce the number of attachments and detachments
-}





collect : {lbl' : BlockLabel} -> CompileResultD lbl lbl' crt -> CompM $ CompileResult lbl crt
collect {lbl' = labelPost} (CRDC g) = pure $ CRC g
collect {lbl' = labelPost} (CRDO (lbls ** (g, ctxs))) = do
  SG ctx phis <- segregate ctxs

  let ctxPost = attach labelPost ctx

  let post : CFG CBlock (Ends $ map (~> labelPost) lbls) (Undefined labelPost)
      post = SingleVertex {vins = Just lbls} $ phis |++> emptyCBlock (detach ctxPost)
  
  let final = Connect g post

  pure $ CRO (labelPost ** (final, ctxPost))




terminate : (lbl' : BlockLabel) -> CompileResult lbl crt -> CompileResultD lbl lbl' crt
terminate labelPost (CRC g) = CRDC g
terminate labelPost (CRO (lbl ** (g, ctx))) = let
  g' = mapOut {outs = Just [labelPost]} (<+| Branch labelPost) g
  in CRDO ([lbl] ** (g', [ctx]))





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





mutual
  {-
  Returns a control flow graph that executes the instruction `instr`.
  The graph starts in a block labeled `labelIn` with `ctx` describing values of
  variables at the start of the graph.
  -}
  compileInstr : (labelIn : BlockLabel)
              -> (ctx : Attached labelIn VarCTX)
              -> (instr : Instr)
              -> CompM (CompileResult labelIn $ InstrCR instr)




  -- Block --------------------------------------------------------------------
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
      

  -- Assign -------------------------------------------------------------------
  compileInstr labelIn ctx (Assign var expr) = do

    -- TODO: consider having attached context in the state
    ((lbl ** g), val) <- evalStateT (detach ctx) $ compileExpr labelIn expr
    
    let g' = mapOut {outs = Undefined} (assign var val) g

    let ctx' = getContext g'
    pure $ CRO (lbl ** (g', ctx'))
    
    
  -- If -----------------------------------------------------------------------
  compileInstr labelIn ctx instr@(If cond instrThen)
    = compileInstrAndJump labelIn !freshLabel ctx instr >>= collect

  -- IfElse -------------------------------------------------------------------
  compileInstr labelIn ctx instr@(IfElse cond instrThen instrElse)
    = compileInstrAndJump labelIn !freshLabel ctx instr >>= collect

  -- While --------------------------------------------------------------------
  compileInstr labelIn ctx instr@(While cond loop)
    = compileInstrAndJump labelIn !freshLabel ctx instr >>= collect
              

  -- Return -------------------------------------------------------------------
  compileInstr labelIn ctx (Return expr) = do
    ((_ ** g), val) <- evalStateT (detach ctx) $ compileExpr labelIn expr
    
    let g' = mapOut {outs = Closed} (<+| Ret val) g
    pure (CRC g')


  -- RetVoid ------------------------------------------------------------------
  compileInstr labelIn ctx RetVoid = do
    let g = mapOut {outs = Closed} (<+| RetVoid) initCFG
    pure (CRC g)












  compileInstrAndJump : (labelIn, labelPost : BlockLabel)
                     -> (ctx : Attached labelIn VarCTX)
                     -> (instr : Instr)
                     -> CompM (CompileResultD labelIn labelPost $ InstrCR instr)

  -- Assign -------------------------------------------------------------------
  compileInstrAndJump labelIn labelPost ctx instr@(Assign var expr)
    = terminate labelPost <$> compileInstr labelIn ctx instr

  -- Return -------------------------------------------------------------------
  compileInstrAndJump labelIn labelPost ctx instr@(Return expr)
    = terminate labelPost <$> compileInstr labelIn ctx instr

  -- RetVoid ------------------------------------------------------------------
  compileInstrAndJump labelIn labelPost ctx instr@RetVoid
    = terminate labelPost <$> compileInstr labelIn ctx instr




  -- Block --------------------------------------------------------------------
  compileInstrAndJump labelIn labelPost ctx (Block instrs)
    = compile' labelIn ctx instrs
    
    where

      mutual

        decideInstrCR : (instr : Instr) -> Either (InstrCR instr = Closed) (InstrCR instr = Open)
        decideInstrCR instr with (InstrCR instr)
          decideInstrCR instr | Closed = Left Refl
          decideInstrCR instr | Open = Right Refl

        compile' : (labelIn : BlockLabel)
                -> Attached labelIn VarCTX
                -> (instrs : List Instr)
                -> CompM (CompileResultD labelIn labelPost $ InstrsCR instrs)
        compile' labelIn ctx Nil = pure (initCRD labelIn labelPost)
        
        compile' labelIn ctx (instr :: Nil)
          
          = rewrite closed_or_commut (InstrCR instr) (InstrsCR Nil)
            in compileInstrAndJump labelIn labelPost ctx instr
          
        compile' labelIn ctx (instr :: instrs) with (decideInstrCR instr)

          
          compile' labelIn ctx (instr :: instrs) | Left crc = do
            res <- compileInstrAndJump labelIn labelPost ctx instr

            let thm : (InstrCR instr = ClosedOr (InstrCR instr) (InstrsCR instrs))
                thm = rewrite crc in Refl
                
            pure $ rewrite revEq thm in res
          

          compile' labelIn ctx (instr :: instrs) | Right cro = do
            
            res <- compileInstr labelIn ctx instr
            
            let CRO (lbl ** (g, ctx)) = the (CompileResult labelIn Open) $ rewrite revEq cro in res
            
            res' <- compile' lbl ctx instrs
            
            let thm : (InstrsCR instrs = ClosedOr (InstrCR instr) (InstrsCR instrs))
                thm = rewrite cro in Refl
            
            pure $ rewrite revEq thm in combineCRD g res'




  -- If -----------------------------------------------------------------------
  compileInstrAndJump labelIn labelPost ctx (If cond instrThen) = do

    -- TODO: use `ifology`
    ((condLabel ** condG), val) <- evalStateT (detach ctx) $ compileExpr labelIn cond
    labelThen <- freshLabel

    let condG' = mapOut {outs = Just [labelThen, labelPost]} (<+| CondBranch val labelThen labelPost) condG
    
    thenRes <- compileInstrAndJump labelThen labelPost (reattach labelThen ctx) instrThen
    (thenOuts ** (thenG, thenCTXs)) <- handleBranchResult condLabel thenRes

    let branches : CFG CBlock
                    (Ends [condLabel ~> labelThen, condLabel ~> labelPost])
                    (Ends $ map (~> labelPost) (thenOuts ++ [condLabel]))

        branches = rewrite map_append {f = (~> labelPost)} thenOuts condLabel
                  in Parallel thenG Empty
    
    let ctx' = reattach condLabel ctx
    let final = Connect condG' branches
    
    pure $ CRDO (thenOuts ++ [condLabel] ** (final, thenCTXs ++ [ctx']))

    
    where

      handleBranchResult : (labelIn : BlockLabel)
                        -> CompileResultD lbl lbl' crt
                        -> CompM (outs ** ( CFG CBlock (Ends [labelIn ~> lbl]) (Ends $ map (~> lbl') outs)
                                          , DList (\lbl => Attached lbl VarCTX) outs
                                          ))
      
      handleBranchResult labelIn (CRDC g) = do
        let g' = mapIn {ins = Just [labelIn]} ([] |++>) g
        pure ([] ** (g', []))

      handleBranchResult labelIn (CRDO (outs ** (g, ctxs))) = do
        let g' = mapIn {ins = Just [labelIn]} ([] |++>) g
        pure (outs ** (g', ctxs))



  -- IfElse -------------------------------------------------------------------
  compileInstrAndJump labelIn labelPost ctx (IfElse cond instrThen instrElse) = do

    -- TODO: use `ifology`
    ((condLabel ** condG), val) <- evalStateT (detach ctx) $ compileExpr labelIn cond
    labelThen <- freshLabel
    labelElse <- freshLabel

    let condG' = mapOut {outs = Just [labelThen, labelElse]} (<+| CondBranch val labelThen labelElse) condG
    thenRes <- compileInstrAndJump labelThen labelPost (reattach labelThen ctx) instrThen
    elseRes <- compileInstrAndJump labelElse labelPost (reattach labelElse ctx) instrElse

    handleBranchResults labelIn condLabel condG' thenRes elseRes
    
    where

      handleBranchResults : (nodeIn, nodeOut : BlockLabel)
                         -> (node : CFG CBlock (Undefined nodeIn) (Ends [nodeOut ~> labelThen, nodeOut ~> labelElse]))
                         
                         -> {labelPost : BlockLabel}
                         -> (thenRes : CompileResultD labelThen labelPost crtT)
                         -> (elseRes : CompileResultD labelElse labelPost crtE)
                         
                         -> CompM (CompileResultD nodeIn labelPost (OpenOr crtT crtE))

      handleBranchResults nodeIn nodeOut node (CRDC thenG) (CRDC elseG) = do
        
        -- there is only one input so phi instructions make no sense
        let thenG' = mapIn {ins = Just [nodeOut]} ([] |++>) thenG
        let elseG' = mapIn {ins = Just [nodeOut]} ([] |++>) elseG
        
        let final = Connect node (Parallel thenG' elseG')
        
        pure (CRDC final)

      handleBranchResults nodeIn nodeOut node (CRDC thenG) (CRDO (elseOuts ** (elseG, elseCTXs))) = do

        let thenG' = mapIn {ins = Just [nodeOut]} ([] |++>) thenG
        let elseG' = mapIn {ins = Just [nodeOut]} ([] |++>) elseG

        let final = node `Connect` (thenG' `Parallel` elseG')

        pure $ CRDO (elseOuts ** (final, elseCTXs))

      handleBranchResults nodeIn nodeOut node {labelPost} (CRDO (thenOuts ** (thenG, thenCTXs))) (CRDC elseG) = do

        let thenG' = mapIn {ins = Just [nodeOut]} ([] |++>) thenG
        let elseG' = mapIn {ins = Just [nodeOut]} ([] |++>) elseG

        let final = node `Connect` (thenG' `Parallel` elseG')
        let final' = rewrite revEq $ concat_nil (map (\arg => arg ~> labelPost) thenOuts)
                     in final

        pure $ CRDO (thenOuts ** (final', thenCTXs))
      
      handleBranchResults
        nodeIn
        nodeOut
        node
        {labelPost}
        (CRDO (thenOuts ** (thenG, thenCTXs)))
        (CRDO (elseOuts ** (elseG, elseCTXs)))
        
        = do

          let thenG' = mapIn {ins = Just [nodeOut]} ([] |++>) thenG
          let elseG' = mapIn {ins = Just [nodeOut]} ([] |++>) elseG

          let final = node `Connect` (thenG' `Parallel` elseG')
          let final' = rewrite map_concat {f = (~> labelPost)} thenOuts elseOuts
                     in final

          pure $ CRDO (thenOuts ++ elseOuts ** (final', thenCTXs ++ elseCTXs))
  



  -- While --------------------------------------------------------------------
  compileInstrAndJump labelIn labelPost ctxIn (While cond loop) = do

    labelNodeIn <- freshLabel

    let incoming : CFG CBlock (Undefined labelIn) (Ends [labelIn ~> labelNodeIn])
        incoming = SingleVertex {vouts = Just [labelNodeIn]}
                $ emptyCBlock (detach ctxIn) <+| Branch labelNodeIn
    
    -- TODO: get rid of unnecessary assignments
    ctxNode' <- reattach labelNodeIn <$> newRegForAll ctxIn
    let ctxNode = map (DMap.dmap Var) ctxNode'

    ((labelNodeOut ** nodeG), val) <- evalStateT (detach ctxNode) $ compileExpr labelNodeIn cond
    let ctxNodeOut = reattach labelNodeOut ctxNode
    labelLoop <- freshLabel

    let nodeG' = mapOut {outs = Just [labelLoop, labelPost]} (<+| CondBranch val labelLoop labelPost) nodeG

    let ctxLoopIn = reattach labelLoop ctxNode

    {-
    TODO: Consider using `compileInstrAndJump` here. This would require 
    modifying the definition of `Cycle` so that `node` can have multiple inputs
    from the loop body.
    -}
    loopRes <- compileInstr labelLoop ctxLoopIn loop
    
    loopG <- handleLoopResult ctxNode' ctxIn nodeG' loopRes

    let final = Connect incoming loopG
    
    pure $ CRDO ([labelNodeOut] ** (final, [ctxNodeOut]))

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





    









