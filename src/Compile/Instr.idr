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





collect : {lbl' : BlockLabel} -> CompileResultUD lbl lbl' crt -> CompM $ CompileResultUU lbl crt
collect {lbl' = labelPost} (CRUDC g) = pure $ CRUUC g
collect {lbl' = labelPost} (CRUDO (lbls ** (g, ctxs))) = do
  SG ctx phis <- segregate ctxs

  let ctxPost = attach labelPost ctx

  let post : CFG CBlock (Ends $ map (~> labelPost) lbls) (Undefined labelPost)
      post = SingleVertex {vins = Just lbls} $ phis |++> emptyCBlock (detach ctxPost)
  
  let final = Connect g post

  pure $ CRUUO (labelPost ** (final, ctxPost))




terminate : (lbl' : BlockLabel) -> CompileResultUU lbl crt -> CompileResultUD lbl lbl' crt
terminate labelPost (CRUUC g) = CRUDC g
terminate labelPost (CRUUO (lbl ** (g, ctx))) = let
  g' = mapOut {outs = Just [labelPost]} (<+| Branch labelPost) g
  in CRUDO ([lbl] ** (g', [ctx]))





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
  The convention is that names of funcions and data types shall have a
  suffix <X><Y> where:
  - <X> describes the kind of expected input of a graph
  - <Y> describes the kind of expected output of a graph
  
  <X> and <Y> can be one of two values:
  - 'U' (undefined) - the graph can have one undefined endpoint, that is
    a vertex without specified inputs or outputs
  - 'D' (defined) - the graph can have only defined endpoints, that is
    vertices with already known inputs or outputs.
  -}

  {-
  Returns a control flow graph that executes the instruction `instr`.
  The graph starts in a block labeled `labelIn` with `ctx` describing values of
  variables at the start of the graph.
  -}
  compileInstrUU : (labelIn : BlockLabel)
              -> (ctx : Attached labelIn VarCTX)
              -> (instr : Instr)
              -> CompM (CompileResultUU labelIn $ InstrCR instr)




  -- Block --------------------------------------------------------------------
  compileInstrUU labelIn ctx (Block instrs) = compile' labelIn ctx instrs where

    mutual

      compile' : (labelIn : BlockLabel)
              -> Attached labelIn VarCTX
              -> (instrs : List Instr)
              -> CompM (CompileResultUU labelIn $ InstrsCR instrs)
      compile' labelIn ctx [] = pure (initCRUU labelIn)
      compile' labelIn ctx (instr :: instrs) = do
        res <- compileInstrUU labelIn ctx instr
        handleRes res instrs
        
      handleRes : {0 labelIn : BlockLabel}
              -> CompileResultUU labelIn crt
              -> (instrs : List Instr)
              -> CompM (CompileResultUU labelIn $ ClosedOr crt (InstrsCR instrs))
      handleRes (CRUUC g) instrs = pure (CRUUC g)
      handleRes (CRUUO (lbl ** (g, ctx))) instrs = do
        res <- compile' lbl ctx instrs
        pure $ combineCRUU g res
      

  -- Assign -------------------------------------------------------------------
  compileInstrUU labelIn ctx (Assign var expr) = do

    -- TODO: consider having attached context in the state
    ((lbl ** g), val) <- evalStateT (detach ctx) $ compileExpr labelIn expr
    
    let g' = mapOut {outs = Undefined} (assign var val) g

    let ctx' = getContext g'
    pure $ CRUUO (lbl ** (g', ctx'))
    
    
  -- If -----------------------------------------------------------------------
  compileInstrUU labelIn ctx instr@(If cond instrThen)
    = compileInstrUD labelIn !freshLabel ctx instr >>= collect

  -- IfElse -------------------------------------------------------------------
  compileInstrUU labelIn ctx instr@(IfElse cond instrThen instrElse)
    = compileInstrUD labelIn !freshLabel ctx instr >>= collect

  -- While --------------------------------------------------------------------
  compileInstrUU labelIn ctx instr@(While cond loop)
    = compileInstrUD labelIn !freshLabel ctx instr >>= collect
              

  -- Return -------------------------------------------------------------------
  compileInstrUU labelIn ctx (Return expr) = do
    ((_ ** g), val) <- evalStateT (detach ctx) $ compileExpr labelIn expr
    
    let g' = mapOut {outs = Closed} (<+| Ret val) g
    pure (CRUUC g')


  -- RetVoid ------------------------------------------------------------------
  compileInstrUU labelIn ctx RetVoid = do
    let g = mapOut {outs = Closed} (<+| RetVoid) initCFG
    pure (CRUUC g)












  compileInstrUD : (labelIn, labelPost : BlockLabel)
                     -> (ctx : Attached labelIn VarCTX)
                     -> (instr : Instr)
                     -> CompM (CompileResultUD labelIn labelPost $ InstrCR instr)

  -- Assign -------------------------------------------------------------------
  compileInstrUD labelIn labelPost ctx instr@(Assign var expr)
    = terminate labelPost <$> compileInstrUU labelIn ctx instr

  -- Return -------------------------------------------------------------------
  compileInstrUD labelIn labelPost ctx instr@(Return expr)
    = terminate labelPost <$> compileInstrUU labelIn ctx instr

  -- RetVoid ------------------------------------------------------------------
  compileInstrUD labelIn labelPost ctx instr@RetVoid
    = terminate labelPost <$> compileInstrUU labelIn ctx instr




  -- Block --------------------------------------------------------------------
  compileInstrUD labelIn labelPost ctx (Block instrs)
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
                -> CompM (CompileResultUD labelIn labelPost $ InstrsCR instrs)
        compile' labelIn ctx Nil = pure (initCRUD labelIn labelPost)
        
        compile' labelIn ctx (instr :: Nil)
          
          = rewrite closed_or_commut (InstrCR instr) (InstrsCR Nil)
            in compileInstrUD labelIn labelPost ctx instr
          
        compile' labelIn ctx (instr :: instrs) with (decideInstrCR instr)

          
          compile' labelIn ctx (instr :: instrs) | Left crc = do
            res <- compileInstrUD labelIn labelPost ctx instr

            let thm : (InstrCR instr = ClosedOr (InstrCR instr) (InstrsCR instrs))
                thm = rewrite crc in Refl
                
            pure $ rewrite revEq thm in res
          

          compile' labelIn ctx (instr :: instrs) | Right cro = do
            
            res <- compileInstrUU labelIn ctx instr
            
            let CRUUO (lbl ** (g, ctx)) = the (CompileResultUU labelIn Open) $ rewrite revEq cro in res
            
            res' <- compile' lbl ctx instrs
            
            let thm : (InstrsCR instrs = ClosedOr (InstrCR instr) (InstrsCR instrs))
                thm = rewrite cro in Refl
            
            pure $ rewrite revEq thm in combineCRUD g res'




  -- If -----------------------------------------------------------------------
  compileInstrUD labelIn labelPost ctx (If cond instrThen) = do

    -- TODO: use `ifology`
    ((condLabel ** condG), val) <- evalStateT (detach ctx) $ compileExpr labelIn cond
    labelThen <- freshLabel

    let condG' = mapOut {outs = Just [labelThen, labelPost]} (<+| CondBranch val labelThen labelPost) condG
    
    thenRes <- compileInstrUD labelThen labelPost (reattach labelThen ctx) instrThen
    (thenOuts ** (thenG, thenCTXs)) <- handleBranchResult condLabel thenRes

    let branches : CFG CBlock
                    (Ends [condLabel ~> labelThen, condLabel ~> labelPost])
                    (Ends $ map (~> labelPost) (thenOuts ++ [condLabel]))

        branches = rewrite map_append {f = (~> labelPost)} thenOuts condLabel
                  in Parallel thenG Empty
    
    let ctx' = reattach condLabel ctx
    let final = Connect condG' branches
    
    pure $ CRUDO (thenOuts ++ [condLabel] ** (final, thenCTXs ++ [ctx']))

    
    where

      handleBranchResult : (labelIn : BlockLabel)
                        -> CompileResultUD lbl lbl' crt
                        -> CompM (outs ** ( CFG CBlock (Ends [labelIn ~> lbl]) (Ends $ map (~> lbl') outs)
                                          , DList (\lbl => Attached lbl VarCTX) outs
                                          ))
      
      handleBranchResult labelIn (CRUDC g) = do
        let g' = mapIn {ins = Just [labelIn]} ([] |++>) g
        pure ([] ** (g', []))

      handleBranchResult labelIn (CRUDO (outs ** (g, ctxs))) = do
        let g' = mapIn {ins = Just [labelIn]} ([] |++>) g
        pure (outs ** (g', ctxs))



  -- IfElse -------------------------------------------------------------------
  compileInstrUD labelIn labelPost ctx (IfElse cond instrThen instrElse) = do

    -- TODO: use `ifology`
    ((condLabel ** condG), val) <- evalStateT (detach ctx) $ compileExpr labelIn cond
    labelThen <- freshLabel
    labelElse <- freshLabel

    let condG' = mapOut {outs = Just [labelThen, labelElse]} (<+| CondBranch val labelThen labelElse) condG
    thenRes <- compileInstrUD labelThen labelPost (reattach labelThen ctx) instrThen
    elseRes <- compileInstrUD labelElse labelPost (reattach labelElse ctx) instrElse

    handleBranchResults labelIn condLabel condG' thenRes elseRes
    
    where

      handleBranchResults : (nodeIn, nodeOut : BlockLabel)
                         -> (node : CFG CBlock (Undefined nodeIn) (Ends [nodeOut ~> labelThen, nodeOut ~> labelElse]))
                         
                         -> {labelPost : BlockLabel}
                         -> (thenRes : CompileResultUD labelThen labelPost crtT)
                         -> (elseRes : CompileResultUD labelElse labelPost crtE)
                         
                         -> CompM (CompileResultUD nodeIn labelPost (OpenOr crtT crtE))

      handleBranchResults nodeIn nodeOut node (CRUDC thenG) (CRUDC elseG) = do
        
        -- there is only one input so phi instructions make no sense
        let thenG' = mapIn {ins = Just [nodeOut]} ([] |++>) thenG
        let elseG' = mapIn {ins = Just [nodeOut]} ([] |++>) elseG
        
        let final = Connect node (Parallel thenG' elseG')
        
        pure (CRUDC final)

      handleBranchResults nodeIn nodeOut node (CRUDC thenG) (CRUDO (elseOuts ** (elseG, elseCTXs))) = do

        let thenG' = mapIn {ins = Just [nodeOut]} ([] |++>) thenG
        let elseG' = mapIn {ins = Just [nodeOut]} ([] |++>) elseG

        let final = node `Connect` (thenG' `Parallel` elseG')

        pure $ CRUDO (elseOuts ** (final, elseCTXs))

      handleBranchResults nodeIn nodeOut node {labelPost} (CRUDO (thenOuts ** (thenG, thenCTXs))) (CRUDC elseG) = do

        let thenG' = mapIn {ins = Just [nodeOut]} ([] |++>) thenG
        let elseG' = mapIn {ins = Just [nodeOut]} ([] |++>) elseG

        let final = node `Connect` (thenG' `Parallel` elseG')
        let final' = rewrite revEq $ concat_nil (map (\arg => arg ~> labelPost) thenOuts)
                     in final

        pure $ CRUDO (thenOuts ** (final', thenCTXs))
      
      handleBranchResults
        nodeIn
        nodeOut
        node
        {labelPost}
        (CRUDO (thenOuts ** (thenG, thenCTXs)))
        (CRUDO (elseOuts ** (elseG, elseCTXs)))
        
        = do

          let thenG' = mapIn {ins = Just [nodeOut]} ([] |++>) thenG
          let elseG' = mapIn {ins = Just [nodeOut]} ([] |++>) elseG

          let final = node `Connect` (thenG' `Parallel` elseG')
          let final' = rewrite map_concat {f = (~> labelPost)} thenOuts elseOuts
                     in final

          pure $ CRUDO (thenOuts ++ elseOuts ** (final', thenCTXs ++ elseCTXs))
  



  -- While --------------------------------------------------------------------
  compileInstrUD labelIn labelPost ctxIn (While cond loop) = do

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
    TODO: Consider using `compileInstrUD` here. This would require 
    modifying the definition of `Cycle` so that `node` can have multiple inputs
    from the loop body.
    -}
    loopRes <- compileInstrUU labelLoop ctxLoopIn loop
    
    loopG <- handleLoopResult ctxNode' ctxIn nodeG' loopRes

    let final = Connect incoming loopG
    
    pure $ CRUDO ([labelNodeOut] ** (final, [ctxNodeOut]))

    where
      
      handleLoopResult : {labelIn, nodeIn, nodeOut : BlockLabel}
                      -> (ctxNode : Attached nodeIn VarCTX')
                      -> (ctxIn : Attached labelIn VarCTX)
                      -> (node : CFG CBlock (Undefined nodeIn) (Ends [nodeOut ~> labelLoop, nodeOut ~> labelPost]))
                      -> (loopRes : CompileResultUU labelLoop crt)
                      -> CompM $ CFG CBlock (Ends [labelIn ~> nodeIn]) (Ends [nodeOut ~> labelPost])
      
      handleLoopResult {labelIn, nodeIn, nodeOut} ctxNode ctxIn node (CRUUC loop) = do

        {-
        TODO: take care of the fact that, new registers were assigned to every
        variable, but nothing represents that in the generated code.
        -}
        
        -- there is only one input so phi instructions make no sense
        let node' = mapIn {ins = Just [labelIn]} ([] |++>) node
        let loop' = mapIn {ins = Just [nodeOut]} ([] |++>) loop
        let final = Connect node' (Parallel loop' Empty)
        
        pure final

      handleLoopResult {labelIn, nodeIn, nodeOut} ctxNode ctxIn node (CRUUO (loopOut ** (loop, ctxLoop))) = do

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





    









