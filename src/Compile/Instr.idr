module Compile.Instr

import Control.Monad.State
import Control.Monad.Either

import Data.Some
import Data.Attached
import Data.DList
import Data.DMap
import Data.DSum
import Data.Typed

import LNG
import LLVM

import Compile.Tools
import Compile.Tools.CBlock
import Compile.Tools.CompileResult
import Compile.Tools.CompM
import Compile.Tools.VariableCTX
import Compile.Tools.Other
import Compile.Expr

import CFG
import Utils

{-
TODO: Figure out how to reduce the number of attachments and detachments
-}



--* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
-- Utils ----------------------------------------------------------------------
--* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
jumpTo : (lbl' : BlockLabel) -> CompileResultUU lbl crt -> CompileResultUD lbl lbl' crt
jumpTo labelPost (CRUUC g) = CRUDC g
jumpTo labelPost (CRUUO (lbl ** g)) = let
  g' = omap {outs = Just [labelPost]} (<+| Branch labelPost) g
  in CRUDO ([lbl] ** g')


jumpFrom : (lbl : BlockLabel) -> CompileResultUD lbl' lbl'' crt -> CompileResultDD [lbl ~> lbl'] lbl'' crt
jumpFrom labelPre (CRUDC g) = CRDDC $ imap {ins = Just [labelPre]} ([] |++>) g
jumpFrom labelPre (CRUDO (lbls ** g)) = let
  g' = imap {ins = Just [labelPre]} ([] |++>) g
  in CRDDO (lbls ** g')


ifology' : (labelIn : BlockLabel)
        -> (ctx : labelIn :~: VarCTX)
        -> (expr : Expr TBool)
        -> (lblT : BlockLabel)
        -> (lblF : BlockLabel)
        -> CompM  ( outsT ** outsF ** CFG CBlock
                                          (Undefined labelIn)
                                          (Defined $ outsT ~~> lblT ++ outsF ~~> lblF)
                  )
ifology' labelIn ctx expr lblT lblF = evalStateT (detach ctx) $ ifology labelIn expr lblT lblF

                  

compileExpr' : (labelIn : BlockLabel)
            -> (ctx : labelIn :~: VarCTX)
            -> (expr : Expr t)
            -> CompM  ( (lbl ** CFG CBlock (Undefined labelIn) (Undefined lbl))
                      , LLValue (GetLLType t)
                      )
compileExpr' labelIn ctx expr = evalStateT (detach ctx) $ compileExpr labelIn expr







--* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
-- Compilation ----------------------------------------------------------------
--* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
mutual
  {-
  TODO: Consider getting rid of `InstrCR` in favor of returning a dependent
  pair (lbls ** CFG _ ins (Defined $ lbls ~~> lbl))
  or (maybeLBL ** CFG _ ins (fromMaybe Closed $ map Undefined maybeLBL))
  -}

  
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



  --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  -- UU -----------------------------------------------------------------------
  --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  {-
  Returns a control flow graph that executes the instruction `instr`.
  The graph starts in a block labeled `labelIn` with `ctx` describing values of
  variables at the start of the graph.
  -}
  export
  compileInstrUU : (labelIn : BlockLabel)
                -> (ctx : labelIn :~: VarCTX)
                -> (instr : Instr)
                -> CompM (CompileResultUU labelIn $ InstrCR instr)




  -- Block --------------------------------------------------------------------
  compileInstrUU labelIn ctx (Block instrs) = compile' labelIn ctx instrs where

    mutual

      compile' : (labelIn : BlockLabel)
              -> labelIn :~: VarCTX
              -> (instrs : List Instr)
              -> CompM (CompileResultUU labelIn $ InstrsCR instrs)
      compile' labelIn ctx [] = pure (emptyCRUU labelIn)
      compile' labelIn ctx (instr :: instrs) = do
        res <- compileInstrUU labelIn ctx instr
        handleRes res instrs
        
      handleRes : {0 labelIn : BlockLabel}
              -> CompileResultUU labelIn crt
              -> (instrs : List Instr)
              -> CompM (CompileResultUU labelIn $ ClosedOr crt (InstrsCR instrs))
      handleRes (CRUUC g) instrs = pure (CRUUC g)
      handleRes (CRUUO (lbl ** g)) instrs = do
        res <- compile' lbl (getContext g) instrs
        pure $ connectCRUU g res
      

  -- Assign -------------------------------------------------------------------
  compileInstrUU labelIn ctx (Assign var expr) = do

    -- TODO: consider having attached context in the state
    ((lbl ** g), val) <- compileExpr' labelIn ctx expr
    
    let g' = omap {outs = Undefined} (assign var val) g

    let ctx' = getContext g'
    pure $ CRUUO (lbl ** g')
    
    
  -- If -----------------------------------------------------------------------
  compileInstrUU labelIn ctx instr@(If cond instrThen)
    = compileInstrUD labelIn !freshLabel ctx instr >>= collectOutsCR

  -- IfElse -------------------------------------------------------------------
  compileInstrUU labelIn ctx instr@(IfElse cond instrThen instrElse)
    = compileInstrUD labelIn !freshLabel ctx instr >>= collectOutsCR

  -- While --------------------------------------------------------------------
  compileInstrUU labelIn ctx instr@(While cond loop)
    = compileInstrUD labelIn !freshLabel ctx instr >>= collectOutsCR
              

  -- Return -------------------------------------------------------------------
  compileInstrUU labelIn ctx (Return expr) = do
    ((_ ** g), val) <- compileExpr' labelIn ctx expr
    
    let g' = omap {outs = Closed} (<+| Ret val) g
    pure (CRUUC g')


  -- RetVoid ------------------------------------------------------------------
  compileInstrUU labelIn ctx RetVoid = do
    let g = omap {outs = Closed} (<+| RetVoid) initCFG
    pure (CRUUC g)










  --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  -- UD -----------------------------------------------------------------------
  --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  export
  compileInstrUD : (labelIn, labelPost : BlockLabel)
                -> (ctx : labelIn :~: VarCTX)
                -> (instr : Instr)
                -> CompM (CompileResultUD labelIn labelPost $ InstrCR instr)

  -- Assign -------------------------------------------------------------------
  compileInstrUD labelIn labelPost ctx instr@(Assign var expr)
    = jumpTo labelPost <$> compileInstrUU labelIn ctx instr

  -- Return -------------------------------------------------------------------
  compileInstrUD labelIn labelPost ctx instr@(Return expr)
    = jumpTo labelPost <$> compileInstrUU labelIn ctx instr

  -- RetVoid ------------------------------------------------------------------
  compileInstrUD labelIn labelPost ctx instr@RetVoid
    = jumpTo labelPost <$> compileInstrUU labelIn ctx instr




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
                -> labelIn :~: VarCTX
                -> (instrs : List Instr)
                -> CompM (CompileResultUD labelIn labelPost $ InstrsCR instrs)
        compile' labelIn ctx Nil = pure (emptyCRUD labelIn labelPost)
        
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
            
            let CRUUO (lbl ** g) = the (CompileResultUU labelIn Open) $ rewrite revEq cro in res
            
            res' <- compile' lbl (getContext g) instrs
            
            let thm : (InstrsCR instrs = ClosedOr (InstrCR instr) (InstrsCR instrs))
                thm = rewrite cro in Refl
            
            pure $ rewrite revEq thm in connectCRUD g res'




  -- If -----------------------------------------------------------------------
  compileInstrUD labelIn labelPost ctx (If cond instrThen) = do

    labelThen <- freshLabel
    (outsT ** outsF ** condG) <- ifology' labelIn ctx cond labelThen labelPost
    let (ctxsT, ctxsF) = split (getContexts condG)
    
    thenRes <- compileInstrDD outsT labelThen labelPost ctxsT instrThen
    let (branchOuts ** thenG) = unwrapCRDD thenRes

    let final : CFG CBlock (Undefined labelIn) (Defined $ (branchOuts ++ outsF) ~~> labelPost)
        final = rewrite collect_concat labelPost branchOuts outsF
                in LBranch condG thenG
    
    pure $ CRUDO (branchOuts ++ outsF ** final)
    



  -- IfElse -------------------------------------------------------------------
  compileInstrUD labelIn labelPost ctx (IfElse cond instrThen instrElse) = do

    labelThen <- freshLabel
    labelElse <- freshLabel
    (outsT ** outsF ** condG) <- ifology' labelIn ctx cond labelThen labelElse
    let (ctxsT, ctxsF) = split (getContexts condG)

    thenRes <- compileInstrDD outsT labelThen labelPost ctxsT instrThen
    elseRes <- compileInstrDD outsF labelElse labelPost ctxsF instrElse

    let branches = parallelCR thenRes elseRes

    pure $ connectCRDDCRUD condG branches




  -- While --------------------------------------------------------------------
  compileInstrUD labelIn labelPost ctxIn instr@(While cond loop) = do
  
    labelNodeIn <- freshLabel

    let pre : CFG CBlock (Undefined labelIn) (Defined [labelIn ~> labelNodeIn])
        pre = SingleVertex {vouts = Just [labelNodeIn]}
            $ emptyCBlock (detach ctxIn) <+| Branch labelNodeIn

    connectCRDDCRUD pre <$> compileInstrDD [labelIn] labelNodeIn labelPost (getContexts pre) instr









  --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  -- DD -----------------------------------------------------------------------
  --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  compileInstrDDViaUD : (pre : List BlockLabel)
                     -> (labelIn, labelPost : BlockLabel)
                     -> (ctxs : DList (:~: VarCTX) (pre ~~> labelIn))
                     -> (instr : Instr)
                     -> CompM (CompileResultDD (pre ~~> labelIn) labelPost $ InstrCR instr)
  
  compileInstrDDViaUD pre labelIn labelPost ctxs instr = do
    SG ctx phis <- segregate ctxs
    res <- compileInstrUD labelIn labelPost ctx instr

    collectInsCR pre phis ctx res


  export
  compileInstrDD : (pre : List BlockLabel)
                -> (labelIn, labelPost : BlockLabel)
                -> (ctxs : DList (:~: VarCTX) (pre ~~> labelIn))
                -> (instr : Instr)
                -> CompM (CompileResultDD (pre ~~> labelIn) labelPost $ InstrCR instr)




  -- Block --------------------------------------------------------------------
  compileInstrDD pre labelIn labelPost ctxs instr@(Block instrs)
    = compileInstrDDViaUD pre labelIn labelPost ctxs instr

  -- Assign -------------------------------------------------------------------
  compileInstrDD pre labelIn labelPost ctxs instr@(Assign var expr)
    = compileInstrDDViaUD pre labelIn labelPost ctxs instr

  -- If -----------------------------------------------------------------------
  compileInstrDD pre labelIn labelPost ctxs instr@(If cond instrThen)
    = compileInstrDDViaUD pre labelIn labelPost ctxs instr

  -- IfElse -------------------------------------------------------------------
  compileInstrDD pre labelIn labelPost ctxs instr@(IfElse cond instrThen instrElse)
    = compileInstrDDViaUD pre labelIn labelPost ctxs instr

  -- Return -------------------------------------------------------------------
  compileInstrDD pre labelIn labelPost ctxs instr@(Return expr)
    = compileInstrDDViaUD pre labelIn labelPost ctxs instr
  
  -- RetVoid ------------------------------------------------------------------
  compileInstrDD pre labelIn labelPost ctxs instr@RetVoid
    = compileInstrDDViaUD pre labelIn labelPost ctxs instr
  



  -- While --------------------------------------------------------------------
  compileInstrDD pre labelNodeIn labelPost ctxsIn instr@(While cond loop) = do

    -- TODO: get rid of unnecessary assignments
    ctxNode' <- attach labelNodeIn <$> newRegForAll (commonKeys ctxsIn)
    let ctxNode = map (DMap.map LLVM.Var) ctxNode'

    ((labelNodeOut ** nodeG), val) <- compileExpr' labelNodeIn ctxNode cond
    labelLoop <- freshLabel

    let nodeG' = omap {outs = Just [labelLoop, labelPost]} (<+| CondBranch val labelLoop labelPost) nodeG
    let [ctxLoop, ctxPost] = getContexts nodeG'

    loopRes <- compileInstrDD [labelNodeOut] labelLoop labelNodeIn [ctxLoop] loop
    
    final <- handleLoopResult ctxNode' ctxsIn nodeG' loopRes

    
    
    pure $ CRDDO ([labelNodeOut] ** final)
    
    where

      phiFromDList : The t
                  -> (lbls : List BlockLabel)
                  -> DList (:~: (LLValue t)) (lbls ~~> lbl)
                  -> PhiExpr (MkInputs lbls) t

      phiFromDList (MkThe t) Nil Nil = Phi t Nil
      phiFromDList theT (lbl :: lbls) (val :: vals)
        = addInput lbl (detach val) (phiFromDList theT lbls vals)




      mkPhis : VarCTX'
            -> {lbls : List BlockLabel}
            -> DList (:~: VarCTX) (lbls ~~> lbl)
            -> CompM $ List (PhiInstr (MkInputs lbls))
      
      mkPhis ctx {lbls} ctxs = traverse mkPhi' (DMap.toList ctx) where
        
        mkPhi' : (DSum Variable (Reg . GetLLType))
              -> CompM $ PhiInstr (MkInputs lbls)

        mkPhi' (key :=> reg) = do

          vals <- dtraverse (traverse (getVal key)) ctxs

          let vals' = phiFromDList (map GetLLType $ typeOf key) lbls vals
          
          pure $ AssignPhi reg vals'

          where


            getVal : (key : Variable t) -> VarCTX -> CompM $ LLValue (GetLLType t)

            getVal key ctx = do
              let Just val  = VariableCTX.lookup key ctx
                            | Nothing => throwError $ Impossible "variable non existent in loop body or node context"
              pure val
      


      
      handleLoopResult : {pre : List BlockLabel}
                      -> {nodeIn, nodeOut, labelLoop : BlockLabel}
                      -> (ctxNode : nodeIn :~: VarCTX')
                      -> (ctxsIn : DList (:~: VarCTX) (pre ~~> nodeIn))
                      -> (node : CFG CBlock (Undefined nodeIn) (Defined [nodeOut ~> labelLoop, nodeOut ~> labelPost]))
                      -> (loopRes : CompileResultDD [nodeOut ~> labelLoop] nodeIn crt)
                      -> CompM $ CFG CBlock (Defined $ pre ~~> nodeIn) (Defined [nodeOut ~> labelPost])
      
      handleLoopResult {pre} ctxNode ctxsIn node (CRDDC loop) = do

        phis <- mkPhis (detach ctxNode) ctxsIn
        
        let node' = imap {ins = Just pre} (phis |++>) node
        let final = LBranch node' loop
        
        pure final

      handleLoopResult {pre, nodeIn, nodeOut} ctxNode ctxsIn node (CRDDO (loopOuts ** loop)) = do

        let ctxsLoopOut = getContexts loop
        
        let ctxs  : DList (:~: VarCTX) ((pre ++ loopOuts) ~~> nodeIn)
            ctxs  = rewrite collect_concat nodeIn pre loopOuts
                    in ctxsIn ++ ctxsLoopOut

        phis <- mkPhis (detach ctxNode) ctxs

        let node' : CFG CBlock (Defined $ pre ~~> nodeIn ++ loopOuts ~~> nodeIn) (Defined $ (nodeOut ~>> [labelLoop, labelPost]))
            node' = rewrite revEq $ collect_concat nodeIn pre loopOuts
                     in imap {ins = Just $ pre ++ loopOuts} (phis |++>) node
        
        let final = Cycle node' loop
        
        pure final













