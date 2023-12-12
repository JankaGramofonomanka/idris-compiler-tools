module Compile.Instr

import Data.List

import Control.Monad.State
import Control.Monad.Either

import Data.Some
import Data.Attached
import Data.Doc
import Data.DList
import Data.DSum
import Data.The
import Data.Typed

import LNG.TypeChecked
import LNG.TypeChecked.Render
import LLVM
import LLVM.Render

import Compile.Data.CBlock
import Compile.Data.CompileResult
import Compile.Data.CompM
import Compile.Data.Context
import Compile.Data.Context.Utils
import Compile.Data.Error
import Compile.Expr
import Compile.Utils

import CFG
import Theory

import Utils

{-
TODO: Figure out how to reduce the number of attachments and detachments
-}



--* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
-- Utils ----------------------------------------------------------------------
--* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
jumpTo : (labelPost : Label)
      -> DataUU rt labelIn
      -> CompileResult rt (Undefined labelIn) labelPost Simple
jumpTo labelPost dat = let
  (cfg, ctxs) = close labelPost dat.ctx dat.cfg
  in CRS $ MkDataXD { outs = [dat.lblOut], cfg, ctxs }

jumpFrom : (lbl : Label)
        -> CompileResult rt (Undefined lbl')        lbl'' k
        -> CompileResult rt (Defined [lbl ~> lbl']) lbl'' k
jumpFrom labelPre (CRR g) = CRR $ imap {ins = Just [labelPre]} ([] |++>) g
jumpFrom labelPre (CRS dat) = let
  cfg' = imap {ins = Just [labelPre]} ([] |++>) dat.cfg
  in CRS $ {cfg := cfg'} dat

collectOuts : {labelPost : Label}
  -> DataXD rt (Undefined labelIn) labelPost
  -> CompM $ DataUU rt labelIn
collectOuts {labelPost} dat = do
  SG ctx phis <- segregate dat.ctxs

  let post : CFG (CBlock rt) (Defined $ dat.outs ~~> labelPost) (Undefined labelPost)
      post = SingleVertex (phis |++:> emptyCBlock)
  
  let final = Series dat.cfg post

  pure $ MkDataUU { lblOut = labelPost, cfg = final, ctx }


ifology' : (labelIn : Label)
        -> (ctx : labelIn :~: VarCTX)
        -> (expr : Expr TBool)
        -> (lblT : Label)
        -> (lblF : Label)
        -> CompM $ DataXD2 rt (Undefined labelIn) lblT lblF
ifology' labelIn ctx expr lblT lblF = do
  (ctx, (outsT ** outsF ** cfg)) <- runStateT (detach ctx) $ ifology labelIn expr lblT lblF

  let ctxsT = replicate (outsT ~~> lblT) (`attach` ctx)
      ctxsF = replicate (outsF ~~> lblF) (`attach` ctx)

  pure $ MkDataXD2 { outsT, outsF, cfg, ctxsT, ctxsF }

                  

compileExpr' : (labelIn : Label)
            -> (ctx : labelIn :~: VarCTX)
            -> (expr : Expr t)
            -> CompM  ( DataUU rt labelIn
                      , LLValue (GetLLType t)
                      )
compileExpr' labelIn ctx expr = do
  (ctx, ((lblOut ** cfg), val)) <- runStateT (detach ctx) $ compileExpr labelIn expr

  pure (MkDataUU { lblOut, cfg, ctx = attach lblOut ctx }, val)







--* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
-- Compilation ----------------------------------------------------------------
--* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *

{-
TODO: Consider getting rid of `CompileResult` in favor of returning a dependent
pair (lbls ** CFG _ ins (Defined $ lbls ~~> lbl))
or (maybeLBL ** CFG _ ins (fromMaybe Closed $ map Undefined maybeLBL))
-}

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
  compileInstrUU : (labelIn : Label)
                -> (ctx : labelIn :~: VarCTX)
                -> (instr : Instr rt Simple)
                -> CompM $ DataUU (GetLLType rt) labelIn




  -- Block --------------------------------------------------------------------
  compileInstrUU labelIn ctx (Block instrs) = compile labelIn ctx instrs where

    compile : (labelIn : Label)
           -> (ctx : labelIn :~: VarCTX)
           -> (instrs : Instrs rt Simple)
           -> CompM $ DataUU (GetLLType rt) labelIn
    compile labelIn ctx Nil = pure $ MkDataUU { lblOut = labelIn, cfg = emptyCFG, ctx }
    compile labelIn ctx (instr :: instrs) = do
      dat  <- compileInstrUU labelIn ctx instr
      dat' <- compile dat.lblOut dat.ctx instrs
      pure $ { cfg $= connect dat.cfg } dat'

  -- Assign -------------------------------------------------------------------
  compileInstrUU labelIn ctx instr@(Assign var expr) = do

    (dat, val) <- compileExpr' labelIn ctx expr
    
    pure $ { -- add a comment marking the assignment and print the instruction
             cfg $= omap ((<: mkSentence [prt var, "~", prt val]) . (<: prt instr))
           , ctx $= map (insert var val)
           } dat

  -- Exec ---------------------------------------------------------------------
  compileInstrUU labelIn ctx (Exec expr) = do
    (dat, val) <- compileExpr' labelIn ctx expr
    pure dat

  -- If -----------------------------------------------------------------------
  compileInstrUU labelIn ctx instr@(If cond instrThen)
    = compileInstrUD' labelIn !freshLabel ctx instr >>= collectOuts

  -- IfElse -------------------------------------------------------------------
  compileInstrUU labelIn ctx instr@(IfElse {k = Simple, k' = Simple} cond instrThen instrElse)
    = compileInstrUD' labelIn !freshLabel ctx instr >>= collectOuts

  compileInstrUU labelIn ctx instr@(IfElse {k = Simple, k' = Returning} cond instrThen instrElse)
    = compileInstrUD' labelIn !freshLabel ctx instr >>= collectOuts

  compileInstrUU labelIn ctx instr@(IfElse {k = Returning, k' = Simple} cond instrThen instrElse)
    = compileInstrUD' labelIn !freshLabel ctx instr >>= collectOuts

  -- While --------------------------------------------------------------------
  compileInstrUU labelIn ctx instr@(While cond loop)
    = compileInstrUD' labelIn !freshLabel ctx instr >>= collectOuts








  --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  -- UD -----------------------------------------------------------------------
  --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  export
  compileInstrUD' : (labelIn, labelPost : Label)
                 -> (ctx : labelIn :~: VarCTX)
                 -> (instr : Instr rt kind)
                 -> CompM $ DataXD (GetLLType rt) (Undefined labelIn) labelPost
  compileInstrUD' labelIn labelPost ctx instr = unwrapCR <$> compileInstrUD labelIn labelPost ctx instr

  export
  compileInstrUD : (labelIn, labelPost : Label)
                -> (ctx : labelIn :~: VarCTX)
                -> (instr : Instr rt kind)
                -> CompM (CompileResult (GetLLType rt) (Undefined labelIn) labelPost kind)

  -- Assign -------------------------------------------------------------------
  compileInstrUD labelIn labelPost ctx instr@(Assign var expr)
    = jumpTo labelPost <$> compileInstrUU labelIn ctx instr
  
  -- Exec ---------------------------------------------------------------------
  compileInstrUD labelIn labelPost ctx instr@(Exec expr)
    = jumpTo labelPost <$> compileInstrUU labelIn ctx instr

  -- Return -------------------------------------------------------------------
  compileInstrUD labelIn labelPost ctx instr@(Return expr) = do
      (dat, val) <- compileExpr' labelIn ctx expr
      
      let cfg = omap (<+| Ret val) dat.cfg
      pure (CRR cfg)

  -- RetVoid ------------------------------------------------------------------
  compileInstrUD labelIn labelPost ctx instr@RetVoid = do
      let g = omap (<+| RetVoid) emptyCFG
      pure (CRR g)




  -- Block --------------------------------------------------------------------
  compileInstrUD labelIn labelPost ctx (Block instrs)
    = compile labelIn ctx instrs
    
    where

      compile : (labelIn : Label)
             -> (ctx : labelIn :~: VarCTX)
             -> (instrs : Instrs rt k)
             -> CompM (CompileResult (GetLLType rt) (Undefined labelIn) labelPost k)
      compile labelIn ctx Nil = pure (emptyCR labelIn labelPost ctx)
      compile labelIn ctx (TermSingleton instr) = compileInstrUD labelIn labelPost ctx instr
      compile labelIn ctx (instr :: instrs) = do
        dat <- compileInstrUU labelIn ctx instr
        res <- compile dat.lblOut dat.ctx instrs
        pure $ connectCR dat.cfg res


  -- If -----------------------------------------------------------------------
  compileInstrUD labelIn labelPost ctx (If cond instrThen) = do

    labelThen <- freshLabel
    condDat <- ifology' labelIn ctx cond labelThen labelPost
    
    branchDat <- compileInstrDD' condDat.outsT labelThen labelPost condDat.ctxsT instrThen
    
    let final : CFG (CBlock $ GetLLType rt) (Undefined labelIn) (Defined $ (branchDat.outs ++ condDat.outsF) ~~> labelPost)
        final = rewrite collect_concat labelPost branchDat.outs condDat.outsF
                in lbranch condDat.cfg branchDat.cfg

    let ctxs = rewrite collect_concat labelPost branchDat.outs condDat.outsF
               in branchDat.ctxs ++ condDat.ctxsF

    pure $ CRS (MkDataXD { outs = branchDat.outs ++ condDat.outsF, cfg = final, ctxs })
    



  -- IfElse -------------------------------------------------------------------
  compileInstrUD labelIn labelPost ctx (IfElse cond instrThen instrElse) = do

    labelThen <- freshLabel
    labelElse <- freshLabel
    condDat <- ifology' labelIn ctx cond labelThen labelElse

    thenRes <- compileInstrDD condDat.outsT labelThen labelPost condDat.ctxsT instrThen
    elseRes <- compileInstrDD condDat.outsF labelElse labelPost condDat.ctxsF instrElse

    let branches = parallelCR thenRes elseRes

    let final = seriesCR condDat.cfg branches

    pure final




  -- While --------------------------------------------------------------------
  compileInstrUD labelIn labelPost ctxIn instr@(While cond loop) = do
  
    labelNodeIn <- freshLabel

    let pre : ( CFG (CBlock $ GetLLType rt) (Undefined labelIn) (Defined [labelIn ~> labelNodeIn])
              , DList (:~: VarCTX) [labelIn ~> labelNodeIn]
              )
        pre = close labelNodeIn ctxIn emptyCFG
        
    (pre', ctxs) <- pure pre

    seriesCR pre' <$> compileInstrDD [labelIn] labelNodeIn labelPost ctxs instr









  --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  -- DD -----------------------------------------------------------------------
  --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  compileInstrDDViaUD : (pre : List Label)
                     -> (labelIn, labelPost : Label)
                     -> (ctxs : DList (:~: VarCTX) (pre ~~> labelIn))
                     -> (instr : Instr rt kind)
                     -> CompM (CompileResult (GetLLType rt) (Defined $ pre ~~> labelIn) labelPost kind)
  
  compileInstrDDViaUD pre labelIn labelPost ctxs instr = do
    SG ctx phis <- segregate ctxs
    res <- compileInstrUD labelIn labelPost ctx instr

    let preG = imap (phis |++:>) emptyCFG
          
    pure $ connectCR preG res


  export
  compileInstrDD' : (pre : List Label)
                 -> (labelIn, labelPost : Label)
                 -> (ctxs : DList (:~: VarCTX) (pre ~~> labelIn))
                 -> (instr : Instr rt kind)
                 -> CompM $ DataXD (GetLLType rt) (Defined $ pre ~~> labelIn) labelPost
  compileInstrDD' pre labelIn labelPost ctxs instr = unwrapCR <$> compileInstrDD pre labelIn labelPost ctxs instr

  export
  compileInstrDD : (pre : List Label)
                -> (labelIn, labelPost : Label)
                -> (ctxs : DList (:~: VarCTX) (pre ~~> labelIn))
                -> (instr : Instr rt kind)
                -> CompM (CompileResult (GetLLType rt) (Defined $ pre ~~> labelIn) labelPost kind)




  -- Block --------------------------------------------------------------------
  compileInstrDD pre labelIn labelPost ctxs instr@(Block instrs)
    = compileInstrDDViaUD pre labelIn labelPost ctxs instr

  -- Assign -------------------------------------------------------------------
  compileInstrDD pre labelIn labelPost ctxs instr@(Assign var expr)
    = compileInstrDDViaUD pre labelIn labelPost ctxs instr
  
  -- Exec ---------------------------------------------------------------------
  compileInstrDD pre labelIn labelPost ctxs instr@(Exec expr)
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
    ctxNode' <-newRegForAll ctxsIn
    let ctxNode = map toValues ctxNode'

    labelLoop <- freshLabel

    condDat <- ifology' labelNodeIn ctxNode cond labelLoop labelPost


    loopDat <- compileInstrDD' condDat.outsT labelLoop labelNodeIn condDat.ctxsT loop

    let ctxs  : DList (:~: VarCTX) ((pre ++ loopDat.outs) ~~> labelNodeIn)
        ctxs  = rewrite collect_concat labelNodeIn pre loopDat.outs
                in ctxsIn ++ loopDat.ctxs


    phis <- mkPhis ctxNode' ctxs

    let nodeG : CFG (CBlock $ GetLLType rt)
                    (Defined $ pre ~~> labelNodeIn ++ loopDat.outs ~~> labelNodeIn)
                    (Defined $ (condDat.outsT ~~> labelLoop) ++ (condDat.outsF ~~> labelPost))
        nodeG = rewrite revEq $ collect_concat labelNodeIn pre loopDat.outs
                in imap (phis |++:>) condDat.cfg

    let final = Cycle nodeG loopDat.cfg

    pure $ CRS (MkDataXD { outs = condDat.outsF, cfg = final, ctxs = condDat.ctxsF })

    where

      phiFromDList : The t
                  -> (lbls : List Label)
                  -> DList (:~: (LLValue t)) (lbls ~~> lbl)
                  -> PhiExpr lbls t

      phiFromDList (MkThe t) Nil Nil = Phi t Nil
      phiFromDList theT (lbl :: lbls) (val :: vals)
        = addInput lbl (detach val) (phiFromDList theT lbls vals)




      mkPhis : lbl :~: VarCTX'
            -> {lbls : List Label}
            -> DList (:~: VarCTX) (lbls ~~> lbl)
            -> CompM $ List (PhiInstr lbls, Maybe String)

      mkPhis ctx {lbls} ctxs = traverse mkPhi' (toList $ detach ctx) where
        
        mkPhi' : (DSum Variable (Reg . GetLLType))
              -> CompM (PhiInstr lbls, Maybe String)

        mkPhi' (key :=> reg) = do

          vals <- dtraverse (traverse (getVal key)) ctxs

          let vals' = phiFromDList (map GetLLType $ typeOf key) lbls vals
          
          pure $ (AssignPhi reg vals', Just $ prt key)

          where


            getVal : (key : Variable t) -> VarCTX -> CompM $ LLValue (GetLLType t)

            getVal key ctx = do
              let Just val  = lookup key ctx
                            | Nothing => throwError $ Impossible "variable non existent in loop body or nodeG context"
              pure val
      















