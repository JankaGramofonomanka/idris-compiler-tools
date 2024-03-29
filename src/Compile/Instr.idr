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

{-
TODO: Figure out how to reduce the number of attachments and detachments
-}



--* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
-- Utils ----------------------------------------------------------------------
--* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
jumpTo : (labelPost : Label)
      -> (labelOut ** CFG (CBlock rt) (Undefined labelIn) (Undefined labelOut))
      -> CompileResult rt (Undefined labelIn) labelPost Simple
jumpTo labelPost (lbl ** g) = let
  g' = omap (<+| Branch labelPost) g
  in CRS ([lbl] ** g')

jumpFrom : (lbl : Label)
        -> CompileResult rt (Undefined lbl')        lbl'' k
        -> CompileResult rt (Defined [lbl ~> lbl']) lbl'' k
jumpFrom labelPre (CRR g) = CRR $ imap {ins = Just [labelPre]} ([] |++>) g
jumpFrom labelPre (CRS (lbls ** g)) = let
  g' = imap {ins = Just [labelPre]} ([] |++>) g
  in CRS (lbls ** g')

collectOuts : {labelPost : Label}
  -> (lbls ** CFG (CBlock rt) (Undefined labelIn) (Defined $ lbls ~~> labelPost))
  -> CompM $ (labelOut **  CFG (CBlock rt) (Undefined labelIn) (Undefined labelOut))
collectOuts {labelPost} (lbls ** g) = do
  SG ctx phis <- segregate (getContexts g)

  let ctxPost = ctx

  let post : CFG (CBlock rt) (Defined $ lbls ~~> labelPost) (Undefined labelPost)
      post = SingleVertex (phis |++:> emptyCBlock ctxPost)
  
  let final = Series g post

  pure (labelPost ** final)


ifology' : (labelIn : Label)
        -> (ctx : labelIn :~: VarCTX)
        -> (expr : Expr TBool)
        -> (lblT : Label)
        -> (lblF : Label)
        -> CompM  ( outsT ** outsF ** CFG (CBlock rt)
                                          (Undefined labelIn)
                                          (Defined $ outsT ~~> lblT ++ outsF ~~> lblF)
                  )
ifology' labelIn ctx expr lblT lblF = evalStateT (detach ctx) $ ifology labelIn expr lblT lblF

                  

compileExpr' : (labelIn : Label)
            -> (ctx : labelIn :~: VarCTX)
            -> (expr : Expr t)
            -> CompM  ( (lbl ** CFG (CBlock rt) (Undefined labelIn) (Undefined lbl))
                      , LLValue (GetLLType t)
                      )
compileExpr' labelIn ctx expr = evalStateT (detach ctx) $ compileExpr labelIn expr







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
  ||| Returns a control flow graph that executes the instruction `instr`.
  ||| The graph starts in a block labeled `labelIn` with `ctx` describing values of
  ||| variables at the start of the graph.
  export
  compileInstrUU : (labelIn : Label)
                -> (ctx : labelIn :~: VarCTX)
                -> (instr : Instr rt Simple)
                -> CompM (labelOut ** CFG (CBlock $ GetLLType rt) (Undefined labelIn) (Undefined labelOut))




  -- Block --------------------------------------------------------------------
  compileInstrUU labelIn ctx (Block instrs) = compile labelIn ctx instrs where

    compile : (labelIn : Label)
           -> (ctx : labelIn :~: VarCTX)
           -> (instrs : Instrs rt Simple)
           -> CompM (labelOut **  CFG (CBlock $ GetLLType rt) (Undefined labelIn) (Undefined labelOut))
    compile labelIn ctx Nil = pure (labelIn ** emptyCFG ctx)
    compile labelIn ctx (instr :: instrs) = do
      (lbl ** g) <- compileInstrUU labelIn ctx instr
      (lbl' ** g') <- compile lbl (getContext g) instrs
      pure $ (lbl' ** connect g g')

  -- Assign -------------------------------------------------------------------
  compileInstrUU labelIn ctx instr@(Assign var expr) = do

    -- TODO: consider having attached context in the state
    ((lbl ** g), val) <- compileExpr' labelIn ctx expr
    
    let g' = omap (assign var val . (<: prt instr)) g

    pure (lbl ** g')
    
  -- Exec ---------------------------------------------------------------------
  compileInstrUU labelIn ctx (Exec expr) = do
    ((lbl ** g), val) <- compileExpr' labelIn ctx expr
    pure (lbl ** g)
    
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
                 -> CompM (lbls ** CFG (CBlock $ GetLLType rt) (Undefined labelIn) (Defined $ lbls ~~> labelPost))
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
      ((_ ** g), val) <- compileExpr' labelIn ctx expr
      
      let g' = omap (<+| Ret val) g
      pure (CRR g')

  -- RetVoid ------------------------------------------------------------------
  compileInstrUD labelIn labelPost ctx instr@RetVoid = do
      let g = omap (<+| RetVoid) (emptyCFG ctx)
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
        (lbl ** g) <- compileInstrUU labelIn ctx instr
        res <- compile lbl (getContext g) instrs
        pure $ connectCR g res


  -- If -----------------------------------------------------------------------
  compileInstrUD labelIn labelPost ctx (If cond instrThen) = do

    labelThen <- freshLabel
    (outsT ** outsF ** condG) <- ifology' labelIn ctx cond labelThen labelPost
    let (ctxsT, ctxsF) = split (getContexts condG)
    
    (branchOuts ** thenG) <- compileInstrDD' outsT labelThen labelPost ctxsT instrThen
    
    let final : CFG (CBlock $ GetLLType rt) (Undefined labelIn) (Defined $ (branchOuts ++ outsF) ~~> labelPost)
        final = rewrite collect_concat labelPost branchOuts outsF
                in LBranch condG thenG
    
    pure $ CRS (branchOuts ++ outsF ** final)
    



  -- IfElse -------------------------------------------------------------------
  compileInstrUD labelIn labelPost ctx (IfElse cond instrThen instrElse) = do

    labelThen <- freshLabel
    labelElse <- freshLabel
    (outsT ** outsF ** condG) <- ifology' labelIn ctx cond labelThen labelElse
    let (ctxsT, ctxsF) = split (getContexts condG)

    thenRes <- compileInstrDD outsT labelThen labelPost ctxsT instrThen
    elseRes <- compileInstrDD outsF labelElse labelPost ctxsF instrElse

    let branches = parallelCR thenRes elseRes

    let final = seriesCR condG branches

    pure final




  -- While --------------------------------------------------------------------
  compileInstrUD labelIn labelPost ctxIn instr@(While cond loop) = do
  
    labelNodeIn <- freshLabel

    let pre : CFG (CBlock $ GetLLType rt) (Undefined labelIn) (Defined [labelIn ~> labelNodeIn])
        pre = SingleVertex (emptyCBlock ctxIn <+| Branch labelNodeIn)

    seriesCR pre <$> compileInstrDD [labelIn] labelNodeIn labelPost (getContexts pre) instr









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

    let preG = imap (phis |++:>) (emptyCFG ctx)
          
    pure $ connectCR preG res


  export
  compileInstrDD' : (pre : List Label)
                 -> (labelIn, labelPost : Label)
                 -> (ctxs : DList (:~: VarCTX) (pre ~~> labelIn))
                 -> (instr : Instr rt kind)
                 -> CompM (lbls ** CFG (CBlock $ GetLLType rt) (Defined $ pre ~~> labelIn) (Defined $ lbls ~~> labelPost))
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

    (outsT ** outsF ** nodeG) <- ifology' labelNodeIn ctxNode cond labelLoop labelPost
    let (ctxsLoop, ctxsPost) = split (getContexts nodeG)


    (loopOuts ** loop) <- compileInstrDD' outsT labelLoop labelNodeIn ctxsLoop loop
    
    let ctxsLoopOut = getContexts loop
    
    let ctxs  : DList (:~: VarCTX) ((pre ++ loopOuts) ~~> labelNodeIn)
        ctxs  = rewrite collect_concat labelNodeIn pre loopOuts
                in ctxsIn ++ ctxsLoopOut


    phis <- mkPhis ctxNode' ctxs

    let node' : CFG (CBlock $ GetLLType rt)
                    (Defined $ pre ~~> labelNodeIn ++ loopOuts ~~> labelNodeIn)
                    (Defined $ (outsT ~~> labelLoop) ++ (outsF ~~> labelPost))
        node' = rewrite revEq $ collect_concat labelNodeIn pre loopOuts
                in imap (phis |++:>) nodeG
    
    let final = Cycle node' loop
    
    pure $ CRS (outsF ** final)
    
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
                            | Nothing => throwError $ Impossible "variable non existent in loop body or node context"
              pure val
      















