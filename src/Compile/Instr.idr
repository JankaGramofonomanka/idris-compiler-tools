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
import LLVM.Generalized

import Compile.Data.CBlock
import Compile.Data.CompileResult
import Compile.Data.CompM
import Compile.Data.Error
import Compile.Data.LLVM
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
jumpTo : (labelPost : BlockLabel)
      -> (labelOut ** CFG (CBlock rt) (Undefined labelIn) (Undefined labelOut))
      -> CompileResult rt (Undefined labelIn) labelPost Open
jumpTo labelPost (lbl ** g) = let
  g' = omap {outs = Just [labelPost]} (<+| Branch labelPost) g
  in CRO ([lbl] ** g')

collectOuts : {labelPost : BlockLabel}
  -> (lbls ** CFG (CBlock rt) (Undefined labelIn) (Defined $ lbls ~~> labelPost))
  -> CompM $ (labelOut **  CFG (CBlock rt) (Undefined labelIn) (Undefined labelOut))


collectOuts {labelPost} (lbls ** g) = do
  --SG ctxPost phis <- segregate (getContexts g)

  let post : CFG (CBlock rt) (Defined $ lbls ~~> labelPost) (Undefined labelPost)
      --post = SingleVertex {vins = Just lbls} $ phis |++:> emptyCBlock ctxPost
      post = SingleVertex {vins = Just lbls} $ [] |++:> emptyCBlock
  
  let final = Series g post

  pure (labelPost ** final)








--* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
-- Compilation ----------------------------------------------------------------
--* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *

{-
TODO: Consider getting rid of `GetCRT` in favor of returning a dependent
pair (lbls ** CFG _ ins (Defined $ lbls ~~> lbl))
or (maybeLBL ** CFG _ ins (fromMaybe Closed $ map Undefined maybeLBL))
-}
public export
GetCRT : InstrKind -> CRType
GetCRT Simple    = Open
GetCRT Returning = Closed

private
thmGetCRT : (k, k' : InstrKind) -> GetCRT (BrKind k k') = CRParallel (GetCRT k) (GetCRT k')
thmGetCRT Simple    Simple    = Refl
thmGetCRT Simple    Returning = Refl
thmGetCRT Returning Simple    = Refl
thmGetCRT Returning Returning = Refl

private
thmGetCRT' : {k, k' : InstrKind} -> GetCRT (BrKind k k') = CRParallel (GetCRT k) (GetCRT k')
thmGetCRT' {k, k'} = thmGetCRT k k'


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
                -> (instr : Instr rt Simple)
                -> CompM (labelOut ** CFG (CBlock $ GetLLType rt) (Undefined labelIn) (Undefined labelOut))



  -- Block --------------------------------------------------------------------
  compileInstrUU labelIn (Block instrs) = compile labelIn instrs where

    compile : (labelIn : BlockLabel)
           -> (instrs : Instrs rt Simple)
           -> CompM (labelOut **  CFG (CBlock $ GetLLType rt) (Undefined labelIn) (Undefined labelOut))
    compile labelIn Nil = pure (labelIn ** emptyCFG)
    compile labelIn (instr :: instrs) = do
      (lbl ** g) <- compileInstrUU labelIn instr
      (lbl' ** g') <- compile lbl instrs
      pure $ (lbl' ** connect g g')

  -- Assign -------------------------------------------------------------------
  compileInstrUU labelIn instr@(Assign var expr) = do

    -- TODO: consider having attached context in the state
    ((lbl ** g), val) <- compileExpr labelIn expr
    
    let g' = omap {outs = Undefined} (<: prt instr) g

    pure (lbl ** g')
    
  -- Exec ---------------------------------------------------------------------
  compileInstrUU labelIn (Exec expr) = do
    ((lbl ** g), val) <- compileExpr labelIn expr
    pure (lbl ** g)
    
  -- If -----------------------------------------------------------------------
  compileInstrUU labelIn instr@(If cond instrThen)
    = compileInstrUD' labelIn !freshLabel instr >>= collectOuts

  -- IfElse -------------------------------------------------------------------
  compileInstrUU labelIn instr@(IfElse {k = Simple, k' = Simple} cond instrThen instrElse)
    = compileInstrUD' labelIn !freshLabel instr >>= collectOuts

  compileInstrUU labelIn instr@(IfElse {k = Simple, k' = Returning} cond instrThen instrElse)
    = compileInstrUD' labelIn !freshLabel instr >>= collectOuts

  compileInstrUU labelIn instr@(IfElse {k = Returning, k' = Simple} cond instrThen instrElse)
    = compileInstrUD' labelIn !freshLabel instr >>= collectOuts

  -- While --------------------------------------------------------------------
  compileInstrUU labelIn instr@(While cond loop)
    = compileInstrUD' labelIn !freshLabel instr >>= collectOuts







  --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  -- UD -----------------------------------------------------------------------
  --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  export
  compileInstrUD' : (labelIn, labelPost : BlockLabel)
                 -> (instr : Instr rt kind)
                 -> CompM (lbls ** CFG (CBlock $ GetLLType rt) (Undefined labelIn) (Defined $ lbls ~~> labelPost))
  compileInstrUD' labelIn labelPost instr = unwrapCR <$> compileInstrUD labelIn labelPost instr

  export
  compileInstrUD : (labelIn, labelPost : BlockLabel)
                -> (instr : Instr rt kind)
                -> CompM (CompileResult (GetLLType rt) (Undefined labelIn) labelPost $ GetCRT kind)

  -- Assign -------------------------------------------------------------------
  compileInstrUD labelIn labelPost instr@(Assign var expr)
    = jumpTo labelPost <$> compileInstrUU labelIn instr
  
  -- Exec ---------------------------------------------------------------------
  compileInstrUD labelIn labelPost instr@(Exec expr)
    = jumpTo labelPost <$> compileInstrUU labelIn instr

  -- Return -------------------------------------------------------------------
  compileInstrUD labelIn labelPost instr@(Return expr) = do
      ((_ ** g), val) <- compileExpr labelIn expr
      
      let g' = omap {outs = Closed} (<+| Ret val) g
      pure (CRC g')

  -- RetVoid ------------------------------------------------------------------
  compileInstrUD labelIn labelPost instr@RetVoid = do
      let g = omap {outs = Closed} (<+| RetVoid) emptyCFG
      pure (CRC g)




  -- Block --------------------------------------------------------------------
  compileInstrUD labelIn labelPost (Block instrs)
    = compile labelIn instrs
    
    where

      compile : (labelIn : BlockLabel)
             -> (instrs : Instrs rt k)
             -> CompM (CompileResult (GetLLType rt) (Undefined labelIn) labelPost $ GetCRT k)
      compile labelIn Nil = pure (emptyCR labelIn labelPost)
      compile labelIn (TermSingleton instr) = compileInstrUD labelIn labelPost instr
      compile labelIn (instr :: instrs) = do
        (lbl ** g) <- compileInstrUU labelIn instr
        res <- compile lbl instrs
        pure $ connectCR g res


  -- If -----------------------------------------------------------------------
  compileInstrUD labelIn labelPost (If cond instrThen) = do

    labelThen <- freshLabel
    (outsT ** outsF ** condG) <- ifology labelIn cond labelThen labelPost
    
    (branchOuts ** thenG) <- compileInstrDD' outsT labelThen labelPost instrThen
    
    let final : CFG (CBlock $ GetLLType rt) (Undefined labelIn) (Defined $ (branchOuts ++ outsF) ~~> labelPost)
        final = rewrite collect_concat labelPost branchOuts outsF
                in LBranch condG thenG
    
    pure $ CRO (branchOuts ++ outsF ** final)
    



  -- IfElse -------------------------------------------------------------------
  compileInstrUD labelIn labelPost (IfElse {k, k'} cond instrThen instrElse) = do

    labelThen <- freshLabel
    labelElse <- freshLabel
    (outsT ** outsF ** condG) <- ifology labelIn cond labelThen labelElse
    
    thenRes <- compileInstrDD outsT labelThen labelPost instrThen
    elseRes <- compileInstrDD outsF labelElse labelPost instrElse

    let branches = parallelCR thenRes elseRes

    let final : CompileResult (GetLLType rt)
                              (Undefined labelIn)
                              labelPost
                              (GetCRT $ BrKind k k')
        final = rewrite thmGetCRT k k'
                in seriesCR condG branches

    pure final




  -- While --------------------------------------------------------------------
  compileInstrUD labelIn labelPost instr@(While cond loop) = do
  
    labelNodeIn <- freshLabel

    let pre : CFG (CBlock $ GetLLType rt) (Undefined labelIn) (Defined [labelIn ~> labelNodeIn])
        pre = SingleVertex {vouts = Just [labelNodeIn]}
            $ emptyCBlock <+| Branch labelNodeIn

    seriesCR pre <$> compileInstrDD [labelIn] labelNodeIn labelPost instr







  --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  -- DD -----------------------------------------------------------------------
  --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  compileInstrDDViaUD : (pre : List BlockLabel)
                     -> (labelIn, labelPost : BlockLabel)
                     -> (instr : Instr rt kind)
                     -> CompM (CompileResult (GetLLType rt) (Defined $ pre ~~> labelIn) labelPost $ GetCRT kind)
  
  compileInstrDDViaUD pre labelIn labelPost instr = do
    --SG ctx phis <- segregate ctxs
    --res <- compileInstrUD labelIn labelPost ctx instr
    res <- compileInstrUD labelIn labelPost instr

    --let preG = imap {ins = Just pre} (phis |++:>) (emptyCFG ctx)
    let preG = imap {ins = Just pre} ([] |++:>) emptyCFG
          
    pure $ connectCR preG res

  export
  compileInstrDD' : (pre : List BlockLabel)
                 -> (labelIn, labelPost : BlockLabel)
                 -> (instr : Instr rt kind)
                 -> CompM (lbls ** CFG (CBlock $ GetLLType rt) (Defined $ pre ~~> labelIn) (Defined $ lbls ~~> labelPost))
  compileInstrDD' pre labelIn labelPost instr = unwrapCR <$> compileInstrDD pre labelIn labelPost instr

  export
  compileInstrDD : (pre : List BlockLabel)
                -> (labelIn, labelPost : BlockLabel)
                -> (instr : Instr rt kind)
                -> CompM (CompileResult (GetLLType rt) (Defined $ pre ~~> labelIn) labelPost $ GetCRT kind)



  -- Block --------------------------------------------------------------------
  compileInstrDD pre labelIn labelPost instr@(Block instrs)
    = compileInstrDDViaUD pre labelIn labelPost instr

  -- Assign -------------------------------------------------------------------
  compileInstrDD pre labelIn labelPost instr@(Assign var expr)
    = compileInstrDDViaUD pre labelIn labelPost instr
  
  -- Exec ---------------------------------------------------------------------
  compileInstrDD pre labelIn labelPost instr@(Exec expr)
    = compileInstrDDViaUD pre labelIn labelPost instr

  -- If -----------------------------------------------------------------------
  compileInstrDD pre labelIn labelPost instr@(If cond instrThen)
    = compileInstrDDViaUD pre labelIn labelPost instr

  -- IfElse -------------------------------------------------------------------
  compileInstrDD pre labelIn labelPost instr@(IfElse cond instrThen instrElse)
    = compileInstrDDViaUD pre labelIn labelPost instr

  -- Return -------------------------------------------------------------------
  compileInstrDD pre labelIn labelPost instr@(Return expr)
    = compileInstrDDViaUD pre labelIn labelPost instr
  
  -- RetVoid ------------------------------------------------------------------
  compileInstrDD pre labelIn labelPost instr@RetVoid
    = compileInstrDDViaUD pre labelIn labelPost instr
  



  -- While --------------------------------------------------------------------
  compileInstrDD pre labelNodeIn labelPost instr@(While cond loop) = do

    -- TODO: get rid of unnecessary assignments
    --ctxNode' <- attach labelNodeIn <$> newRegForAll (commonKeys ctxsIn)
    --let ctxNode = map toValues ctxNode'

    --((labelNodeOut ** nodeG), val) <- compileExpr labelNodeIn ctxNode cond
    ((labelNodeOut ** nodeG), val) <- compileExpr labelNodeIn cond
    labelLoop <- freshLabel

    let nodeG' = omap {outs = Just [labelLoop, labelPost]} (<+| CondBranch val labelLoop labelPost) nodeG
    --let [ctxLoop, ctxPost] = getContexts nodeG'

    --(loopOuts ** loop) <- compileInstrDD' [labelNodeOut] labelLoop labelNodeIn [ctxLoop] loop
    (loopOuts ** loop) <- compileInstrDD' [labelNodeOut] labelLoop labelNodeIn loop
    
    --let ctxsLoopOut = getContexts loop
    
    --let ctxs  : DList (:~: VarCTX) ((pre ++ loopOuts) ~~> labelNodeIn)
    --    ctxs  = rewrite collect_concat labelNodeIn pre loopOuts
    --            in ctxsIn ++ ctxsLoopOut


    --phis <- mkPhis (detach ctxNode') ctxs

    let node' : CFG (CBlock $ GetLLType rt)
                    (Defined $ pre ~~> labelNodeIn ++ loopOuts ~~> labelNodeIn)
                    (Defined $ (labelNodeOut ~>> [labelLoop, labelPost]))
        node' = rewrite revEq $ collect_concat labelNodeIn pre loopOuts
                  --in imap {ins = Just $ pre ++ loopOuts} (phis |++:>) nodeG'
                  in imap {ins = Just $ pre ++ loopOuts} ([] |++:>) nodeG'
    
    let final = Cycle node' loop
    
    pure $ CRO ([labelNodeOut] ** final)

    {-    
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
            -> CompM $ List (PhiInstr (MkInputs lbls), Maybe String)
      
      mkPhis ctx {lbls} ctxs = traverse mkPhi' (toList ctx) where
        
        mkPhi' : (DSum Variable (Reg . GetLLType))
              -> CompM (PhiInstr (MkInputs lbls), Maybe String)

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
    -}













