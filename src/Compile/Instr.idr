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
jumpTo : (lblPost : Label)
      -> (lblOut ** CFG (CBlock rt) (Undefined lblIn) (Undefined lblOut))
      -> CompileResult rt (Undefined lblIn) lblPost Simple
jumpTo lblPost (lbl ** g) = let
  g' = omap (<+| Branch lblPost) g
  in CRS ([lbl] ** g')

jumpFrom : (lbl : Label)
        -> CompileResult rt (Undefined lbl')        lbl'' k
        -> CompileResult rt (Defined [lbl ~> lbl']) lbl'' k
jumpFrom lblPre (CRR g) = CRR $ imap {ins = Just [lblPre]} ([] |++>) g
jumpFrom lblPre (CRS (lbls ** g)) = let
  g' = imap {ins = Just [lblPre]} ([] |++>) g
  in CRS (lbls ** g')

collectOuts : {lblPost : Label}
  -> (lbls ** CFG (CBlock rt) (Undefined lblIn) (Defined $ lbls ~~> lblPost))
  -> CompM $ (lblOut **  CFG (CBlock rt) (Undefined lblIn) (Undefined lblOut))
collectOuts {lblPost} (lbls ** g) = do
  SG ctx phis <- segregate (getContexts g)

  let ctxPost = ctx

  let post : CFG (CBlock rt) (Defined $ lbls ~~> lblPost) (Undefined lblPost)
      post = SingleVertex (phis |++:> emptyCBlock ctxPost)

  let final = Series g post

  pure (lblPost ** final)


ifology' : (lblIn : Label)
        -> (ctx : lblIn :~: VarCTX)
        -> (expr : Expr TBool)
        -> (lblT : Label)
        -> (lblF : Label)
        -> CompM  ( outsT ** outsF ** CFG (CBlock rt)
                                          (Undefined lblIn)
                                          (Defined $ outsT ~~> lblT ++ outsF ~~> lblF)
                  )
ifology' lblIn ctx expr lblT lblF = evalStateT (detach ctx) $ ifology lblIn expr lblT lblF



compileExpr' : (lblIn : Label)
            -> (ctx : lblIn :~: VarCTX)
            -> (expr : Expr t)
            -> CompM  ( (lbl ** CFG (CBlock rt) (Undefined lblIn) (Undefined lbl))
                      , LLValue (GetLLType t)
                      )
compileExpr' lblIn ctx expr = evalStateT (detach ctx) $ compileExpr lblIn expr







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
  ||| The graph starts in a block labeled `lblIn` with `ctx` describing values of
  ||| variables at the start of the graph.
  export
  compileInstrUU : (lblIn : Label)
                -> (ctx : lblIn :~: VarCTX)
                -> (instr : Instr rt Simple)
                -> CompM (lblOut ** CFG (CBlock $ GetLLType rt) (Undefined lblIn) (Undefined lblOut))




  -- Block --------------------------------------------------------------------
  compileInstrUU lblIn ctx (Block instrs) = compile lblIn ctx instrs where

    compile : (lblIn : Label)
           -> (ctx : lblIn :~: VarCTX)
           -> (instrs : Instrs rt Simple)
           -> CompM (lblOut **  CFG (CBlock $ GetLLType rt) (Undefined lblIn) (Undefined lblOut))
    compile lblIn ctx Nil = pure (lblIn ** emptyCFG ctx)
    compile lblIn ctx (instr :: instrs) = do
      (lbl ** g) <- compileInstrUU lblIn ctx instr
      (lbl' ** g') <- compile lbl (getContext g) instrs
      pure $ (lbl' ** connect g g')

  -- Assign -------------------------------------------------------------------
  compileInstrUU lblIn ctx instr@(Assign var expr) = do

    -- TODO: consider having attached context in the state
    ((lbl ** g), val) <- compileExpr' lblIn ctx expr

    let g' = omap (assign var val . (<: prt instr)) g

    pure (lbl ** g')

  -- Exec ---------------------------------------------------------------------
  compileInstrUU lblIn ctx (Exec expr) = do
    ((lbl ** g), val) <- compileExpr' lblIn ctx expr
    pure (lbl ** g)

  -- If -----------------------------------------------------------------------
  compileInstrUU lblIn ctx instr@(If cond instrThen)
    = compileInstrUD' lblIn !freshLabel ctx instr >>= collectOuts

  -- IfElse -------------------------------------------------------------------
  compileInstrUU lblIn ctx instr@(IfElse {k = Simple, k' = Simple} cond instrThen instrElse)
    = compileInstrUD' lblIn !freshLabel ctx instr >>= collectOuts

  compileInstrUU lblIn ctx instr@(IfElse {k = Simple, k' = Returning} cond instrThen instrElse)
    = compileInstrUD' lblIn !freshLabel ctx instr >>= collectOuts

  compileInstrUU lblIn ctx instr@(IfElse {k = Returning, k' = Simple} cond instrThen instrElse)
    = compileInstrUD' lblIn !freshLabel ctx instr >>= collectOuts

  -- While --------------------------------------------------------------------
  compileInstrUU lblIn ctx instr@(While cond loop)
    = compileInstrUD' lblIn !freshLabel ctx instr >>= collectOuts








  --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  -- UD -----------------------------------------------------------------------
  --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  export
  compileInstrUD' : (lblIn, lblPost : Label)
                 -> (ctx : lblIn :~: VarCTX)
                 -> (instr : Instr rt kind)
                 -> CompM (lbls ** CFG (CBlock $ GetLLType rt) (Undefined lblIn) (Defined $ lbls ~~> lblPost))
  compileInstrUD' lblIn lblPost ctx instr = unwrapCR <$> compileInstrUD lblIn lblPost ctx instr

  export
  compileInstrUD : (lblIn, lblPost : Label)
                -> (ctx : lblIn :~: VarCTX)
                -> (instr : Instr rt kind)
                -> CompM (CompileResult (GetLLType rt) (Undefined lblIn) lblPost kind)

  -- Assign -------------------------------------------------------------------
  compileInstrUD lblIn lblPost ctx instr@(Assign var expr)
    = jumpTo lblPost <$> compileInstrUU lblIn ctx instr

  -- Exec ---------------------------------------------------------------------
  compileInstrUD lblIn lblPost ctx instr@(Exec expr)
    = jumpTo lblPost <$> compileInstrUU lblIn ctx instr

  -- Return -------------------------------------------------------------------
  compileInstrUD lblIn lblPost ctx instr@(Return expr) = do
      ((_ ** g), val) <- compileExpr' lblIn ctx expr

      let g' = omap (<+| Ret val) g
      pure (CRR g')

  -- RetVoid ------------------------------------------------------------------
  compileInstrUD lblIn lblPost ctx instr@RetVoid = do
      let g = omap (<+| RetVoid) (emptyCFG ctx)
      pure (CRR g)




  -- Block --------------------------------------------------------------------
  compileInstrUD lblIn lblPost ctx (Block instrs)
    = compile lblIn ctx instrs

    where

      compile : (lblIn : Label)
             -> (ctx : lblIn :~: VarCTX)
             -> (instrs : Instrs rt k)
             -> CompM (CompileResult (GetLLType rt) (Undefined lblIn) lblPost k)
      compile lblIn ctx Nil = pure (emptyCR lblIn lblPost ctx)
      compile lblIn ctx (TermSingleton instr) = compileInstrUD lblIn lblPost ctx instr
      compile lblIn ctx (instr :: instrs) = do
        (lbl ** g) <- compileInstrUU lblIn ctx instr
        res <- compile lbl (getContext g) instrs
        pure $ connectCR g res


  -- If -----------------------------------------------------------------------
  compileInstrUD lblIn lblPost ctx (If cond instrThen) = do

    lblThen <- freshLabel
    (outsT ** outsF ** condG) <- ifology' lblIn ctx cond lblThen lblPost
    let (ctxsT, ctxsF) = split (getContexts condG)

    (branchOuts ** thenG) <- compileInstrDD' outsT lblThen lblPost ctxsT instrThen

    let final : CFG (CBlock $ GetLLType rt) (Undefined lblIn) (Defined $ (branchOuts ++ outsF) ~~> lblPost)
        final = rewrite collect_concat lblPost branchOuts outsF
                in LBranch condG thenG

    pure $ CRS (branchOuts ++ outsF ** final)




  -- IfElse -------------------------------------------------------------------
  compileInstrUD lblIn lblPost ctx (IfElse cond instrThen instrElse) = do

    lblThen <- freshLabel
    lblElse <- freshLabel
    (outsT ** outsF ** condG) <- ifology' lblIn ctx cond lblThen lblElse
    let (ctxsT, ctxsF) = split (getContexts condG)

    thenRes <- compileInstrDD outsT lblThen lblPost ctxsT instrThen
    elseRes <- compileInstrDD outsF lblElse lblPost ctxsF instrElse

    let branches = parallelCR thenRes elseRes

    let final = seriesCR condG branches

    pure final




  -- While --------------------------------------------------------------------
  compileInstrUD lblIn lblPost ctxIn instr@(While cond loop) = do

    lblNodeIn <- freshLabel

    let pre : CFG (CBlock $ GetLLType rt) (Undefined lblIn) (Defined [lblIn ~> lblNodeIn])
        pre = SingleVertex (emptyCBlock ctxIn <+| Branch lblNodeIn)

    seriesCR pre <$> compileInstrDD [lblIn] lblNodeIn lblPost (getContexts pre) instr









  --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  -- DD -----------------------------------------------------------------------
  --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  compileInstrDDViaUD : (pre : List Label)
                     -> (lblIn, lblPost : Label)
                     -> (ctxs : DList (:~: VarCTX) (pre ~~> lblIn))
                     -> (instr : Instr rt kind)
                     -> CompM (CompileResult (GetLLType rt) (Defined $ pre ~~> lblIn) lblPost kind)

  compileInstrDDViaUD pre lblIn lblPost ctxs instr = do
    SG ctx phis <- segregate ctxs
    res <- compileInstrUD lblIn lblPost ctx instr

    let preG = imap (phis |++:>) (emptyCFG ctx)

    pure $ connectCR preG res


  export
  compileInstrDD' : (pre : List Label)
                 -> (lblIn, lblPost : Label)
                 -> (ctxs : DList (:~: VarCTX) (pre ~~> lblIn))
                 -> (instr : Instr rt kind)
                 -> CompM (lbls ** CFG (CBlock $ GetLLType rt) (Defined $ pre ~~> lblIn) (Defined $ lbls ~~> lblPost))
  compileInstrDD' pre lblIn lblPost ctxs instr = unwrapCR <$> compileInstrDD pre lblIn lblPost ctxs instr

  export
  compileInstrDD : (pre : List Label)
                -> (lblIn, lblPost : Label)
                -> (ctxs : DList (:~: VarCTX) (pre ~~> lblIn))
                -> (instr : Instr rt kind)
                -> CompM (CompileResult (GetLLType rt) (Defined $ pre ~~> lblIn) lblPost kind)




  -- Block --------------------------------------------------------------------
  compileInstrDD pre lblIn lblPost ctxs instr@(Block instrs)
    = compileInstrDDViaUD pre lblIn lblPost ctxs instr

  -- Assign -------------------------------------------------------------------
  compileInstrDD pre lblIn lblPost ctxs instr@(Assign var expr)
    = compileInstrDDViaUD pre lblIn lblPost ctxs instr

  -- Exec ---------------------------------------------------------------------
  compileInstrDD pre lblIn lblPost ctxs instr@(Exec expr)
    = compileInstrDDViaUD pre lblIn lblPost ctxs instr

  -- If -----------------------------------------------------------------------
  compileInstrDD pre lblIn lblPost ctxs instr@(If cond instrThen)
    = compileInstrDDViaUD pre lblIn lblPost ctxs instr

  -- IfElse -------------------------------------------------------------------
  compileInstrDD pre lblIn lblPost ctxs instr@(IfElse cond instrThen instrElse)
    = compileInstrDDViaUD pre lblIn lblPost ctxs instr

  -- Return -------------------------------------------------------------------
  compileInstrDD pre lblIn lblPost ctxs instr@(Return expr)
    = compileInstrDDViaUD pre lblIn lblPost ctxs instr

  -- RetVoid ------------------------------------------------------------------
  compileInstrDD pre lblIn lblPost ctxs instr@RetVoid
    = compileInstrDDViaUD pre lblIn lblPost ctxs instr




  -- While --------------------------------------------------------------------
  compileInstrDD pre lblNodeIn lblPost ctxsIn instr@(While cond loop) = do

    -- TODO: get rid of unnecessary assignments
    ctxNode' <-newRegForAll ctxsIn
    let ctxNode = map toValues ctxNode'

    lblLoop <- freshLabel

    (outsT ** outsF ** nodeG) <- ifology' lblNodeIn ctxNode cond lblLoop lblPost
    let (ctxsLoop, ctxsPost) = split (getContexts nodeG)


    (loopOuts ** loop) <- compileInstrDD' outsT lblLoop lblNodeIn ctxsLoop loop

    let ctxsLoopOut = getContexts loop

    let ctxs  : DList (:~: VarCTX) ((pre ++ loopOuts) ~~> lblNodeIn)
        ctxs  = rewrite collect_concat lblNodeIn pre loopOuts
                in ctxsIn ++ ctxsLoopOut


    phis <- mkPhis ctxNode' ctxs

    let node' : CFG (CBlock $ GetLLType rt)
                    (Defined $ pre ~~> lblNodeIn ++ loopOuts ~~> lblNodeIn)
                    (Defined $ (outsT ~~> lblLoop) ++ (outsF ~~> lblPost))
        node' = rewrite revEq $ collect_concat lblNodeIn pre loopOuts
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
















