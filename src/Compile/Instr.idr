||| A module defijning the compilation of LNG instructions
|||
||| Termonology used in this module:
|||
||| ## input/output edges
||| * The *input edges* of a graph are the edges from vertices outside of that
|||   graph to vertices inside it.
||| * By analogy, the *output edges* of a graph are the edges from vertices
|||   inside that graph to vertices outside of it.
|||
||| ## undefined inputs/outputs
||| * A graph has an *undefined input* if it contains a block (a vertex) that
|||   is incomplete at the beginning.
||| * By analogy, a graph has an *undefined output* if it contains a block that
|||   is incomplete at the end.
|||
||| ## input/output block
||| * An *input block* of a graph is a block that contains an entry point to
|||   that graph.
|||   In other words:
|||   - a block whose predecessors are not in the graph,
|||   - or a block that is the destination of some of the input edges.
||| * By analogy, an *output block* of a graph is a block that contains an exit
|||   point from that graph.
|||   In other words:
|||   - a block whose succecessors are not in the graph,
|||   - or a block that is the source of some of the output edges.
|||
||| ## input/output label
||| * An *input label* is a label of an input block
||| * By analogy, an *output label* is a label of an output block
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
||| Adds a jump instruction at the end of a graph with a single undefined
||| output, thus defining its outputs.
||| @ lblPost the label of the block to jump to
||| @ lblOut  the label of the undefined output block
|||         / the output label of the graph to be modified
||| @ rt      the return type of the function whose body the returned graph
|||           will be part of
||| @ lblIn   the input label of the graph
jumpTo
   : (lblPost : Label)
  -> ( lblOut
    ** ( CFG (CBlock rt) (Undefined lblIn) (Undefined lblOut)
       , lblOut :~: VarCTX
       )
     )
  -> CompileResult rt (Undefined lblIn) lblPost Simple
jumpTo lblPost (lbl ** (g, ctx))
  = CRS ([lbl] ** (close lblPost ctx g))

||| Defines the inputs of a graph (wrapped in a "compile result")
||| @ lbl the source of the input edge of the returned graph.
||| @ res the graph (wrapped in a "compile result") whose inputs are to be
|||       defined.
jumpFrom
   : (lbl : Label)
  -> (res : CompileResult rt (Undefined       lbl')  lbl'' k)
  ->        CompileResult rt (Defined [lbl ~> lbl']) lbl'' k
jumpFrom lblPre (CRR g) = CRR $ imap {ins = Just [lblPre]} ([] |++>) g
jumpFrom lblPre (CRS (lbls ** (g, ctxs))) = let
  g' = imap {ins = Just [lblPre]} ([] |++>) g
  in CRS (lbls ** (g', ctxs))

||| Appends a merging block to a graph with multiple converging otuput edges
||| The merging block is incomplete at the end and thus thereturned graph has
||| a single undefined output.
||| @ lblPost the label of the merging block
|||         / the destination of the output edges of the graph
||| @ lbls    the output labels of the graph to be modified
|||         / te sources of the output edges of the graph to be modified
||| @ lblIn   the input label of the graph
||| @ rt      the return type of the function whose body the returned graph
|||           will be part of
collectOuts
   : {lblPost : Label}
  -> ( lbls
    ** ( CFG (CBlock rt) (Undefined lblIn) (Defined $ lbls ~~> lblPost)
       , DList (:~: VarCTX) (lbls ~~> lblPost)
       )
     )
  -> CompM
     ( lblOut
    ** ( CFG (CBlock rt) (Undefined lblIn) (Undefined lblOut)
       , lblOut :~: VarCTX
       )
     )
collectOuts {lblPost} (lbls ** (g, ctxs)) = do
  -- Merge the contexts coming from the different outputs of the graph
  SG ctxPost phis <- segregate ctxs

  -- Construct the merging block and pit it in a singleton graph
  let post : CFG (CBlock rt) (Defined $ lbls ~~> lblPost) (Undefined lblPost)
      post = SingleVertex (phis |++:> emptyCBlock)

  -- Connect the graph with the merging block
  let final = Series g post

  -- Return the final graph, its output label, and output context
  pure (lblPost ** (final, ctxPost))

||| A wrapper around `ifology`.
||| Using it avoids the unsafe "detaching" of a variable context from a label.
||| @ lblIn the input label of the returned graph
||| @ ctx   the context at the beginning of the returned graph
||| @ expr  the expression to be compiled
||| @ lblT  the "true" label
||| @ lblF  the "false" label
||| @ outsT the "true" outputs
||| @ outsF the "false" outputs
||| @ rt    the return type of the function whose body the returned graph will
|||         be part of
ifology'
   : (lblIn : Label)
  -> (ctx  : lblIn :~: VarCTX)
  -> (expr : Expr TBool)
  -> (lblT : Label)
  -> (lblF : Label)
  -> CompM ( outsT
          ** outsF
          ** ( CFG (CBlock rt)
                   (Undefined lblIn)
                   (Defined $ outsT ~~> lblT ++ outsF ~~> lblF)
             , DList (:~: VarCTX) (outsT ~~> lblT)
             , DList (:~: VarCTX) (outsF ~~> lblF)
             )
           )
ifology' lblIn ctx expr lblT lblF = do
  -- Detatch the context from the labe, to run `ifology`
  (ctx, (outsT ** outsF ** cfg)) <- runStateT (detach ctx) $ ifology lblIn expr lblT lblF

  -- Attatch the context to the output edges of the resultingh graph
  let ctxsT = replicate (outsT ~~> lblT) (`attach` ctx)
      ctxsF = replicate (outsF ~~> lblF) (`attach` ctx)

  -- Return the graph, its outputs and output contexts
  pure (outsT ** outsF ** (cfg, ctxsT, ctxsF))

||| A wrapper around `compileExpr`.
||| Using it avoids the unsafe "detaching" of a variable context from a label.
||| @ lblIn  the input label of the returned graph
||| @ ctx    the context at the beginning of the returned graph
||| @ expr   the expression to be compiled
||| @ lblOut the input label of the returned graph
||| @ rt     the return type of the function whose body the returned graph will
|||          be part of
compileExpr'
   : (lblIn : Label)
  -> (ctx  : lblIn :~: VarCTX)
  -> (expr : Expr t)
  -> CompM ( ( lblOut
            ** ( CFG (CBlock rt) (Undefined lblIn) (Undefined lblOut)
               , lblOut :~: VarCTX
               )
             )
           , LLValue (GetLLType t)
           )

-- TODO: consider having attached context in the state
compileExpr' lblIn ctx expr = do

  -- Detatch the context from the labe, to run `ifology`
  (ctx, ((lbl ** cfg), val)) <- runStateT (detach ctx) $ compileExpr lblIn expr

  -- Return the graph, its output label, output context,
  -- and the value of the expression
  pure ((lbl ** (cfg, attach lbl ctx)), val)


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
  ||| Compile a simple instruction int a graph a single undefined input and
  ||| a signle undefined.
  ||| Returns the graph and the label of its output block.
  ||| @ lblIn  the input label of the graph
  ||| @ ctx    the context at the beginning of the graph
  ||| @ instr  the instruction to compile
  ||| @ rt     the return type of the function whose body the instruction is
  |||          part of
  ||| @ lblOut the input label of the graph
  export
  compileInstrUU
     : (lblIn : Label)
    -> (ctx   : lblIn :~: VarCTX)
    -> (instr : Instr rt Simple)
    -> CompM ( lblOut
            ** ( CFG (CBlock $ GetLLType rt) (Undefined lblIn) (Undefined lblOut)
               , lblOut :~: VarCTX
               )
             )

  -- A block of instructions
  compileInstrUU lblIn ctx (Block instrs) = compile lblIn ctx instrs where

    ||| Compile each instruction and connect their graphs together
    compile
       : (lblIn  : Label)
      -> (ctx    : lblIn :~: VarCTX)
      -> (instrs : Instrs rt Simple)
      -> CompM ( lblOut
              ** ( CFG (CBlock $ GetLLType rt) (Undefined lblIn) (Undefined lblOut)
                 , lblOut :~: VarCTX
                 )
               )
    -- Nothing to do, return an empty graph and an unchanged context
    compile lblIn ctx Nil = pure (lblIn ** (emptyCFG, ctx))

    compile lblIn ctxIn (instr :: instrs) = do
      -- Compile the head and the tail
      (lblMid ** (g,  ctxMid)) <- compileInstrUU lblIn  ctxIn  instr
      (lblOut ** (g', ctxOut)) <- compile        lblMid ctxMid instrs

      -- Connect the results
      pure $ (lblOut ** (connect g g', ctxOut))

  -- An assignment
  compileInstrUU lblIn ctx instr@(Assign var expr) = do

    -- Compile the assigned expression
    ((lblOut ** (g, ctx')), val) <- compileExpr' lblIn ctx expr

    -- Assign the value of that expressions to the variable in the variable
    -- context
    let ctx'' = map (insert var val) ctx'
        -- add a comment marking the assignment and print the instruction
        g' = omap ((<: mkSentence [prt var, "~", prt val]) . (<: prt instr)) g

    pure (lblOut ** (g', ctx''))

  -- An execution of an expression
  compileInstrUU lblIn ctx (Exec expr) = do
    -- compile the expression and ignore its value
    ((lbl ** g), val) <- compileExpr' lblIn ctx expr
    pure (lbl ** g)

  -- Compile the following via `compileInstrUD` and add a merging block -------
  -- An if-then statement
  compileInstrUU lblIn ctx instr@(If cond instrThen)
    = compileInstrUD' lblIn !freshLabel ctx instr >>= collectOuts

  -- An if-then-else statement
  -- Pattern match on the kinds of the branch instructions to appease the type
  -- checker
  compileInstrUU lblIn ctx instr@(IfElse {k = Simple, k' = Simple} cond instrThen instrElse)
    = compileInstrUD' lblIn !freshLabel ctx instr >>= collectOuts

  compileInstrUU lblIn ctx instr@(IfElse {k = Simple, k' = Returning} cond instrThen instrElse)
    = compileInstrUD' lblIn !freshLabel ctx instr >>= collectOuts

  compileInstrUU lblIn ctx instr@(IfElse {k = Returning, k' = Simple} cond instrThen instrElse)
    = compileInstrUD' lblIn !freshLabel ctx instr >>= collectOuts

  -- Impossible, because the kind of the instruction is `Simple`
  compileInstrUU lblIn ctx instr@(IfElse {k = Returning, k' = Returning} cond instrThen instrElse)
    impossible

  -- A while loop
  compileInstrUU lblIn ctx instr@(While cond loop)
    = compileInstrUD' lblIn !freshLabel ctx instr >>= collectOuts

  --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  -- UD -----------------------------------------------------------------------
  --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

  ||| A wrapper around `compileInstrUD` that converts the "compile result" into
  ||| a dependent pair of the graph, its output contexts, and its output labels,
  ||| thus dropping the information whether the graph is returning or not.
  ||| @ lblIn   the input label of the graph
  ||| @ lblPost label of a block succeding the graph
  |||         / the destination of the output edges of the graph
  ||| @ ctx     the context at the beginning of the graph
  ||| @ instr   the instruction to compile
  ||| @ rt      the return type of the function whose body the instruction is
  |||           part of
  ||| @ kind    the kind of the compiled instruction - "simple" or "returning"
  ||| @ lbls    the output labels of the graph
  export
  compileInstrUD'
     : (lblIn, lblPost : Label)
    -> (ctx            : lblIn :~: VarCTX)
    -> (instr          : Instr rt kind)
    -> CompM ( lbls
            ** ( CFG (CBlock $ GetLLType rt) (Undefined lblIn) (Defined $ lbls ~~> lblPost)
               , DList (:~: VarCTX) (lbls ~~> lblPost)
               )
             )
  compileInstrUD' lblIn lblPost ctx instr = unwrapCR <$> compileInstrUD lblIn lblPost ctx instr

  ||| Compile an instruction of any kind into a graph with defined outputs and
  ||| a single undefined input.
  ||| Returns the graph as a "compile result"
  ||| @ lblIn   the input label of the graph
  ||| @ lblPost label of a block succeding the graph
  |||         / the destination of the output edges of the graph
  ||| @ ctx     the context at the beginning of the graph
  ||| @ instr   the instruction to compile
  ||| @ rt      the return type of the function whose body the instruction is
  |||           part of
  ||| @ kind    the kind of the compiled instruction - "simple" or "returning"
  export
  compileInstrUD
     : (lblIn, lblPost : Label)
    -> (ctx            : lblIn :~: VarCTX)
    -> (instr          : Instr rt kind)
    -> CompM (CompileResult (GetLLType rt) (Undefined lblIn) lblPost kind)

  -- An assignment
  -- Compile via `compileInstrUU` and add jump statement
  compileInstrUD lblIn lblPost ctx instr@(Assign var expr)
    = jumpTo lblPost <$> compileInstrUU lblIn ctx instr

  -- An execution of an expression
  -- Compile via `compileInstrUU` and add jump statement
  compileInstrUD lblIn lblPost ctx instr@(Exec expr)
    = jumpTo lblPost <$> compileInstrUU lblIn ctx instr

  -- A return statement
  compileInstrUD lblIn lblPost ctx instr@(Return expr) = do
      -- Compile the returned expression
      ((_ ** (g, _)), val) <- compileExpr' lblIn ctx expr

      -- Add a return statement
      let g' = omap (<+| Ret val) g
      pure (CRR g')

  -- A void return statement
  compileInstrUD lblIn lblPost ctx instr@RetVoid = do
      -- Return a singleton graph consisting only of a return statement
      let g = omap (<+| RetVoid) emptyCFG
      pure (CRR g)

  -- A block of instructions
  compileInstrUD lblIn lblPost ctx (Block instrs)
    = compile lblIn ctx instrs

    where

      ||| Compile each instruction and connect their graphs together
      compile : (lblIn : Label)
             -> (ctx : lblIn :~: VarCTX)
             -> (instrs : Instrs rt k)
             -> CompM (CompileResult (GetLLType rt) (Undefined lblIn) lblPost k)
      -- Nothing to do, return an empty graph
      compile lblIn ctx Nil = pure (emptyCR lblIn lblPost ctx)

      -- Compile the terminating instruction via `compileInstrUD`
      compile lblIn ctx (TermSingleton instr) = compileInstrUD lblIn lblPost ctx instr

      compile lblIn ctx (instr :: instrs) = do
        -- Compile the head and the tail
        (lblMid ** (g, ctx)) <- compileInstrUU lblIn  ctx instr
        res                  <- compile        lblMid ctx instrs

        -- Connect the results
        pure $ connectCR g res

  -- An if-then statement
  compileInstrUD lblIn lblPost ctx (If cond instrThen) = do

    -- Generate the input labelof the branch sub-graph
    lblThen <- freshLabel

    -- Compile the condition through jump statements
    (outsT ** outsF ** (condG, ctxsT, ctxsF)) <- ifology' lblIn ctx cond lblThen lblPost

    -- Compile the branch
    (branchOuts ** (thenG, ctxsT')) <- compileInstrDD' outsT lblThen lblPost ctxsT instrThen

    -- Construct the final graph by connecting the condition graph with the
    -- branch graph
    let final : CFG (CBlock $ GetLLType rt) (Undefined lblIn) (Defined $ (branchOuts ++ outsF) ~~> lblPost)
        final = rewrite collect_concat lblPost branchOuts outsF
                in LBranch condG thenG

    let ctxs = rewrite collect_concat lblPost branchOuts outsF
               in ctxsT' ++ ctxsF

    -- Return the graph and its output labels
    pure $ CRS (branchOuts ++ outsF ** (final, ctxs))

  -- An if-then-else statement
  compileInstrUD lblIn lblPost ctx (IfElse cond instrThen instrElse) = do

    -- Generate the input labels of the branches
    lblThen <- freshLabel
    lblElse <- freshLabel

    -- Compile the condition through jump statements
    (outsT ** outsF ** (condG, ctxsT, ctxsF)) <- ifology' lblIn ctx cond lblThen lblElse

    -- Compile the branches
    thenRes <- compileInstrDD outsT lblThen lblPost ctxsT instrThen
    elseRes <- compileInstrDD outsF lblElse lblPost ctxsF instrElse

    -- Construct the final graph by connecting the branches to the condition
    -- graph
    let branches = parallelCR thenRes elseRes
    let final    = seriesCR condG branches

    pure final

  -- A while loop
  compileInstrUD lblIn lblPost ctxIn instr@(While cond loop) = do

    -- Generate the input label
    lblNodeIn <- freshLabel

    -- A singleton graph with an undefined input, consisting of a single branch
    -- instruction
    let pre : ( CFG (CBlock $ GetLLType rt) (Undefined lblIn) (Defined [lblIn ~> lblNodeIn])
              , DList (:~: VarCTX) [lblIn ~> lblNodeIn]
              )
        pre = close lblNodeIn ctxIn emptyCFG

    (pre', ctxs) <- pure pre

    -- Compile via `compileInstrDD` and prepend the `pre'` block
    seriesCR pre' <$> compileInstrDD [lblIn] lblNodeIn lblPost ctxs instr

  --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  -- DD -----------------------------------------------------------------------
  --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  ||| Compile an instruction of any kind into a graph with defined inputs and
  ||| defined outputs. Do it via the `compileInstrUD` function, and define the
  ||| inputs of the graph it returns.
  ||| @ pre     labels of the predecessors of the input block of the graph
  |||         / sources of the input edges of the graph
  ||| @ lblIn   the input label of the graph
  ||| @ lblPost label of a block succeding the graph
  |||         / the destination of the output edges of the graph
  ||| @ ctxs    the contexts at the ends of the graphs predecessors
  ||| @ instr   the instruction to compile
  ||| @ rt      the return type of the function whose body the instruction is
  |||           part of
  ||| @ kind    the kind of the compiled instruction - "simple" or "returning"
  compileInstrDDViaUD
     : (pre            : List Label)
    -> (lblIn, lblPost : Label)
    -> (ctxs           : DList (:~: VarCTX) (pre ~~> lblIn))
    -> (instr          : Instr rt kind)
    -> CompM (CompileResult (GetLLType rt) (Defined $ pre ~~> lblIn) lblPost kind)

  compileInstrDDViaUD pre lblIn lblPost ctxs instr = do
    -- Merge the contexts coming from the different outputs of the graph
    SG ctx phis <- segregate ctxs

    -- Comstruct a prefix graph, with the phi instructions
    let preG = imap (phis |++:>) emptyCFG

    -- Compile the instruction, pass the merged context
    res <- compileInstrUD lblIn lblPost ctx instr

    -- Return the graph computing the expression with the phi assignments
    -- prepended to it
    pure $ connectCR preG res

  ||| A wrapper around `compileInstrDD` that converts the "compile result" into
  ||| a dependent pair of the graph, its output contexts, and its output labels,
  ||| thus dropping the information whether the graph is returning or not.
  ||| @ pre     labels of the predecessors of the input block of the graph
  |||         / sources of the input edges of the graph
  ||| @ lblIn   the input label of the graph
  ||| @ lblPost label of a block succeding the graph
  |||         / the destination of the output edges of the graph
  ||| @ ctxs    the contexts at the ends of the graphs predecessors
  ||| @ instr   the instruction to compile
  ||| @ rt      the return type of the function whose body the instruction is
  |||           part of
  ||| @ kind    the kind of the compiled instruction - "simple" or "returning"
  ||| @ lbls    the output labels of the graph
  export
  compileInstrDD'
     : (pre            : List Label)
    -> (lblIn, lblPost : Label)
    -> (ctxs           : DList (:~: VarCTX) (pre ~~> lblIn))
    -> (instr          : Instr rt kind)
    -> CompM ( lbls
            ** ( CFG (CBlock $ GetLLType rt) (Defined $ pre ~~> lblIn) (Defined $ lbls ~~> lblPost)
               , DList (:~: VarCTX) (lbls ~~> lblPost)
               )
             )
  compileInstrDD' pre lblIn lblPost ctxs instr = unwrapCR <$> compileInstrDD pre lblIn lblPost ctxs instr

  ||| Compile an instruction of any kind into a graph with defined inputs and
  ||| defined outputs.
  ||| Returns the graph as a "compile result"
  ||| @ pre     labels of the predecessors of the input block of the graph
  |||         / sources of the input edges of the graph
  ||| @ lblIn   the input label of the graph
  ||| @ lblPost label of a block succeding the graph
  |||         / the destination of the output edges of the graph
  ||| @ ctxs    the contexts at the ends of the graphs predecessors
  ||| @ instr   the instruction to compile
  ||| @ rt      the return type of the function whose body the instruction is
  |||           part of
  ||| @ kind    the kind of the compiled instruction - "simple" or "returning"
  export
  compileInstrDD
     : (pre            : List Label)
    -> (lblIn, lblPost : Label)
    -> (ctxs           : DList (:~: VarCTX) (pre ~~> lblIn))
    -> (instr          : Instr rt kind)
    -> CompM (CompileResult (GetLLType rt) (Defined $ pre ~~> lblIn) lblPost kind)

  -- Compile the following via `compileInstrUD` -------------------------------

  -- A block of instructions
  compileInstrDD pre lblIn lblPost ctxs instr@(Block instrs)
    = compileInstrDDViaUD pre lblIn lblPost ctxs instr

  -- An assignment
  compileInstrDD pre lblIn lblPost ctxs instr@(Assign var expr)
    = compileInstrDDViaUD pre lblIn lblPost ctxs instr

  -- An execution of an expression
  compileInstrDD pre lblIn lblPost ctxs instr@(Exec expr)
    = compileInstrDDViaUD pre lblIn lblPost ctxs instr

  -- An if-then statement
  compileInstrDD pre lblIn lblPost ctxs instr@(If cond instrThen)
    = compileInstrDDViaUD pre lblIn lblPost ctxs instr

  -- An if-then-else statement
  compileInstrDD pre lblIn lblPost ctxs instr@(IfElse cond instrThen instrElse)
    = compileInstrDDViaUD pre lblIn lblPost ctxs instr

  -- A return statement
  compileInstrDD pre lblIn lblPost ctxs instr@(Return expr)
    = compileInstrDDViaUD pre lblIn lblPost ctxs instr

  -- A void return statement
  compileInstrDD pre lblIn lblPost ctxs instr@RetVoid
    = compileInstrDDViaUD pre lblIn lblPost ctxs instr

  -----------------------------------------------------------------------------

  -- A while loop
  compileInstrDD pre lblNodeIn lblPost ctxsIn instr@(While cond loop) = do

    -- TODO: get rid of unnecessary assignments
    -- Assign a new refister for every variable in the incoming contexts.
    ctxNode' <-newRegForAll ctxsIn
    let ctxNode = map toValues ctxNode'

    -- Generate the input label of the loop-body graph.
    lblLoop <- freshLabel

    -- Compile the condition through jump statements.
    (outsT ** outsF ** (nodeG, ctxsLoop, ctxsPost)) <- ifology' lblNodeIn ctxNode cond lblLoop lblPost

    -- Compile the loop body.
    (loopOuts ** (loop, ctxsLoopOut)) <- compileInstrDD' outsT lblLoop lblNodeIn ctxsLoop loop

    -- Concatenate them with the contexts coming in from outside the loop
    -- - together, they constitute all contexts coming into the condition graph
    let ctxs  : DList (:~: VarCTX) ((pre ++ loopOuts) ~~> lblNodeIn)
        ctxs  = rewrite collect_concat lblNodeIn pre loopOuts
                in ctxsIn ++ ctxsLoopOut

    -- Compute the phi statements needed to produce the new-register context
    -- (`ctxNode`) given the incoming contexts (`ctxs`).
    phis <- mkPhis ctxNode' ctxs

    -- Define the inputs of the condition graph by prepending to it the phi
    -- assignemtns.
    let node' : CFG (CBlock $ GetLLType rt)
                    (Defined $ pre ~~> lblNodeIn ++ loopOuts ~~> lblNodeIn)
                    (Defined $ (outsT ~~> lblLoop) ++ (outsF ~~> lblPost))
        node' = rewrite revEq $ collect_concat lblNodeIn pre loopOuts
                in imap (phis |++:>) nodeG

    -- Construct the final graph by connecting the condition graph with the
    -- loop-body graph.
    let final = Cycle node' loop

    pure $ CRS (outsF ** (final, ctxsPost))

    where

      ||| Make a phi expresion from a dependent list of values attached to the
      ||| edges they come from.
      ||| @ t    the type of the expression
      ||| @ lbls the input labels of the expression
      ||| @ vals the values attached to edges
      phiFromDList
         : The t
        -> (lbls : List Label)
        -> (vals : DList (:~: (LLValue t)) (lbls ~~> lbl))
        -> PhiExpr lbls t
      phiFromDList (MkThe t) Nil Nil = Phi t Nil
      phiFromDList theT (lbl :: lbls) (val :: vals)
        = addInput lbl (detach val) (phiFromDList theT lbls vals)

      ||| Get a value of a variable from a variable context
      ||| If the variable is not in the context, throws an "impossible" error.
      ||| @ var the variable
      ||| @ ctx the context
      getVal
         : (var : Variable t)
        -> (ctx : VarCTX)
        -> CompM $ LLValue (GetLLType t)
      getVal var ctx = do
        let Just val = lookup var ctx
                     | Nothing => throwError $ Impossible "variable non existent in loop body or node context"
        pure val

      ||| Given a desired context, make a list of phi expressions from a
      ||| dependent list of variable contexts attached to the edges they come
      ||| from.
      ||| Execution of the phi expressions will produce the desired context.
      |||
      ||| Returns the phi assignment with a comment marking what assignemnt
      ||| took place.
      |||
      ||| @ ctx  the desired context
      ||| @ lbls the sources of the input edges
      ||| @ ctxs the list of contecxts attached to edges
      mkPhis
         : (ctx : lbl :~: VarCTX')
        -> {lbls : List Label}
        -> (ctxs : DList (:~: VarCTX) (lbls ~~> lbl))
        -> CompM $ List (PhiInstr lbls, Maybe String)

      mkPhis ctx {lbls} ctxs = traverse mkPhi' (toList $ detach ctx) where

        ||| Given a variable and its desired value, make a phi expression that
        ||| assigns the value to the variable
        ||| @ dsum the desired variable-value pair
        mkPhi'
           : (dsum : DSum Variable (Reg . GetLLType))
          -> CompM (PhiInstr lbls, Maybe String)
        mkPhi' (var :=> reg) = do

          -- For every context in the list, get the value of the variable in
          -- question (`var`)
          vals <- dtraverse (traverse (getVal var)) ctxs

          -- Convert the list to a phi expression
          let vals' = phiFromDList (map GetLLType $ typeOf var) lbls vals

          -- Construct the phi assignment and the comment
          pure $ (AssignPhi reg vals', Just $ prt var)
