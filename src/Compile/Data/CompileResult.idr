module Compile.Data.CompileResult

import Data.List

import Control.Monad.State

import Data.DMap
import Data.DList
import Data.Attached

import LLVM
import LNG.TypeChecked

import Compile.Data.CBlock
import Compile.Data.CompM
import Compile.Data.Context
import Compile.Data.Context.Utils
import Compile.Data.Error
import Compile.Utils
import CFG

import Theory

-- TODO Add documentation
export
close : (dest : Label)
     -> lbl :~: VarCTX
     -> CFG (CBlock rt) ins (Undefined lbl)
     -> ( CFG (CBlock rt) ins (Defined [lbl ~> dest])
        , DList (:~: VarCTX) [lbl ~> dest]
        )
close {lbl} dest ctx cfg = (omap (<+| Branch dest) cfg, [attach (lbl ~> dest) (detach ctx)])

||| The result of a compilation of a piece of code.
||| A `CFG` wrapped in additional constructors for easier differentiating
||| between the results of "returning" and "non-returning" instructions.
|||
||| @ rt     the return type of the function, whose body the wrapped graph is
|||          part of, used to enforce the correct types of returned values.
||| @ ins    the input edges of the wrapped graph.
||| @ outLbl the label of the block that is a successor of the wrapped graph.
||| @ kind   the kind of the instruction whose compilation results in the graph
|||          that is beeing wrapped.
public export
data CompileResult
   : (rt     : LLType)
  -> (ins    : Edges Label)
  -> (outLbl : Label)
  -> (kind   : InstrKind)
  -> Type
  where
  ||| A "returning" result. Contains a graph with no outputs.
  ||| @ cfg the wrapped graph.
  CRR : (cfg : CFG (CBlock rt) ins Closed)
     -> CompileResult rt ins lbl Returning

  ||| A "simple" (non-returning) result.
  ||| Contains a graph with defined outputs, the list of the sources of its
  ||| output edges and the list of its output contexts (contexts at the end
  ||| of its outputs).
  CRS : ( lbls
       ** ( CFG (CBlock rt) ins (Defined $ lbls ~~> lbl)
          , DList (:~: VarCTX) (lbls ~~> lbl)
          )
        )
     -> CompileResult rt ins lbl Simple

||| Extract the graph from the "compile result", thus dropping the information
||| whether it is returning or not.
export
unwrapCR : CompileResult rt ins lbl kind
          -> ( outs
            ** ( CFG (CBlock rt) ins (Defined $ outs ~~> lbl)
               , DList (:~: VarCTX) (outs ~~> lbl)
               )
             )
unwrapCR (CRR g) = ([] ** (g, []))
unwrapCR (CRS (outs ** stuff)) = (outs ** stuff)

||| Create an empty "compile result".
||| The empty result will consist of singleton graph, whose only vertex's only
||| instruction is the terminating instruction
||| @ lbl the label of the only block in the graph
||| @ lbl' the label of the block to which the terminator jumps to
||| @ ctx the context as it is before the block
export
emptyCR
   : (lbl, lbl' : Label)
  -> (ctx       : lbl :~: VarCTX)
  -> CompileResult rt (Undefined lbl) lbl' Simple
emptyCR lbl lbl' ctx = CRS ([lbl] ** (close lbl' ctx (emptyCFG {lbl})))


||| Prepend a graph with undefined output to a "compile reslult" that wrapps a
||| graph with an undefined input
||| @ pre  the graph            (the prefix)
||| @ post the "compile result" (the postfix)
export
connectCR
   : (pre  : CFG (CBlock   rt) ins (Undefined lbl))
  -> (post : CompileResult rt (Undefined lbl) lbl' k)
  ->         CompileResult rt  ins            lbl' k
connectCR g (CRR g') = CRR $ connect g g'
connectCR g (CRS (lbls ** (g', ctxs))) = CRS $ (lbls ** (connect g g', ctxs))

||| Prepend a graph with defined outputs to a "compile reslult" that wrapps a
||| graph with defined inputs
||| @ pre  the graph            (the prefix)
||| @ post the "compile result" (the postfix)
export
seriesCR
   : (pre  : CFG (CBlock rt) ins (Defined outs))
  -> (post : CompileResult rt (Defined outs) lbl' k)
  ->         CompileResult rt ins lbl' k
seriesCR g (CRR g') = CRR $ Series g g'
seriesCR g (CRS (lbls ** (g', ctxs))) = CRS $ (lbls ** (Series g g', ctxs))

||| Connect two "compile results" in parallel
||| @ lbl  the label of the successor of the parallel graphs
||| @ lres the left  "compile result"
||| @ rres the right "compile result"
export
parallelCR
   : {lbl : Label}
  -> (lres : CompileResult rt (Defined ledges) lbl lk)
  -> (rres : CompileResult rt (Defined redges) lbl rk)
  ->         CompileResult rt (Defined $ ledges ++ redges) lbl (BrKind lk rk)

parallelCR {lbl} (CRR lg) (CRR rg) = CRR $ Parallel lg rg

-- Without the "case of" pattern match idris thinks the function is not covering
--parallelCR {lbl} (CRR lg) (CRS (routs ** (rg, rctxs))) = CRS (routs ** (Parallel lg rg, rctxs))
parallelCR {lbl} (CRR lg) (CRS dp) = case dp of
  (routs ** (rg, rctxs)) => CRS (routs ** (Parallel lg rg, rctxs))

parallelCR {lbl} (CRS (louts ** (lg, lctxs))) (CRR rg) = let

  g = rewrite revEq $ concat_nil (louts ~~> lbl)
      in Parallel lg rg

  in CRS (louts ** (g, lctxs))

parallelCR {lbl} (CRS (louts ** (lg, lctxs))) (CRS (routs ** (rg, rctxs))) = let

  g = rewrite collect_concat lbl louts routs
      in Parallel lg rg

  ctxs = rewrite collect_concat lbl louts routs
         in lctxs ++ rctxs

  in CRS (louts ++ routs ** (g, ctxs))



