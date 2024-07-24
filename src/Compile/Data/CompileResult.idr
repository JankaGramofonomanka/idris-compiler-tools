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
  ||| Contains a graph with defined outputs and the list of the sources of its
  ||| output edges.
  CRS : (lbls ** CFG (CBlock rt) ins (Defined $ lbls ~~> lbl))
     -> CompileResult rt ins lbl Simple

||| Extract the graph from the "compile result", thus dropping the information
||| whether it is returning or not.
export
unwrapCR : CompileResult rt ins lbl kind
          -> (outs ** CFG (CBlock rt) ins (Defined $ outs ~~> lbl))
unwrapCR (CRR g) = ([] ** g)
unwrapCR (CRS (outs ** g)) = (outs ** g)

||| Create an ampty "compile result".
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
emptyCR lbl lbl' ctx = CRS ([lbl] ** omap (<+| Branch lbl') (emptyCFG ctx))


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
connectCR g (CRS (lbls ** g')) = CRS $ (lbls ** connect g g')

||| Prepend a graph with defined outputs to a "compile reslult" that wrapps a
||| graph with an defined inputs
||| @ pre  the graph            (the prefix)
||| @ post the "compile result" (the postfix)
export
seriesCR
   : (pre  : CFG (CBlock rt) ins (Defined outs))
  -> (post : CompileResult rt (Defined outs) lbl' k)
  ->         CompileResult rt ins lbl' k
seriesCR g (CRR g') = CRR $ Series g g'
seriesCR g (CRS (lbls ** g')) = CRS $ (lbls ** Series g g')

||| Connect two "compile results" in parallel\
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
--parallelCR {lbl} (CRR lg) (CRS (routs ** rg)) = CRS (routs ** Parallel lg rg)
parallelCR {lbl} (CRR lg) (CRS dp) = case dp of
  (routs ** rg) => CRS (routs ** Parallel lg rg)

parallelCR {lbl} (CRS (louts ** lg)) (CRR rg) = let

  g = rewrite revEq $ concat_nil (louts ~~> lbl)
      in Parallel lg rg

  in CRS (louts ** g)

parallelCR {lbl} (CRS (louts ** lg)) (CRS (routs ** rg)) = let

  g = rewrite collect_concat lbl louts routs
      in Parallel lg rg

  in CRS (louts ++ routs ** g)



