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

-- TODO Add documentation
public export
record DataUU (rt : LLType) (lblIn : Label) where
  constructor MkDataUU
  lblOut : Label
  cfg : CFG (CBlock rt) (Undefined lblIn) (Undefined lblOut)
  ctx : lblOut :~: VarCTX

-- TODO Add documentation
public export
record DataXD (rt : LLType) (ins : Edges Label) (dest : Label) where
  constructor MkDataXD
  outs : List Label
  cfg : CFG (CBlock rt) ins (Defined $ outs ~~> dest)
  ctxs : DList (:~: VarCTX) (outs ~~> dest)

-- TODO Add documentation
public export
record DataXD2 (rt : LLType) (ins : Edges Label) (lblT, lblF : Label) where
  constructor MkDataXD2
  outsT : List Label
  outsF : List Label

  cfg : CFG (CBlock rt) ins (Defined $ (outsT ~~> lblT) ++ (outsF ~~> lblF))

  ctxsT : DList (:~: VarCTX) (outsT ~~> lblT)
  ctxsF : DList (:~: VarCTX) (outsF ~~> lblF)

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

  -- TODO shorten the documentation to sth like "A "sinmle" result. Contains DataXD"
  ||| A "simple" (non-returning) result.
  ||| Contains a graph with defined outputs, the list of the sources of its
  ||| output edges and the list of its output contexts (contexts at the end
  ||| of its outputs).
  CRS : DataXD rt ins lbl
     -> CompileResult rt ins lbl Simple

||| Extract the graph from the "compile result", thus dropping the information
||| whether it is returning or not.
export
unwrapCR : CompileResult rt ins lbl kind
        -> DataXD rt ins lbl
unwrapCR (CRR cfg) = MkDataXD { outs = [], cfg, ctxs = [] }
unwrapCR (CRS dat) = dat

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
emptyCR lbl lbl' ctx = let
  (cfg, ctxs) = (close lbl' ctx (emptyCFG {lbl}))
  in CRS (MkDataXD { outs = [lbl], cfg, ctxs })


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
connectCR g (CRS dat) = CRS $ { cfg $= connect g } dat

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
seriesCR g (CRS dat) = CRS $ { cfg $= Series g } dat

||| Connect two "compile results" in parallel
||| @ lbl  the label of the successor of the parallel graphs
||| @ lres the left  "compile result"
||| @ rres the right "compile result"
export
parallelCR
   : {0 lbl : Label}
  -> (lres : CompileResult rt (Defined ledges) lbl lk)
  -> (rres : CompileResult rt (Defined redges) lbl rk)
  ->         CompileResult rt (Defined $ ledges ++ redges) lbl (BrKind lk rk)

parallelCR {lbl} (CRR lg) (CRR rg) = CRR $ Parallel lg rg

parallelCR {lbl} (CRR lg) (CRS rdat) = CRS $ { cfg $= Parallel lg } rdat

-- TODO try without pattern matching on DataXD
parallelCR {lbl} (CRS (MkDataXD { outs, cfg = lg, ctxs })) (CRR rg)
  = let

    g = rewrite revEq $ concat_nil (outs ~~> lbl)
        in Parallel lg rg

    in CRS $ MkDataXD { outs, cfg = g, ctxs }

-- TODO try without pattern matching on DataXD
parallelCR {lbl} (CRS (MkDataXD { outs = louts, cfg = lg, ctxs = lctxs }))
                 (CRS (MkDataXD { outs = routs, cfg = rg, ctxs = rctxs }))
  = let

    cfg = rewrite collect_concat lbl louts routs
          in Parallel lg rg

    ctxs = rewrite collect_concat lbl louts routs
           in lctxs ++ rctxs

    in CRS $ MkDataXD { outs = louts ++ routs, cfg, ctxs }



