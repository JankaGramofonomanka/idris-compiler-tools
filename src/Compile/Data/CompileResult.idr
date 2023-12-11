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

export
close : (dest : Label)
     -> lbl :~: VarCTX
     -> CFG (CBlock rt) ins (Undefined lbl)
     -> ( CFG (CBlock rt) ins (Defined [lbl ~> dest])
        , DList (:~: VarCTX) [lbl ~> dest]
        )
close {lbl} dest ctx cfg = (omap (<+| Branch dest) cfg, [attach (lbl ~> dest) (detach ctx)])

public export
data CompileResult : LLType -> Edges Label -> Label -> InstrKind -> Type where
  CRR : CFG (CBlock rt) ins Closed
     -> CompileResult rt ins lbl Returning
  CRS : ( lbls
       ** ( CFG (CBlock rt) ins (Defined $ lbls ~~> lbl)
          , DList (:~: VarCTX) (lbls ~~> lbl)
          )
        )
     -> CompileResult rt ins lbl Simple


export
unwrapCR : CompileResult rt ins lbl kind
          -> ( outs
            ** ( CFG (CBlock rt) ins (Defined $ outs ~~> lbl)
               , DList (:~: VarCTX) (outs ~~> lbl)
               )
             )
unwrapCR (CRR g) = ([] ** (g, []))
unwrapCR (CRS (outs ** stuff)) = (outs ** stuff)

export
emptyCR : (lbl, lbl' : Label) -> lbl :~: VarCTX -> CompileResult rt (Undefined lbl) lbl' Simple
emptyCR lbl lbl' ctx = CRS ([lbl] ** (close lbl' ctx (emptyCFG {lbl})))



export
connectCR : CFG (CBlock rt) ins (Undefined lbl)
         -> CompileResult rt (Undefined lbl) lbl' k
         -> CompileResult rt ins lbl' k
connectCR g (CRR g') = CRR $ connect g g'
connectCR g (CRS (lbls ** (g', ctxs))) = CRS $ (lbls ** (connect g g', ctxs))

export
seriesCR : CFG (CBlock rt) ins (Defined outs)
        -> CompileResult rt (Defined outs) lbl' k
        -> CompileResult rt ins lbl' k
seriesCR g (CRR g') = CRR $ Series g g'
seriesCR g (CRS (lbls ** (g', ctxs))) = CRS $ (lbls ** (Series g g', ctxs))


export
parallelCR : {lbl : Label}
          -> (lres : CompileResult rt (Defined ledges) lbl lk)
          -> (rres : CompileResult rt (Defined redges) lbl rk)
          
          -> CompileResult rt (Defined $ ledges ++ redges) lbl (BrKind lk rk)

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



