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

public export
data CompileResult : LLType -> Edges Label -> Label -> InstrKind -> Type where
  CRR : CFG (CBlock rt) ins Closed -> CompileResult rt ins lbl Returning
  CRS : (lbls ** CFG (CBlock rt) ins (Defined $ lbls ~~> lbl))
     -> CompileResult rt ins lbl Simple


export
unwrapCR : CompileResult rt ins lbl kind
          -> (outs ** CFG (CBlock rt) ins (Defined $ outs ~~> lbl))
unwrapCR (CRR g) = ([] ** g)
unwrapCR (CRS (outs ** g)) = (outs ** g)

export
emptyCR : (lbl, lbl' : Label) -> CompileResult rt (Undefined lbl) lbl' Simple
emptyCR lbl lbl' = CRS ([lbl] ** omap (<+| Branch lbl') emptyCFG)



export
connectCR : CFG (CBlock rt) ins (Undefined lbl)
         -> CompileResult rt (Undefined lbl) lbl' k
         -> CompileResult rt ins lbl' k
connectCR g (CRR g') = CRR $ connect g g'
connectCR g (CRS (lbls ** g')) = CRS $ (lbls ** connect g g')

export
seriesCR : CFG (CBlock rt) ins (Defined outs)
        -> CompileResult rt (Defined outs) lbl' k
        -> CompileResult rt ins lbl' k
seriesCR g (CRR g') = CRR $ Series g g'
seriesCR g (CRS (lbls ** g')) = CRS $ (lbls ** Series g g')


export
parallelCR : {lbl : Label}
          -> (lres : CompileResult rt (Defined ledges) lbl lk)
          -> (rres : CompileResult rt (Defined redges) lbl rk)

          -> CompileResult rt (Defined $ ledges ++ redges) lbl (BrKind lk rk)

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



