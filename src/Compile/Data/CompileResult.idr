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
data CRType = Open | Closed

public export
CRParallel : CRType -> Lazy CRType -> CRType
CRParallel Open rt = Open
CRParallel Closed rt = rt


public export
CRSeries : CRType -> Lazy CRType -> CRType
CRSeries Closed rt = Closed
CRSeries Open rt = rt

total
export
cr_series_commut : (x, y : CRType) -> CRSeries x y = CRSeries y x
cr_series_commut Closed Closed = Refl
cr_series_commut Closed Open = Refl
cr_series_commut Open Closed = Refl
cr_series_commut Open Open = Refl

total
export
cr_parallel_commut : (x, y : CRType) -> CRParallel x y = CRParallel y x
cr_parallel_commut Closed Closed = Refl
cr_parallel_commut Closed Open = Refl
cr_parallel_commut Open Closed = Refl
cr_parallel_commut Open Open = Refl

public export
toCRType : Maybe BlockLabel -> CRType
toCRType Nothing = Closed
toCRType (Just _) = Open


public export
data CompileResult : LLType -> Edges BlockLabel -> BlockLabel -> CRType -> Type where
  CRC : CFG (CBlock rt) ins Closed -> CompileResult rt ins lbl Closed
  CRO : (lbls ** CFG (CBlock rt) ins (Defined $ lbls ~~> lbl))
     -> CompileResult rt ins lbl Open


export
unwrapCR : CompileResult rt ins lbl crt
          -> (outs ** CFG (CBlock rt) ins (Defined $ outs ~~> lbl))
unwrapCR (CRC g) = ([] ** g)
unwrapCR (CRO (outs ** g)) = (outs ** g)

export
emptyCR : (lbl, lbl' : BlockLabel) -> lbl :~: VarCTX -> CompileResult rt (Undefined lbl) lbl' Open
emptyCR lbl lbl' ctx = CRO ([lbl] ** omap {outs = Just [lbl']} (<+| Branch lbl') (emptyCFG ctx))



export
connectCR : CFG (CBlock rt) ins (Undefined lbl)
         -> CompileResult rt (Undefined lbl) lbl' crt
         -> CompileResult rt ins lbl' crt
connectCR g (CRC g') = CRC $ connect g g'
connectCR g (CRO (lbls ** g')) = CRO $ (lbls ** connect g g')

export
seriesCR : CFG (CBlock rt) ins (Defined outs)
        -> CompileResult rt (Defined outs) lbl' crt
        -> CompileResult rt ins lbl' crt
seriesCR g (CRC g') = CRC $ Series g g'
seriesCR g (CRO (lbls ** g')) = CRO $ (lbls ** Series g g')


export
parallelCR : {lbl : BlockLabel}
          -> (lres : CompileResult rt (Defined ledges) lbl lcrt)
          -> (rres : CompileResult rt (Defined redges) lbl rcrt)
          
          -> CompileResult rt (Defined $ ledges ++ redges) lbl (CRParallel lcrt rcrt)

parallelCR {lbl} (CRC lg) (CRC rg) = CRC $ Parallel lg rg

-- Without the "case of" pattern match idris thinks the function is not covering
--parallelCR {lbl} (CRC lg) (CRO (routs ** rg)) = CRO (routs ** Parallel lg rg)
parallelCR {lbl} (CRC lg) (CRO dp) = case dp of
  (routs ** rg) => CRO (routs ** Parallel lg rg)

parallelCR {lbl} (CRO (louts ** lg)) (CRC rg) = let

  g = rewrite revEq $ concat_nil (louts ~~> lbl)
      in Parallel lg rg

  in CRO (louts ** g)

parallelCR {lbl} (CRO (louts ** lg)) (CRO (routs ** rg)) = let

  g = rewrite collect_concat lbl louts routs
      in Parallel lg rg

  in CRO (louts ++ routs ** g)



