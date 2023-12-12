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
record DataUU (rt : LLType) (lblIn : Label) where
  constructor MkDataUU
  lblOut : Label
  cfg : CFG (CBlock rt) (Undefined lblIn) (Undefined lblOut)
  ctx : lblOut :~: VarCTX

public export
record DataXD (rt : LLType) (ins : Edges Label) (dest : Label) where
  constructor MkDataXD
  outs : List Label
  cfg : CFG (CBlock rt) ins (Defined $ outs ~~> dest)
  ctxs : DList (:~: VarCTX) (outs ~~> dest)

public export
record DataXD2 (rt : LLType) (ins : Edges Label) (lblT, lblF : Label) where
  constructor MkDataXD2
  outsT : List Label
  outsF : List Label
  
  cfg : CFG (CBlock rt) ins (Defined $ (outsT ~~> lblT) ++ (outsF ~~> lblF))
  
  ctxsT : DList (:~: VarCTX) (outsT ~~> lblT)
  ctxsF : DList (:~: VarCTX) (outsF ~~> lblF)

public export
data CompileResult : LLType -> Edges Label -> Label -> InstrKind -> Type where
  CRR : CFG (CBlock rt) ins Closed
     -> CompileResult rt ins lbl Returning
  CRS : DataXD rt ins lbl
     -> CompileResult rt ins lbl Simple


export
unwrapCR : CompileResult rt ins lbl kind
        -> DataXD rt ins lbl
unwrapCR (CRR cfg) = MkDataXD { outs = [], cfg, ctxs = [] }
unwrapCR (CRS dat) = dat

export
emptyCR : (lbl, lbl' : Label) -> lbl :~: VarCTX -> CompileResult rt (Undefined lbl) lbl' Simple
emptyCR lbl lbl' ctx = let
  (cfg, ctxs) = (close lbl' ctx (emptyCFG {lbl}))
  in CRS (MkDataXD { outs = [lbl], cfg, ctxs })



export
connectCR : CFG (CBlock rt) ins (Undefined lbl)
         -> CompileResult rt (Undefined lbl) lbl' k
         -> CompileResult rt ins lbl' k
connectCR g (CRR g') = CRR (g *~> g')
connectCR g (CRS dat) = CRS $ { cfg $= (g *~>) } dat

infixr 5 *~~>
export
(*~~>) : CFG (CBlock rt) ins (Undefined lbl)
      -> CompileResult rt (Undefined lbl) lbl' k
      -> CompileResult rt ins lbl' k
(*~~>) = connectCR

export
seriesCR : CFG (CBlock rt) ins (Defined outs)
        -> CompileResult rt (Defined outs) lbl' k
        -> CompileResult rt ins lbl' k
seriesCR g (CRR g') = CRR (g *-> g')
seriesCR g (CRS dat) = CRS $ { cfg $= (g *->) } dat

infixr 5 *-->
export
(*-->) : CFG (CBlock rt) ins (Defined outs)
      -> CompileResult rt (Defined outs) lbl' k
      -> CompileResult rt ins lbl' k
(*-->) = seriesCR

export
parallelCR : {0 lbl : Label}
          -> (lres : CompileResult rt (Defined ledges) lbl lk)
          -> (rres : CompileResult rt (Defined redges) lbl rk)
          
          -> CompileResult rt (Defined $ ledges ++ redges) lbl (BrKind lk rk)

parallelCR {lbl} (CRR lg) (CRR rg) = CRR (lg |-| rg)

parallelCR {lbl} (CRR lg) (CRS rdat) = CRS $ { cfg $= (lg |-|) } rdat

-- TODO try without pattern matching on DataXD
parallelCR {lbl} (CRS (MkDataXD { outs, cfg = lg, ctxs })) (CRR rg)
  = let

    g = rewrite revEq $ concat_nil (outs ~~> lbl)
        in lg |-| rg

    in CRS $ MkDataXD { outs, cfg = g, ctxs }

-- TODO try without pattern matching on DataXD
parallelCR {lbl} (CRS (MkDataXD { outs = louts, cfg = lg, ctxs = lctxs }))
                 (CRS (MkDataXD { outs = routs, cfg = rg, ctxs = rctxs }))
  = let

    cfg = rewrite collect_concat lbl louts routs
          in lg |-| rg
    
    ctxs = rewrite collect_concat lbl louts routs
           in lctxs ++ rctxs

    in CRS $ MkDataXD { outs = louts ++ routs, cfg, ctxs }

infixr 4 |--|
export
(|--|) : {0 lbl : Label}
      -> (lres : CompileResult rt (Defined ledges) lbl lk)
      -> (rres : CompileResult rt (Defined redges) lbl rk)
      
      -> CompileResult rt (Defined $ ledges ++ redges) lbl (BrKind lk rk)
(|--|) = parallelCR



