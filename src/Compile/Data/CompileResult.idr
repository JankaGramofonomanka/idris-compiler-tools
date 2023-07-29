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
emptyCFG : {lbl : BlockLabel} -> lbl :~: VarCTX -> CFG (CBlock rt) (Undefined lbl) (Undefined lbl)
emptyCFG = initGraph . emptyCBlock





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
data CompileResultUD : LLType -> BlockLabel -> BlockLabel -> CRType -> Type where
  CRUDC : CFG (CBlock rt) (Undefined lbl) Closed -> CompileResultUD rt lbl lbl' Closed
  CRUDO : (lbls ** CFG (CBlock rt) (Undefined lbl) (Defined $ lbls ~~> lbl'))
       -> CompileResultUD rt lbl lbl' Open



public export
data CompileResultDD : LLType -> List (Edge BlockLabel) -> BlockLabel -> CRType -> Type where
  CRDDC : CFG (CBlock rt) (Defined edges) Closed -> CompileResultDD rt edges lbl Closed
  CRDDO : (lbls ** CFG (CBlock rt) (Defined edges) (Defined $ lbls ~~> lbl))
       -> CompileResultDD rt edges lbl Open




export
unwrapCRUD : CompileResultUD rt lbl lbl' crt
          -> (outs ** CFG (CBlock rt) (Undefined lbl) (Defined $ outs ~~> lbl'))
unwrapCRUD (CRUDC g) = ([] ** g)
unwrapCRUD (CRUDO (outs ** g)) = (outs ** g)

export
unwrapCRDD : CompileResultDD rt edges lbl crt
          -> (outs ** CFG (CBlock rt) (Defined edges) (Defined $ outs ~~> lbl))
unwrapCRDD (CRDDC g) = ([] ** (g))
unwrapCRDD (CRDDO (outs ** g)) = (outs ** g)






export
emptyCRUD : (lbl, lbl' : BlockLabel) -> lbl :~: VarCTX -> CompileResultUD rt lbl lbl' Open
emptyCRUD lbl lbl' ctx = CRUDO ([lbl] ** omap {outs = Just [lbl']} (<+| Branch lbl') (emptyCFG ctx))








export
connectCRUD : CFG (CBlock rt) (Undefined lbl) (Undefined lbl')
           -> CompileResultUD rt lbl' lbl'' os
           -> CompileResultUD rt lbl lbl'' os
connectCRUD g (CRUDC g') = CRUDC $ connect g g'
connectCRUD g (CRUDO (lbls ** g')) = CRUDO $ (lbls ** connect g g')


export
connectCRDDCRUD : CFG (CBlock rt) (Undefined lbl) (Defined edges)
               -> CompileResultDD rt edges lbl' crt
               -> CompileResultUD rt lbl lbl' crt

connectCRDDCRUD pre (CRDDC g) = CRUDC (Series pre g)
connectCRDDCRUD pre (CRDDO (lbls ** g)) = let g' = Series pre g in CRUDO (lbls ** g')

export
connectCRUDCRDD : CFG (CBlock rt) (Defined edges) (Undefined lbl)
               -> CompileResultUD rt lbl lbl' crt
               -> CompileResultDD rt edges lbl' crt
connectCRUDCRDD pre (CRUDC g) = CRDDC (connect pre g)
connectCRUDCRDD pre (CRUDO (lbls ** g)) = let g' = connect pre g in CRDDO (lbls ** g')




export
parallelCR : {lbl : BlockLabel}
          -> (lres : CompileResultDD rt ledges lbl lcrt)
          -> (rres : CompileResultDD rt redges lbl rcrt)
          
          -> CompileResultDD rt (ledges ++ redges) lbl (CRParallel lcrt rcrt)

parallelCR {lbl} (CRDDC lg) (CRDDC rg) = CRDDC $ Parallel lg rg

parallelCR {lbl} (CRDDC lg) (CRDDO (routs ** rg)) = CRDDO (routs ** Parallel lg rg)

parallelCR {lbl} (CRDDO (louts ** lg)) (CRDDC rg) = let

  g = rewrite revEq $ concat_nil (louts ~~> lbl)
      in Parallel lg rg

  in CRDDO (louts ** g)

parallelCR {lbl} (CRDDO (louts ** lg)) (CRDDO (routs ** rg)) = let

  g = rewrite collect_concat lbl louts routs
      in Parallel lg rg

  in CRDDO (louts ++ routs ** g)







