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
initCFG : {lbl : BlockLabel} -> CFG CBlock (Undefined lbl) (Undefined lbl)
initCFG = initGraph initCBlock





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
data CompileResultUU : BlockLabel -> CRType -> Type where
  CRUUC : CFG CBlock (Undefined lbl) Closed -> CompileResultUU lbl Closed
  CRUUO : (lbl' **  CFG CBlock (Undefined lbl) (Undefined lbl'))
       -> CompileResultUU lbl Open



public export
data CompileResultUD : BlockLabel -> BlockLabel -> CRType -> Type where
  CRUDC : CFG CBlock (Undefined lbl) Closed -> CompileResultUD lbl lbl' Closed
  CRUDO : (lbls ** (CFG CBlock (Undefined lbl) (Defined $ lbls ~~> lbl'), NonEmpty lbls))
       -> CompileResultUD lbl lbl' Open



public export
data CompileResultDD : List (Edge BlockLabel) -> BlockLabel -> CRType -> Type where
  CRDDC : CFG CBlock (Defined edges) Closed -> CompileResultDD edges lbl Closed
  CRDDO : (lbls ** (CFG CBlock (Defined edges) (Defined $ lbls ~~> lbl), NonEmpty lbls))
       -> CompileResultDD edges lbl Open




export
unwrapCRUD : CompileResultUD lbl lbl' crt
          -> (outs ** CFG CBlock (Undefined lbl) (Defined $ outs ~~> lbl'))
unwrapCRUD (CRUDC g) = ([] ** g)
unwrapCRUD (CRUDO (outs ** (g, prf))) = (outs ** g)

export
unwrapCRDD : CompileResultDD edges lbl crt
          -> (outs ** CFG CBlock (Defined edges) (Defined $ outs ~~> lbl))
unwrapCRDD (CRDDC g) = ([] ** (g))
unwrapCRDD (CRDDO (outs ** (g, prf))) = (outs ** g)






export
emptyCRUU : (lbl : BlockLabel) -> CompileResultUU lbl Open
emptyCRUU lbl = CRUUO (lbl ** initCFG)

export
emptyCRUD : (lbl, lbl' : BlockLabel) -> CompileResultUD lbl lbl' Open
emptyCRUD lbl lbl' = CRUDO ([lbl] ** (omap {outs = Just [lbl']} (<+| Branch lbl') initCFG, IsNonEmpty))








export
connectCRUU : CFG CBlock (Undefined lbl) (Undefined lbl') -> CompileResultUU lbl' os -> CompileResultUU lbl os
connectCRUU g (CRUUC g') = CRUUC $ connect g g'
connectCRUU g (CRUUO (lbl'' ** g')) = CRUUO $ (lbl'' ** connect g g')


export
connectCRUD : CFG CBlock (Undefined lbl) (Undefined lbl')
           -> CompileResultUD lbl' lbl'' os
           -> CompileResultUD lbl lbl'' os
connectCRUD g (CRUDC g') = CRUDC $ connect g g'
connectCRUD g (CRUDO (lbls ** (g', prf))) = CRUDO $ (lbls ** (connect g g', prf))


export
connectCRDDCRUD : {auto 0 prf : NonEmpty edges}
               -> CFG CBlock (Undefined lbl) (Defined edges)
               -> CompileResultDD edges lbl' crt
               -> CompileResultUD lbl lbl' crt

connectCRDDCRUD pre (CRDDC g) = CRUDC (Series pre g)
connectCRDDCRUD pre (CRDDO (lbls ** (g, prf))) = let g' = Series pre g in CRUDO (lbls ** (g', prf))

export
connectCRUDCRDD : CFG CBlock (Defined edges) (Undefined lbl)
               -> CompileResultUD lbl lbl' crt
               -> CompileResultDD edges lbl' crt
connectCRUDCRDD pre (CRUDC g) = CRDDC (connect pre g)
connectCRUDCRDD pre (CRUDO (lbls ** (g, prf))) = let g' = connect pre g in CRDDO (lbls ** (g', prf))




export
parallelCR : {lbl : BlockLabel}
          -> (lres : CompileResultDD ledges lbl lcrt)
          -> (rres : CompileResultDD redges lbl rcrt)
          
          -> CompileResultDD (ledges ++ redges) lbl (CRParallel lcrt rcrt)

parallelCR {lbl} (CRDDC lg) (CRDDC rg) = CRDDC $ Parallel lg rg

parallelCR {lbl} (CRDDC lg) (CRDDO (routs ** (rg, rprf))) = CRDDO (routs ** (Parallel lg rg, rprf))

parallelCR {lbl} (CRDDO (louts ** (lg, lprf))) (CRDDC rg) = let

  g = rewrite revEq $ concat_nil (louts ~~> lbl)
      in Parallel lg rg

  in CRDDO (louts ** (g, lprf))

parallelCR {lbl} (CRDDO (louts ** (lg, lprf))) (CRDDO (routs ** (rg, rprf))) = let

  g = rewrite collect_concat lbl louts routs
      in Parallel lg rg

  in CRDDO (louts ++ routs ** (g, nonempty_plusplus lprf))








export
collectOutsCR : {lbl' : BlockLabel} -> CompileResultUD lbl lbl' crt -> CompM $ CompileResultUU lbl crt
collectOutsCR {lbl' = labelPost} (CRUDC g) = pure $ CRUUC g
collectOutsCR {lbl' = labelPost} (CRUDO (lbls ** (g, prf))) = do
  SG ctx phis <- segregate (getContexts g)

  let ctxPost = ctx

  let post : CFG CBlock (Defined $ lbls ~~> labelPost) (Undefined labelPost)
      post = SingleVertex {vins = Just lbls} $ phis |++> emptyCBlock ctxPost
  
  let final = Series {prf = nonempty_map prf} g post

  pure $ CRUUO (labelPost ** final)


export
collectInsCR : {lbl, lbl' : BlockLabel}
            -> (ins : List BlockLabel)
            -> (phis : List (PhiInstr $ MkInputs ins))
            -> (ctx : lbl :~: VarCTX)
            -> CompileResultUD lbl lbl' crt
            -> CompM $ CompileResultDD (ins ~~> lbl) lbl' crt
collectInsCR ins phis ctxs res = do
  let pre = imap {ins = Just ins} (phis |++>) initCFG
        
  let res' = connectCRUDCRDD pre res
  pure res'












