module Compile.Tools.CompileResult

import Control.Monad.State

import Data.DMap
import Data.DList
import Data.Attached

import LLVM
import LNG

import Compile.Tools
import Compile.Tools.CBlock
import Compile.Tools.VariableCTX
import Compile.Tools.CompM
import CFG

import Utils


export
initCFG : CFG CBlock (Undefined lbl) (Undefined lbl)
initCFG = initGraph initCBlock





public export
data CRType = Open | Closed

public export
OpenOr : CRType -> Lazy CRType -> CRType
OpenOr Open rt = Open
OpenOr Closed rt = rt


public export
ClosedOr : CRType -> Lazy CRType -> CRType
ClosedOr Closed rt = Closed
ClosedOr Open rt = rt

total
export
closed_or_commut : (x, y : CRType) -> ClosedOr x y = ClosedOr y x
closed_or_commut Closed Closed = Refl
closed_or_commut Closed Open = Refl
closed_or_commut Open Closed = Refl
closed_or_commut Open Open = Refl

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
  CRUDO : (lbls ** CFG CBlock (Undefined lbl) (Defined $ lbls ~~> lbl'))
       -> CompileResultUD lbl lbl' Open



public export
data CompileResultDD : List (Edge BlockLabel) -> BlockLabel -> CRType -> Type where
  CRDDC : CFG CBlock (Defined edges) Closed -> CompileResultDD edges lbl Closed
  CRDDO : (lbls ** CFG CBlock (Defined edges) (Defined $ lbls ~~> lbl))
       -> CompileResultDD edges lbl Open





export
unwrapCRUD : CompileResultUD lbl lbl' crt
          -> (outs ** CFG CBlock (Undefined lbl) (Defined $ outs ~~> lbl'))
unwrapCRUD (CRUDC g) = ([] ** g)
unwrapCRUD (CRUDO (outs ** g)) = (outs ** g)

export
unwrapCRDD : CompileResultDD edges lbl crt
          -> (outs ** CFG CBlock (Defined edges) (Defined $ outs ~~> lbl))
unwrapCRDD (CRDDC g) = ([] ** (g))
unwrapCRDD (CRDDO (outs ** g)) = (outs ** g)






export
emptyCRUU : (lbl : BlockLabel) -> CompileResultUU lbl Open
emptyCRUU lbl = CRUUO (lbl ** initCFG)

export
emptyCRUD : (lbl, lbl' : BlockLabel) -> CompileResultUD lbl lbl' Open
emptyCRUD lbl lbl' = CRUDO ([lbl] ** omap {outs = Just [lbl']} (<+| Branch lbl') initCFG)








export
connectCRUU : CFG CBlock (Undefined lbl) (Undefined lbl') -> CompileResultUU lbl' os -> CompileResultUU lbl os
connectCRUU g (CRUUC g') = CRUUC $ connect g g'
connectCRUU g (CRUUO (lbl'' ** g')) = CRUUO $ (lbl'' ** connect g g')


export
connectCRUD : CFG CBlock (Undefined lbl) (Undefined lbl')
           -> CompileResultUD lbl' lbl'' os
           -> CompileResultUD lbl lbl'' os
connectCRUD g (CRUDC g') = CRUDC $ connect g g'
connectCRUD g (CRUDO (lbls ** g')) = CRUDO $ (lbls ** connect g g')


export
connectCRDDCRUD : CFG CBlock (Undefined lbl) (Defined edges)
               -> CompileResultDD edges lbl' crt
               -> CompileResultUD lbl lbl' crt

connectCRDDCRUD pre (CRDDC g) = CRUDC (Connect pre g)
connectCRDDCRUD pre (CRDDO (lbls ** g)) = let g' = Connect pre g in CRUDO (lbls ** g')

export
connectCRUDCRDD : CFG CBlock (Defined edges) (Undefined lbl)
               -> CompileResultUD lbl lbl' crt
               -> CompileResultDD edges lbl' crt
connectCRUDCRDD pre (CRUDC g) = CRDDC (connect pre g)
connectCRUDCRDD pre (CRUDO (lbls ** g)) = let g' = connect pre g in CRDDO (lbls ** g')




export
parallelCR : {lbl : BlockLabel}
          -> (lres : CompileResultDD ledges lbl lcrt)
          -> (rres : CompileResultDD redges lbl rcrt)
          
          -> CompileResultDD (ledges ++ redges) lbl (OpenOr lcrt rcrt)

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








export
collectOutsCR : {lbl' : BlockLabel} -> CompileResultUD lbl lbl' crt -> CompM $ CompileResultUU lbl crt
collectOutsCR {lbl' = labelPost} (CRUDC g) = pure $ CRUUC g
collectOutsCR {lbl' = labelPost} (CRUDO (lbls ** g)) = do
  SG ctx phis <- segregate (getContexts g)

  let ctxPost = ctx

  let post : CFG CBlock (Defined $ lbls ~~> labelPost) (Undefined labelPost)
      post = SingleVertex {vins = Just lbls} $ phis |++> emptyCBlock (detach ctxPost)
  
  let final = Connect g post

  pure $ CRUUO (labelPost ** final)


export
collectInsCR : {lbl' : BlockLabel}
            -> (ins : List BlockLabel)
            -> (phis : List (PhiInstr $ MkInputs ins))
            -> (ctx : lbl :~: VarCTX)
            -> CompileResultUD lbl lbl' crt
            -> CompM $ CompileResultDD (ins ~~> lbl) lbl' crt
collectInsCR ins phis ctxs res = do
  let pre = imap {ins = Just ins} (phis |++>) initCFG
        
  let res' = connectCRUDCRDD pre res
  pure res'
  





public export
data Compatible : CRType -> List BlockLabel -> Type where
  CompatClosed  : Compatible Closed []
  CompatOpen    : Compatible Open [lbl]












