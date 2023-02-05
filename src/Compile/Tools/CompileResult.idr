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
  CRUUO : (lbl' **  ( CFG CBlock (Undefined lbl) (Undefined lbl')
                    , Attached lbl' VarCTX
                    ))
       -> CompileResultUU lbl Open



public export
data CompileResultUD : BlockLabel -> BlockLabel -> CRType -> Type where
  CRUDC : CFG CBlock (Undefined lbl) Closed -> CompileResultUD lbl lbl' Closed
  CRUDO : (lbls ** ( CFG CBlock (Undefined lbl) (Defined $ map (~> lbl') lbls)
                   , DList (\lbl' => Attached lbl' VarCTX) lbls
                   ))
       -> CompileResultUD lbl lbl' Open



public export
data CompileResultDD : BlockLabel -> List BlockLabel -> BlockLabel -> CRType -> Type where
  CRDDC : CFG CBlock (Defined $ map (lbl ~>) lbls) Closed -> CompileResultDD lbl lbls lbl' Closed
  CRDDO : (lbls' ** ( CFG CBlock (Defined $ map (lbl ~>) lbls) (Defined $ map (~> lbl') lbls')
                    , DList (\l => Attached l VarCTX) lbls'
                    ))
       -> CompileResultDD lbl lbls lbl' Open





export
unwrapCRUD : CompileResultUD lbl lbl' crt
          -> (outs ** ( CFG CBlock (Undefined lbl) (Defined $ map (~> lbl') outs)
                      , DList (\l => Attached l VarCTX) outs
                      ))
unwrapCRUD (CRUDC g) = ([] ** (g, []))
unwrapCRUD (CRUDO (outs ** (g, ctxs))) = (outs ** (g, ctxs))

export
unwrapCRDD : CompileResultDD lbl lbls lbl' crt
          -> (outs ** ( CFG CBlock (Defined $ map (lbl ~>) lbls) (Defined $ map (~> lbl') outs)
                      , DList (\l => Attached l VarCTX) outs
                      ))
unwrapCRDD (CRDDC g) = ([] ** (g, []))
unwrapCRDD (CRDDO (outs ** (g, ctxs))) = (outs ** (g, ctxs))






export
initCRUU : (lbl : BlockLabel) -> CompileResultUU lbl Open
initCRUU lbl = CRUUO (lbl ** (initCFG, attach lbl emptyCtx))

export
initCRUD : (lbl, lbl' : BlockLabel) -> CompileResultUD lbl lbl' Open
initCRUD lbl lbl' = CRUDO ([lbl] ** (omap {outs = Just [lbl']} (<+| Branch lbl') initCFG, [attach lbl emptyCtx]))








export
connectCRUU : CFG CBlock (Undefined lbl) (Undefined lbl') -> CompileResultUU lbl' os -> CompileResultUU lbl os
connectCRUU g (CRUUC g') = CRUUC $ connect g g'
connectCRUU g (CRUUO (lbl'' ** (g', ctx))) = CRUUO $ (lbl'' ** (connect g g', ctx))


export
connectCRUD : CFG CBlock (Undefined lbl) (Undefined lbl')
           -> CompileResultUD lbl' lbl'' os
           -> CompileResultUD lbl lbl'' os
connectCRUD g (CRUDC g') = CRUDC $ connect g g'
connectCRUD g (CRUDO (lbls ** (g', ctxs))) = CRUDO $ (lbls ** (connect g g', ctxs))


export
connectCRDD : CFG CBlock (Undefined lbl) (Defined $ map (lbl' ~>) lbls)
           -> CompileResultDD lbl' lbls lbl'' crt
           -> CompileResultUD lbl lbl'' crt

connectCRDD pre (CRDDC g) = CRUDC (Connect pre g)
connectCRDD pre (CRDDO (lbls ** (g, ctxs))) = let
  
  g' = Connect pre g
  
  in CRUDO (lbls ** (g', ctxs))







export
parallelCR : {lbl' : BlockLabel}
          -> (lres : CompileResultDD lbl lins lbl' lcrt)
          -> (rres : CompileResultDD lbl rins lbl' rcrt)
          
          -> CompileResultDD lbl (lins ++ rins) lbl' (OpenOr lcrt rcrt)

parallelCR {lbl'} (CRDDC lg) (CRDDC rg)
  = CRDDC $ rewrite map_concat {f = (lbl ~>)} lins rins in Parallel lg rg

parallelCR {lbl'} (CRDDC lg) (CRDDO (routs ** (rg, rctxs))) = let
  g = rewrite map_concat {f = (lbl ~>)} lins rins in Parallel lg rg
  in CRDDO (routs ** (g, rctxs))

parallelCR {lbl'} (CRDDO (louts ** (lg, lctxs))) (CRDDC rg) = let

  g = rewrite map_concat {f = (lbl ~>)} lins rins
      in rewrite revEq $ concat_nil (map (~> lbl') louts)
      in Parallel lg rg

  in CRDDO (louts ** (g, lctxs))

parallelCR {lbl'} (CRDDO (louts ** (lg, lctxs))) (CRDDO (routs ** (rg, rctxs))) = let

  g = rewrite map_concat {f = (lbl ~>)} lins rins
      in rewrite map_concat {f = (~> lbl')} louts routs
      in Parallel lg rg

  in CRDDO (louts ++ routs ** (g, lctxs ++ rctxs))








export
collectCR : {lbl' : BlockLabel} -> CompileResultUD lbl lbl' crt -> CompM $ CompileResultUU lbl crt
collectCR {lbl' = labelPost} (CRUDC g) = pure $ CRUUC g
collectCR {lbl' = labelPost} (CRUDO (lbls ** (g, ctxs))) = do
  SG ctx phis <- segregate ctxs

  let ctxPost = attach labelPost ctx

  let post : CFG CBlock (Defined $ map (~> labelPost) lbls) (Undefined labelPost)
      post = SingleVertex {vins = Just lbls} $ phis |++> emptyCBlock (detach ctxPost)
  
  let final = Connect g post

  pure $ CRUUO (labelPost ** (final, ctxPost))







public export
data Compatible : CRType -> List BlockLabel -> Type where
  CompatClosed  : Compatible Closed []
  CompatOpen    : Compatible Open [lbl]


-- TODO: consider hiding the attachment somewhere, eg. in the `CBlock` itself
export
getContext : {lbl : BlockLabel}
          -> CFG CBlock ins (Undefined lbl)
          -> Attached lbl $ DMap Variable (LLValue . GetLLType)
getContext {lbl} cfg = attach lbl $ oget ctx cfg












