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
import CFG


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


export
initCRUU : (lbl : BlockLabel) -> CompileResultUU lbl Open
initCRUU lbl = CRUUO (lbl ** (initCFG, attach lbl emptyCtx))




export
combineCRUU : CFG CBlock (Undefined lbl) (Undefined lbl') -> CompileResultUU lbl' os -> CompileResultUU lbl os
combineCRUU g (CRUUC g') = CRUUC $ connect g g'
combineCRUU g (CRUUO (lbl'' ** (g', ctx))) = CRUUO $ (lbl'' ** (connect g g', ctx))




public export
data Compatible : CRType -> List BlockLabel -> Type where
  CompatClosed  : Compatible Closed []
  CompatOpen    : Compatible Open [lbl]


-- TODO: consider hiding the attachment somewhere, eg. in the `CBlock` itself
export
getContext : {lbl : BlockLabel}
          -> CFG CBlock ins (Undefined lbl)
          -> Attached lbl $ DMap Variable (LLValue . GetLLType)
getContext {lbl} cfg = attach lbl $ getOut ctx cfg





public export
data CompileResultUD : BlockLabel -> BlockLabel -> CRType -> Type where
  CRUDC : CFG CBlock (Undefined lbl) Closed -> CompileResultUD lbl lbl' Closed
  CRUDO : (lbls ** ( CFG CBlock (Undefined lbl) (Ends $ map (~> lbl') lbls)
                   , DList (\lbl' => Attached lbl' VarCTX) lbls
                   ))
       -> CompileResultUD lbl lbl' Open


export
initCRUD : (lbl, lbl' : BlockLabel) -> CompileResultUD lbl lbl' Open
initCRUD lbl lbl' = CRUDO ([lbl] ** (mapOut {outs = Just [lbl']} (<+| Branch lbl') initCFG, [attach lbl emptyCtx]))


export
combineCRUD : CFG CBlock (Undefined lbl) (Undefined lbl') -> CompileResultUD lbl' lbl'' os -> CompileResultUD lbl lbl'' os
combineCRUD g (CRUDC g') = CRUDC $ connect g g'
combineCRUD g (CRUDO (lbls ** (g', ctxs))) = CRUDO $ (lbls ** (connect g g', ctxs))






public export
data CompileResultDD : Edge BlockLabel -> BlockLabel -> CRType -> Type where
  CRDDC : CFG CBlock (Ends [edge]) Closed -> CompileResultDD edge lbl Closed
  CRDDO : (lbls ** ( CFG CBlock (Ends [edge]) (Ends $ map (~> lbl) lbls)
                   , DList (\l => Attached l VarCTX) lbls
                   ))
       -> CompileResultDD edge lbl Open









