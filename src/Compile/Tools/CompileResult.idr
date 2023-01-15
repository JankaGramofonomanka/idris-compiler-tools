module Compile.Tools.CompileResult

import Control.Monad.State

import Data.DMap
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


public export
toCRType : Maybe BlockLabel -> CRType
toCRType Nothing = Closed
toCRType (Just _) = Open


public export
data CompileResult : BlockLabel -> CRType -> Type where
  CRC : CFG CBlock (Undefined lbl) Closed -> CompileResult lbl Closed
  CRO : (lbl' **  ( CFG CBlock (Undefined lbl) (Undefined lbl')
                  , Attached lbl' VarCTX
                  ))
     -> CompileResult lbl Open


export
initCR : (lbl : BlockLabel) -> CompileResult lbl Open
initCR lbl = CRO (lbl ** (initCFG, attach lbl emptyCtx))




export
combineCR : CFG CBlock (Undefined lbl) (Undefined lbl') -> CompileResult lbl' os -> CompileResult lbl os
combineCR g (CRC g') = CRC $ connect g g'
combineCR g (CRO (lbl'' ** (g', ctx))) = CRO $ (lbl'' ** (connect g g', ctx))




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








