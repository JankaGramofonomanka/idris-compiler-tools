module Compile.Tools.CompileResult

import Control.Monad.State

import LLVM
import LNG

import Compile.Tools
import Compile.Tools.CBlock
import Compile.Tools.CompM
import CFG.Simple



public export
toIS : Endpoint BlockLabel -> InStatus
toIS Nothing = InOpen
toIS (Just labels) = InClosed (MkInputs labels)

public export
toOS : Endpoint BlockLabel -> OutStatus
toOS Nothing = OutOpen
toOS (Just []) = OutClosed Return
toOS (Just labels) = OutClosed (Jump labels)

public export
VBlock : Vertex BlockLabel
VBlock l ins outs = CBlock l (toIS ins) (toOS outs)

export
implementation Connectable VBlock where
  cnct = (++)


export
initG : Graph VBlock (Undefined lbl) (Undefined lbl)
initG = initGraph initCBlock





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
  CRC : Graph VBlock (Undefined lbl) Closed -> CompileResult lbl Closed
  CRO : (lbl' ** Graph VBlock (Undefined lbl) (Undefined lbl')) -> CompileResult lbl Open


export
initCR : (lbl : BlockLabel) -> CompileResult lbl Open
initCR lbl = CRO (lbl ** initG)




export
combineCR : Graph VBlock (Undefined lbl) (Undefined lbl') -> CompileResult lbl' os -> CompileResult lbl os
combineCR g (CRC g') = CRC $ connect g g'
combineCR g (CRO (lbl'' ** g')) = CRO $ (lbl'' ** connect g g')




public export
data MLabel : CRType -> Type where
  NoLabel : MLabel Closed
  YesLabel : BlockLabel -> MLabel Open

export
getOutLabel : CompileResult lbl os -> MLabel os
getOutLabel (CRC cr) = NoLabel
getOutLabel (CRO (lbl ** cr)) = YesLabel lbl
  
export
getOutputs : CompileResult lbl os -> List BlockLabel
getOutputs (CRC cr) = []
getOutputs (CRO (lbl ** cr)) = [lbl]
















