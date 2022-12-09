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

implementation Connectable VBlock where
  cnct = (++)


public export
data CompileResult : BlockLabel -> (Maybe BlockLabel) -> Type where
  CRClosed : Graph VBlock (Undefined lbl) Closed -> CompileResult lbl Nothing
  CROpen : Graph VBlock (Undefined lblIn) (Undefined lblOut) -> CompileResult lblIn (Just lblOut)
  

export
initCR : CompileResult lbl (Just lbl)
initCR = CROpen (SingleVertex {vins = Nothing} {vouts = Nothing} initCBlock)



export
mapOO : ({is : InStatus} -> CBlock lblOut is OutOpen -> CBlock lblOut is OutOpen)
     -> CompileResult lblIn (Just lblOut)
     -> CompileResult lblIn (Just lblOut)
mapOO f (CROpen {lblIn} g) = CROpen $ mapOut {outs = Undefined} f g


export
addReturn : CFInstr Return -> CompileResult lbl (Just lbl') -> CompileResult lbl Nothing
addReturn instr (CROpen g) = CRClosed $ mapOut {outs = Just []} (<+| instr) g --(<+| instr) g
--closeCR : {cfk : CFKind} -> CFInstr cfk -> CompileResult lbl (Just lbl') -> CompileResult lbl Nothing
--closeCR {cfk} instr (Open g) = Closed $ mapOut {outs = Just []} (<+| instr) g --(<+| instr) g
--closeCR {cfk} instr (Open g) = Open $ mapOut (<+| instr) g
--closeCR {cfk} instr (DoubleBLK blkIn (inputs ** blkOut)) = do
--  addBlock $ blkOut <+| instr
--  pure $ SingleBLKC blkIn


export
combineCR : CompileResult lbl (Just lbl') -> CompileResult lbl' os -> CompileResult lbl os
combineCR (CROpen g) (CRClosed g') = CRClosed $ connect g g'
combineCR (CROpen g) (CROpen g') = CROpen $ connect g g'










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
data CompileResult' : BlockLabel -> CRType -> Type where
  CRC : CompileResult lbl Nothing -> CompileResult' lbl Closed
  CRO : (lbl' ** CompileResult lbl (Just lbl')) -> CompileResult' lbl Open


export
initCR' : (lbl : BlockLabel) -> CompileResult' lbl Open
initCR' lbl = CRO (lbl ** initCR)




export
combineCR' : CompileResult lbl (Just lbl') -> CompileResult' lbl' os -> CompileResult' lbl os
combineCR' cr (CRC cr') = CRC $ combineCR cr cr'
combineCR' cr (CRO (lbl'' ** cr')) = CRO $ (lbl'' ** combineCR cr cr')




public export
data MLabel : CRType -> Type where
  NoLabel : MLabel Closed
  YesLabel : BlockLabel -> MLabel Open

export
getOutLabel : CompileResult' lbl os -> MLabel os
getOutLabel (CRC cr) = NoLabel
getOutLabel (CRO (lbl ** cr)) = YesLabel lbl
  
export
getOutputs : CompileResult' lbl os -> List BlockLabel
getOutputs (CRC cr) = []
getOutputs (CRO (lbl ** cr)) = [lbl]
















