module Compile.Tools.CompileResult

import Control.Monad.State

import LLVM
import LNG

import Compile.Tools
import Compile.Tools.CBlock
import Compile.Tools.CompM





public export
data CompileResult : BlockLabel -> (Maybe BlockLabel) -> Type where
  SingleBLKC : (cfk ** CBlock lbl InOpen (OutClosed cfk)) -> CompileResult lbl Nothing
  SingleBLKO : CBlock lbl InOpen OutOpen -> CompileResult lbl (Just lbl)
  DoubleBLK : (cfk ** CBlock lblIn InOpen (OutClosed cfk))
           -> (inputs ** CBlock lblOut (InClosed inputs) OutOpen)
           -> CompileResult lblIn (Just lblOut)

export
initCR : CompileResult lbl (Just lbl)
initCR = SingleBLKO initCBlock



export
mapOO : ({is : InStatus} -> CBlock lbl is OutOpen -> CBlock lbl is OutOpen)
     -> CompileResult lbl' (Just lbl)
     -> CompileResult lbl' (Just lbl)
mapOO f (SingleBLKO blk) = SingleBLKO (f blk)
mapOO f (DoubleBLK blkIn (ins ** blkOut))
  = DoubleBLK blkIn (ins ** f blkOut)

export
closeCR : {cfk : CFKind} -> CFInstr cfk -> CompileResult lbl (Just lbl') -> CompM (CompileResult lbl Nothing)
closeCR {cfk} instr (SingleBLKO blk) = pure $ SingleBLKC (cfk ** blk <+| instr)
closeCR {cfk} instr (DoubleBLK blkIn (inputs ** blkOut)) = do
  addBlock $ blkOut <+| instr
  pure $ SingleBLKC blkIn



export
combineCR : CompileResult lbl (Just lbl') -> CompileResult lbl' os -> CompM (CompileResult lbl os)

combineCR (SingleBLKO blk) (SingleBLKO blk')                  = pure $ SingleBLKO (blk ++ blk')
combineCR (SingleBLKO blk) (DoubleBLK (cfk ** blkIn) blkOut)  = pure $ DoubleBLK (cfk ** blk ++ blkIn) blkOut
combineCR (SingleBLKO blk) (SingleBLKC (cfk ** blk'))         = pure $ SingleBLKC (cfk ** blk ++ blk')

combineCR (DoubleBLK blkIn (ins ** blkOut)) (SingleBLKO blk) = do
  pure $ DoubleBLK blkIn (ins ** blkOut ++ blk)

combineCR (DoubleBLK blkIn (ins ** blkOut)) (DoubleBLK (cfk ** blkIn') blkOut') = do
  addBlock $ blkOut ++ blkIn'
  pure $ DoubleBLK blkIn blkOut'

combineCR (DoubleBLK blkIn (ins ** blkOut)) (SingleBLKC (cfk ** blk)) = do
  addBlock $ blkOut ++ blk
  pure $ SingleBLKC blkIn













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
data CompileResult' : BlockLabel -> CRType -> Type where
  CRC : CompileResult lbl Nothing -> CompileResult' lbl Closed
  CRO : (lbl' ** CompileResult lbl (Just lbl')) -> CompileResult' lbl Open


export
initCR' : (lbl : BlockLabel) -> CompileResult' lbl Open
initCR' lbl = CRO (lbl ** initCR)



public export
data MLabel : CRType -> Type where
  NoLabel : MLabel Closed
  YesLabel : BlockLabel -> MLabel Open

export
combineCR' : CompileResult lbl (Just lbl') -> CompileResult' lbl' os -> CompM (CompileResult' lbl os)
combineCR' cr (CRC cr') = CRC <$> combineCR cr cr'
combineCR' cr (CRO (lbl'' ** cr')) = do
  cr'' <- combineCR cr cr'
  pure $ CRO (lbl'' ** cr'')
  
export getOutLabel : CompileResult' lbl os -> MLabel os
getOutLabel (CRC cr) = NoLabel
getOutLabel (CRO (lbl ** cr)) = YesLabel lbl
  
export
getOutputs : CompileResult' lbl os -> List BlockLabel
getOutputs (CRC cr) = []
getOutputs (CRO (lbl ** cr)) = [lbl]

public export
toCRType : Maybe BlockLabel -> CRType
toCRType Nothing = Closed
toCRType (Just _) = Open















