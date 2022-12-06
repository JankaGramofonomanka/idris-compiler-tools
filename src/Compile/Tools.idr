module Compile.Tools

import Control.Monad.State
import Control.Monad.Either

import Data.List

import Data.Some
import Data.DMap


import LNG
import LLVM

import Utils



public export
GetLLType : LNGType -> LLType
GetLLType TInt = I32
GetLLType TBool = I1
GetLLType TVoid = Void


public export
data InStatus : Type where
  InOpen : InStatus
  InClosed : (inputs : Inputs)
          -> InStatus

public export
data OutStatus = OutOpen | OutClosed CFKind

-- TODO: `MbPhis InOpen = List [t ** Variable t]` - list of variables that need a phi assignment

public export
MbPhis : InStatus -> Type
MbPhis InOpen = ()
MbPhis (InClosed inputs) = List (PhiInstr inputs)



public export
MbTerm : OutStatus -> Type
MbTerm OutOpen = ()
MbTerm (OutClosed cfk) = CFInstr cfk

public export
record CBlock (label : BlockLabel) (is : InStatus) (os : OutStatus) where
  constructor MkBB
  phis : MbPhis is
  body : List STInstr
  term : MbTerm os
  
  -- TODO: divide assignments between individual instructions
  ctx : DMap Variable (LLValue . GetLLType)

export
initCBlock : CBlock lbl InOpen OutOpen
initCBlock = MkBB () [] () DMap.empty







infixr 7 <++, <+
infixr 6 <+|, |+>, |++>
infixr 5 +|, ++|

export
(++) : CBlock lbl is OutOpen -> CBlock lbl InOpen os -> CBlock lbl is os
MkBB phis body () m ++ MkBB () body' term' m' = MkBB phis (body ++ body') term' (DMap.merge m m')

export
(<++) : CBlock lbl is OutOpen -> List STInstr -> CBlock lbl is OutOpen
MkBB phis body () m <++ instrs = MkBB phis (body ++ instrs) () m

export
(<+) : CBlock lbl is OutOpen -> STInstr -> CBlock lbl is OutOpen
blk <+ instr = blk <++ [instr]

export
(<+|) : CBlock lbl is OutOpen -> CFInstr cfk -> CBlock lbl is (OutClosed cfk)
MkBB phis body () m <+| instr = MkBB phis body instr m

export
(|++>) : {inputs : Inputs}
      -> List (PhiInstr inputs)
      -> CBlock lbl InOpen os
      -> CBlock lbl (InClosed inputs) os
phis |++> MkBB () body term m = MkBB phis body term m

export
(|+>) : {inputs : Inputs}
     -> PhiInstr inputs
     -> CBlock lbl InOpen os
     -> CBlock lbl (InClosed inputs) os
instr |+> blk = [instr] |++> blk

export
(+|) : {inputs : Inputs}
    -> PhiInstr inputs
    -> CBlock lbl (InClosed inputs) os
    -> CBlock lbl (InClosed inputs) os
instr +| MkBB phis body term m = MkBB (instr :: phis) body term m

export
(++|) : {inputs : Inputs}
     -> List (PhiInstr inputs)
     -> CBlock lbl (InClosed inputs) os
     -> CBlock lbl (InClosed inputs) os
phis ++| blk = foldl (flip (+|)) blk phis














public export
record CompState where
  constructor MkCompST

public export
data Error : Type where
  NoSuchVariable : Variable t -> Error


public export
CompM : Type -> Type
CompM = StateT CompState (Either Error)

export
assign : Variable t -> LLValue (GetLLType t) -> CBlock lbl is OutOpen -> CBlock lbl is OutOpen
assign var reg (MkBB phis body term ctx) = MkBB phis body term $ insert var reg ctx

export
freshReg : CompM (Reg t)

export
freshLabel : CompM BlockLabel

export
addBlock : CBlock lbl (InClosed inputs) (OutClosed cfk) -> CompM ()

export
getValue : Variable t -> CompM (LLValue (GetLLType t))

export
getFunPtr : FunId t ts -> CompM $ LLValue (Ptr $ FunType (GetLLType t) (map GetLLType ts))

export
freshRegister : CompM (Reg t)



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














