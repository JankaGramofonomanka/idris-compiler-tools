module Compile.Tools.CBlock

import Data.DMap

import LLVM
import LNG

import Compile.Tools

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
(|++>) : List (PhiInstr inputs)
      -> CBlock lbl InOpen os
      -> CBlock lbl (InClosed inputs) os
phis |++> MkBB () body term m = MkBB phis body term m

export
(|+>) : PhiInstr inputs
     -> CBlock lbl InOpen os
     -> CBlock lbl (InClosed inputs) os
instr |+> blk = [instr] |++> blk

export
(+|) : PhiInstr inputs
    -> CBlock lbl (InClosed inputs) os
    -> CBlock lbl (InClosed inputs) os
instr +| MkBB phis body term m = MkBB (instr :: phis) body term m

export
(++|) : List (PhiInstr inputs)
     -> CBlock lbl (InClosed inputs) os
     -> CBlock lbl (InClosed inputs) os
phis ++| blk = foldl (flip (+|)) blk phis

