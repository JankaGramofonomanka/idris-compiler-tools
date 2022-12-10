module Compile.Tools.CBlock

import Data.DMap

import LLVM
import LNG

import Compile.Tools
import CFG

-- TODO: `MbPhis Undefined = List [t ** Variable t]` - list of variables that need a phi assignment

public export
MbPhis : Endpoint BlockLabel -> Type
MbPhis Nothing = ()
MbPhis (Just ins) = List (PhiInstr $ MkInputs ins)


public export
toCFK : List BlockLabel -> CFKind
toCFK [] = Return
toCFK (lbl :: lbls) = Jump (lbl :: lbls)

public export
fromCFK : CFKind -> List BlockLabel
fromCFK Return = []
fromCFK (Jump lbls) = lbls

public export
MbTerm : Endpoint BlockLabel -> Type
MbTerm Nothing = ()
MbTerm (Just outs) = CFInstr (toCFK outs)

public export
record CBlock (label : BlockLabel) (ins : Endpoint BlockLabel) (outs : Endpoint BlockLabel) where
  constructor MkBB
  phis : MbPhis ins
  body : List STInstr
  term : MbTerm outs
  
  -- TODO: divide assignments between individual instructions
  ctx : DMap Variable (LLValue . GetLLType)

export
initCBlock : CBlock lbl Undefined Undefined
initCBlock = MkBB () [] () DMap.empty







infixr 7 <++, <+
infixr 6 <+|, |+>, |++>
infixr 5 +|, ++|

export
(++) : CBlock lbl ins Undefined -> CBlock lbl Undefined outs -> CBlock lbl ins outs
MkBB phis body () m ++ MkBB () body' term' m' = MkBB phis (body ++ body') term' (DMap.merge m m')

export
(<++) : CBlock lbl ins Undefined -> List STInstr -> CBlock lbl ins Undefined
MkBB phis body () m <++ instrs = MkBB phis (body ++ instrs) () m

export
(<+) : CBlock lbl ins Undefined -> STInstr -> CBlock lbl ins Undefined
blk <+ instr = blk <++ [instr]

export
(<+|) : CBlock lbl ins Undefined -> CFInstr (toCFK outs) -> CBlock lbl ins (Just outs)
MkBB phis body () m <+| instr = MkBB phis body instr m

export
(|++>) : List (PhiInstr (MkInputs inputs))
      -> CBlock lbl Undefined outs
      -> CBlock lbl (Just inputs) outs
phis |++> MkBB () body term m = MkBB phis body term m

export
(|+>) : PhiInstr (MkInputs inputs)
     -> CBlock lbl Undefined outs
     -> CBlock lbl (Just inputs) outs
instr |+> blk = [instr] |++> blk

export
(+|) : PhiInstr (MkInputs inputs)
    -> CBlock lbl (Just inputs) outs
    -> CBlock lbl (Just inputs) outs
instr +| MkBB phis body term m = MkBB (instr :: phis) body term m

export
(++|) : List (PhiInstr (MkInputs inputs))
     -> CBlock lbl (Just inputs) outs
     -> CBlock lbl (Just inputs) outs
phis ++| blk = foldl (flip (+|)) blk phis


export
implementation Connectable CBlock where
  cnct = (++)




