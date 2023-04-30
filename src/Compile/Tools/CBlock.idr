module Compile.Tools.CBlock

import Data.Attached
import Data.DMap
import Data.DList
import Data.GCompare

import LLVM
import LNG

import Compile.Tools
import CFG

-- TODO: `MbPhis Undefined = List [t ** Variable t]` - list of variables that need a phi assignment

public export
MbPhis : Neighbors BlockLabel -> Type
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
MbTerm : Neighbors BlockLabel -> Type
MbTerm Nothing = ()
MbTerm (Just outs) = CFInstr (toCFK outs)

public export
record CBlock (label : BlockLabel) (ins : Neighbors BlockLabel) (outs : Neighbors BlockLabel) where
  constructor MkBB
  phis : MbPhis ins
  body : List STInstr
  term : MbTerm outs
  
  -- TODO: divide assignments between individual instructions
  ctx : DMap Variable (LLValue . GetLLType)

export
context : {lbl : BlockLabel} -> CBlock lbl ins Undefined -> lbl :~: DMap Variable (LLValue . GetLLType)
context {lbl} blk = attach lbl (ctx blk)

export
contexts : {0 lbl : BlockLabel}
        -> {outs : List BlockLabel}
        -> CBlock lbl ins (Just outs)
        -> DList (:~: DMap Variable (LLValue . GetLLType)) (lbl ~>> outs)
contexts {lbl, outs} blk = replicate' lblTo outs (\l => attach (lblTo l) (ctx blk)) where
  0 lblTo : BlockLabel -> Edge BlockLabel
  lblTo v = lbl ~> v
  
export
initCBlock : CBlock lbl Undefined Undefined
initCBlock = MkBB () [] () DMap.empty

export
emptyCBlock : DMap Variable (LLValue . GetLLType) -> CBlock lbl Undefined Undefined
emptyCBlock ctx = MkBB () [] () ctx





infixr 7 <++, <+
infixr 6 <+|, |+>, |++>
infixr 5 +|, ++|

export
(++) : CBlock lbl ins Undefined -> CBlock lbl Undefined outs -> CBlock lbl ins outs
MkBB phis body () m ++ MkBB () body' term' m'
  = MkBB phis (body ++ body') term' (m' `DMap.union` m {- `m'` takes precedence -})

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



-- TODO: consider hiding the attachment somewhere, eg. in the `CBlock` itself
export
getContext : {lbl : BlockLabel}
          -> CFG CBlock ins (Undefined lbl)
          -> lbl :~: DMap Variable (LLValue . GetLLType)
getContext {lbl} cfg = attach lbl $ oget ctx cfg

export
getContexts : CFG CBlock ins (Defined outs)
           -> DList (:~: DMap Variable (LLValue . GetLLType)) outs
getContexts cfg = oget' contexts cfg

