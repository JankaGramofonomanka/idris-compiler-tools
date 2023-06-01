module Compile.Data.CBlock

import Data.Attached
import Data.DList
import Data.GCompare
import Data.The

import LLVM
import LNG.TypeChecked

import Compile.Data.Context
import Compile.Utils
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
  theLabel : The label

  phis : MbPhis ins
  body : List STInstr
  term : MbTerm outs
  
  -- TODO: divide assignments between individual instructions
  ctx : label :~: VarCTX

export
contexts : {0 lbl : BlockLabel}
        -> {outs : List BlockLabel}
        -> CBlock lbl ins (Just outs)
        -> DList (:~: VarCTX) (lbl ~>> outs)
contexts {lbl, outs} blk = replicate' lblTo outs (\l => attach (lblTo l) (detach $ blk.ctx)) where
  0 lblTo : BlockLabel -> Edge BlockLabel
  lblTo v = lbl ~> v
  
export
emptyCBlock : {lbl : BlockLabel} -> lbl :~: VarCTX -> CBlock lbl Undefined Undefined
emptyCBlock {lbl} ctx = MkBB { theLabel = MkThe lbl, phis = (), body = [], term = (), ctx}





infixr 7 <++, <+
infixr 6 <+|, |+>, |++>
infixr 5 +|, ++|

export
(++) : CBlock lbl ins Undefined -> CBlock lbl Undefined outs -> CBlock lbl ins outs
(++) 
  ( MkBB
    { theLabel
    , phis
    , body
    , term = ()
    , ctx
    }
  )
  ( MkBB
    { theLabel = theLabel'
    , phis = ()
    , body = body'
    , term = term'
    , ctx = ctx'
    }
  )
  = MkBB
    { theLabel
    , phis
    , body = (body ++ body')
    , term = term'
    --, ctx = (ctx' `union` ctx {- `ctx'` takes precedence -})
    , ctx = ctx' -- This assumes `ctx'` contains `ctx`
    }

export
(<++) : CBlock lbl ins Undefined -> List STInstr -> CBlock lbl ins Undefined
(MkBB { theLabel, phis , body , term = (), ctx }) <++ instrs
  = MkBB { theLabel, phis, body = (body ++ instrs), term = (), ctx}

export
(<+) : CBlock lbl ins Undefined -> STInstr -> CBlock lbl ins Undefined
blk <+ instr = blk <++ [instr]

export
(<+|) : CBlock lbl ins Undefined -> CFInstr (toCFK outs) -> CBlock lbl ins (Just outs)
MkBB { theLabel, phis, body, term = (), ctx } <+| term = MkBB { theLabel, phis, body, term, ctx }

export
(|++>) : List (PhiInstr (MkInputs inputs))
      -> CBlock lbl Undefined outs
      -> CBlock lbl (Just inputs) outs
phis |++> MkBB { theLabel, phis = (), body, term, ctx } = MkBB { theLabel, phis, body, term, ctx }

export
(|+>) : PhiInstr (MkInputs inputs)
     -> CBlock lbl Undefined outs
     -> CBlock lbl (Just inputs) outs
instr |+> blk = [instr] |++> blk

export
(+|) : PhiInstr (MkInputs inputs)
    -> CBlock lbl (Just inputs) outs
    -> CBlock lbl (Just inputs) outs
instr +| MkBB { theLabel, phis, body, term, ctx } = MkBB { theLabel, phis = (instr :: phis), body, term, ctx }

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
          -> lbl :~: VarCTX
getContext {lbl} cfg = oget ctx cfg

export
getContexts : CFG CBlock ins (Defined outs)
           -> DList (:~: VarCTX) outs
getContexts cfg = oget' contexts cfg

