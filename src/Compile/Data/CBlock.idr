module Compile.Data.CBlock

import Data.Attached
import Data.Doc
import Data.DList
import Data.GCompare
import Data.The

import LLVM
import LLVM.Render
import LNG.TypeChecked
import LNG.TypeChecked.Render

import Compile.Data.Context
import Compile.Utils
import CFG

import Utils

-- TODO: `MbPhis Undefined = List [t ** Variable t]` - list of variables that need a phi assignment

public export
MbPhis : Neighbors BlockLabel -> Type
MbPhis Nothing = ()
MbPhis (Just ins) = List (PhiInstr ins, Maybe String)


public export
toCFK : List BlockLabel -> CFKind
toCFK [] = Return
toCFK (lbl :: lbls) = Jump (lbl :: lbls)

public export
fromCFK : CFKind -> List BlockLabel
fromCFK Return = []
fromCFK (Jump lbls) = lbls

public export
MbTerm : LLType -> Neighbors BlockLabel -> Type
MbTerm rt Nothing = ()
MbTerm rt (Just outs) = CFInstr rt (toCFK outs)

public export
record CBlock (retT : LLType) (label : BlockLabel) (ins : Neighbors BlockLabel) (outs : Neighbors BlockLabel) where
  constructor MkBB
  theLabel : The label

  phis : MbPhis ins
  body : List (STInstr, Maybe String)
  term : MbTerm retT outs
  
  -- TODO: divide assignments between individual instructions
  ctx : label :~: VarCTX

noComment : instr -> (instr, Maybe String)
noComment instr = (instr, Nothing)

export
contexts : {0 lbl : BlockLabel}
        -> {outs : List BlockLabel}
        -> CBlock rt lbl ins (Just outs)
        -> DList (:~: VarCTX) (lbl ~>> outs)
contexts {lbl, outs} blk = replicate' lblTo outs (\l => attach (lblTo l) (detach $ blk.ctx)) where
  0 lblTo : BlockLabel -> Edge BlockLabel
  lblTo v = lbl ~> v
  
export
emptyCBlock : {lbl : BlockLabel} -> lbl :~: VarCTX -> CBlock rt lbl Undefined Undefined
emptyCBlock {lbl} ctx = MkBB { theLabel = MkThe lbl, phis = (), body = [], term = (), ctx}

export
assign : Variable t -> LLValue (GetLLType t) -> CBlock rt lbl ins Undefined -> CBlock rt lbl ins Undefined
assign var reg = { ctx $= map (insert var reg), body $= (++ [(LLVM.Empty, Just $ mkSentence [prt var, "~", prt reg])]) }




infixr 7 <++, <+, <+:, <:
infixr 6 <+|, |+>, |++>, |+:>, |++:>
infixr 5 +|, ++|

export
(++) : CBlock rt lbl ins Undefined -> CBlock rt lbl Undefined outs -> CBlock rt lbl ins outs
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
(<++) : CBlock rt lbl ins Undefined -> List STInstr -> CBlock rt lbl ins Undefined
(MkBB { theLabel, phis , body , term = (), ctx }) <++ instrs
  = MkBB { theLabel, phis, body = (body ++ map noComment instrs), term = (), ctx}

export
(<+) : CBlock rt lbl ins Undefined -> STInstr -> CBlock rt lbl ins Undefined
blk <+ instr = blk <++ [instr]

export
(<+:) : CBlock rt lbl ins Undefined -> (STInstr, Maybe String) -> CBlock rt lbl ins Undefined
(MkBB { theLabel, phis , body , term = (), ctx }) <+: instr
  = MkBB { theLabel, phis, body = (body ++ [instr]), term = (), ctx}

export
(<:) : CBlock rt lbl ins Undefined -> String -> CBlock rt lbl ins Undefined
blk <: cmt = blk <+: (Empty, Just cmt)

export
(<+|) : CBlock rt lbl ins Undefined -> CFInstr rt (toCFK outs) -> CBlock rt lbl ins (Just outs)
MkBB { theLabel, phis, body, term = (), ctx } <+| term = MkBB { theLabel, phis, body, term, ctx }

export
(|++:>) : List (PhiInstr inputs, Maybe String)
       -> CBlock rt lbl Undefined outs
       -> CBlock rt lbl (Just inputs) outs
phis |++:> MkBB { theLabel, phis = (), body, term, ctx } = MkBB { theLabel, phis, body, term, ctx }

export
(|+:>) : (PhiInstr inputs, Maybe String)
      -> CBlock rt lbl Undefined outs
      -> CBlock rt lbl (Just inputs) outs
instr |+:> blk = [instr] |++:> blk

export
(|++>) : List (PhiInstr inputs)
      -> CBlock rt lbl Undefined outs
      -> CBlock rt lbl (Just inputs) outs
phis |++> blk = (map noComment phis) |++:> blk

export
(|+>) : PhiInstr inputs
     -> CBlock rt lbl Undefined outs
     -> CBlock rt lbl (Just inputs) outs
instr |+> blk = [instr] |++> blk

export
(+|) : PhiInstr inputs
    -> CBlock rt lbl (Just inputs) outs
    -> CBlock rt lbl (Just inputs) outs
instr +| MkBB { theLabel, phis, body, term, ctx } = MkBB { theLabel, phis = ((instr, Nothing) :: phis), body, term, ctx }

export
(++|) : List (PhiInstr inputs)
     -> CBlock rt lbl (Just inputs) outs
     -> CBlock rt lbl (Just inputs) outs
phis ++| blk = foldl (flip (+|)) blk phis


export
implementation Connectable (CBlock rt) where
  cnct = (++)



-- TODO: consider hiding the attachment somewhere, eg. in the `CBlock` itself
export
getContext : {lbl : BlockLabel}
          -> CFG (CBlock rt) ins (Undefined lbl)
          -> lbl :~: VarCTX
getContext {lbl} cfg = oget ctx cfg

export
getContexts : CFG (CBlock rt) ins (Defined outs)
           -> DList (:~: VarCTX) outs
getContexts cfg = oget' contexts cfg



export
emptyCFG : {lbl : BlockLabel} -> lbl :~: VarCTX -> CFG (CBlock rt) (Undefined lbl) (Undefined lbl)
emptyCFG = initGraph . emptyCBlock
