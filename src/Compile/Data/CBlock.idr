module Compile.Data.CBlock

import Data.Attached
import Data.Doc
import Data.DList
import Data.GCompare
import Data.The

import LLVM.Generalized as LLVM.G
import LLVM.Render
import LNG.TypeChecked
import LNG.TypeChecked.Render

import Compile.Data.LLVM
import Compile.Utils
import CFG

import Utils

-- TODO: `MbPhis Undefined = List [t ** Variable t]` - list of variables that need a phi assignment

public export
MbPhis : Neighbors BlockLabel -> Type
MbPhis Nothing = ()
MbPhis (Just ins) = List (PhiInstr $ MkInputs ins, Maybe String)


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

noComment : instr -> (instr, Maybe String)
noComment instr = (instr, Nothing)

export
emptyCBlock : {lbl : BlockLabel} -> CBlock rt lbl Undefined Undefined
emptyCBlock {lbl} = MkBB { theLabel = MkThe lbl, phis = (), body = [], term = ()}



infixr 7 <++, <+, <+:, <:
infixr 6 <+|, |+>, |++>, |+:>, |++:>
infixr 5 +|, ++|

export
(++) : CBlock rt lbl ins Undefined -> CBlock rt lbl Undefined outs -> CBlock rt lbl ins outs
(++) 
  ( MkBB { theLabel,             phis,      body,                   term = ()    } )
  ( MkBB { theLabel = theLabel', phis = (), body = body',           term = term' } )
  = MkBB { theLabel,             phis,      body = (body ++ body'), term = term' }

export
(<++) : CBlock rt lbl ins Undefined -> List STInstr -> CBlock rt lbl ins Undefined
(MkBB { theLabel, phis , body , term = () }) <++ instrs
  = MkBB { theLabel, phis, body = (body ++ map noComment instrs), term = () }

export
(<+) : CBlock rt lbl ins Undefined -> STInstr -> CBlock rt lbl ins Undefined
blk <+ instr = blk <++ [instr]

export
(<+:) : CBlock rt lbl ins Undefined -> (STInstr, Maybe String) -> CBlock rt lbl ins Undefined
(MkBB { theLabel, phis , body , term = () }) <+: instr
  = MkBB { theLabel, phis, body = (body ++ [instr]), term = () }
export
(<:) : CBlock rt lbl ins Undefined -> String -> CBlock rt lbl ins Undefined
blk <: cmt = blk <+: (Empty, Just cmt)

export
(<+|) : CBlock rt lbl ins Undefined -> CFInstr rt (toCFK outs) -> CBlock rt lbl ins (Just outs)
MkBB { theLabel, phis, body, term = () } <+| term = MkBB { theLabel, phis, body, term }

export
(|++:>) : List (PhiInstr (MkInputs inputs), Maybe String)
       -> CBlock rt lbl Undefined outs
       -> CBlock rt lbl (Just inputs) outs
phis |++:> MkBB { theLabel, phis = (), body, term } = MkBB { theLabel, phis, body, term }

export
(|+:>) : (PhiInstr (MkInputs inputs), Maybe String)
      -> CBlock rt lbl Undefined outs
      -> CBlock rt lbl (Just inputs) outs
instr |+:> blk = [instr] |++:> blk

export
(|++>) : List (PhiInstr (MkInputs inputs))
      -> CBlock rt lbl Undefined outs
      -> CBlock rt lbl (Just inputs) outs
phis |++> blk = (map noComment phis) |++:> blk

export
(|+>) : PhiInstr (MkInputs inputs)
     -> CBlock rt lbl Undefined outs
     -> CBlock rt lbl (Just inputs) outs
instr |+> blk = [instr] |++> blk

export
(+|) : PhiInstr (MkInputs inputs)
    -> CBlock rt lbl (Just inputs) outs
    -> CBlock rt lbl (Just inputs) outs
instr +| MkBB { theLabel, phis, body, term }
  = MkBB { theLabel, phis = ((instr, Nothing) :: phis), body, term }

export
(++|) : List (PhiInstr (MkInputs inputs))
     -> CBlock rt lbl (Just inputs) outs
     -> CBlock rt lbl (Just inputs) outs
phis ++| blk = foldl (flip (+|)) blk phis


export
implementation Connectable (CBlock rt) where
  cnct = (++)



export
emptyCFG : {lbl : BlockLabel} -> CFG (CBlock rt) (Undefined lbl) (Undefined lbl)
emptyCFG = initGraph emptyCBlock
