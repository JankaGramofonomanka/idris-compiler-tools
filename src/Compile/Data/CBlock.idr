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
import Compile.Utils
import CFG

import Utils

-- TODO: `MbPhis Undefined = List [t ** Variable t]` - list of variables that need a phi assignment

public export
MbPhis : (LLType -> Type) -> Neighbors BlockLabel -> Type
MbPhis var Nothing = ()
MbPhis var (Just ins) = List (PhiInstr var (MkInputs ins), Maybe String)


public export
toCFK : List BlockLabel -> CFKind
toCFK [] = Return
toCFK (lbl :: lbls) = Jump (lbl :: lbls)

public export
fromCFK : CFKind -> List BlockLabel
fromCFK Return = []
fromCFK (Jump lbls) = lbls

public export
MbTerm : (LLType -> Type) -> LLType -> Neighbors BlockLabel -> Type
MbTerm var rt Nothing = ()
MbTerm var rt (Just outs) = CFInstr var rt (toCFK outs)

public export
record CBlock' (var : LLType -> Type)
               (retT : LLType)
               (label : BlockLabel)
               (ins : Neighbors BlockLabel)
               (outs : Neighbors BlockLabel)
  where
    constructor MkBB
    theLabel : The label

    phis : MbPhis var ins
    body : List (STInstr var, Maybe String)
    term : MbTerm var retT outs

noComment : instr -> (instr, Maybe String)
noComment instr = (instr, Nothing)

export
emptyCBlock : {lbl : BlockLabel} -> CBlock' var rt lbl Undefined Undefined
emptyCBlock {lbl} = MkBB { theLabel = MkThe lbl, phis = (), body = [], term = ()}



infixr 7 <++, <+, <+:, <:
infixr 6 <+|, |+>, |++>, |+:>, |++:>
infixr 5 +|, ++|

export
(++) : CBlock' var rt lbl ins Undefined -> CBlock' var rt lbl Undefined outs -> CBlock' var rt lbl ins outs
(++) 
  ( MkBB { theLabel,             phis,      body,                   term = ()    } )
  ( MkBB { theLabel = theLabel', phis = (), body = body',           term = term' } )
  = MkBB { theLabel,             phis,      body = (body ++ body'), term = term' }

export
(<++) : CBlock' var rt lbl ins Undefined -> List (STInstr var) -> CBlock' var rt lbl ins Undefined
(MkBB { theLabel, phis , body , term = () }) <++ instrs
  = MkBB { theLabel, phis, body = (body ++ map noComment instrs), term = () }

export
(<+) : CBlock' var rt lbl ins Undefined -> STInstr var -> CBlock' var rt lbl ins Undefined
blk <+ instr = blk <++ [instr]

export
(<+:) : CBlock' var rt lbl ins Undefined -> (STInstr var, Maybe String) -> CBlock' var rt lbl ins Undefined
(MkBB { theLabel, phis, body, term = () }) <+: instr
  = MkBB { theLabel, phis, body = (body ++ [instr]), term = () }
export
(<:) : CBlock' var rt lbl ins Undefined -> String -> CBlock' var rt lbl ins Undefined
blk <: cmt = blk <+: (Empty, Just cmt)

export
(<+|) : CBlock' var rt lbl ins Undefined -> CFInstr var rt (toCFK outs) -> CBlock' var rt lbl ins (Just outs)
MkBB { theLabel, phis, body, term = () } <+| term = MkBB { theLabel, phis, body, term }

export
(|++:>) : List (PhiInstr var (MkInputs inputs), Maybe String)
       -> CBlock' var rt lbl Undefined outs
       -> CBlock' var rt lbl (Just inputs) outs
phis |++:> MkBB { theLabel, phis = (), body, term } = MkBB { theLabel, phis, body, term }

export
(|+:>) : (PhiInstr var (MkInputs inputs), Maybe String)
      -> CBlock' var rt lbl Undefined outs
      -> CBlock' var rt lbl (Just inputs) outs
instr |+:> blk = [instr] |++:> blk

export
(|++>) : List (PhiInstr var (MkInputs inputs))
      -> CBlock' var rt lbl Undefined outs
      -> CBlock' var rt lbl (Just inputs) outs
phis |++> blk = (map noComment phis) |++:> blk

export
(|+>) : PhiInstr var (MkInputs inputs)
     -> CBlock' var rt lbl Undefined outs
     -> CBlock' var rt lbl (Just inputs) outs
instr |+> blk = [instr] |++> blk

export
(+|) : PhiInstr var (MkInputs inputs)
    -> CBlock' var rt lbl (Just inputs) outs
    -> CBlock' var rt lbl (Just inputs) outs
instr +| MkBB { theLabel, phis, body, term }
  = MkBB { theLabel, phis = ((instr, Nothing) :: phis), body, term }

export
(++|) : List (PhiInstr var (MkInputs inputs))
     -> CBlock' var rt lbl (Just inputs) outs
     -> CBlock' var rt lbl (Just inputs) outs
phis ++| blk = foldl (flip (+|)) blk phis


export
implementation Connectable (CBlock' var rt) where
  cnct = (++)



export
emptyCFG : {lbl : BlockLabel} -> CFG (CBlock' var rt) (Undefined lbl) (Undefined lbl)
emptyCFG = initGraph emptyCBlock
