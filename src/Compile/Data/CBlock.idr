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
MbPhis : Neighbors Label -> Type
MbPhis Nothing = ()
MbPhis (Just ins) = List (PhiInstr ins, Maybe String)


public export
MbTerm : LLType -> Neighbors Label -> Type
MbTerm rt Nothing = ()
MbTerm rt (Just outs) = CFInstr rt outs

public export
record CBlock (retT : LLType) (label : Label) (ins : Neighbors Label) (outs : Neighbors Label) where
  constructor MkBB
  theLabel : The label

  phis : MbPhis ins
  body : List (STInstr, Maybe String)
  term : MbTerm retT outs

noComment : instr -> (instr, Maybe String)
noComment instr = (instr, Nothing)

-- TODO why implicit?
export
emptyCBlock : {lbl : Label} -> CBlock rt lbl Undefined Undefined
emptyCBlock {lbl} = MkBB { theLabel = MkThe lbl, phis = (), body = [], term = () }





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
    }
  )
  ( MkBB
    { theLabel = theLabel'
    , phis = ()
    , body = body'
    , term = term'
    }
  )
  = MkBB
    { theLabel
    , phis
    , body = (body ++ body')
    , term = term'
    }

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
(<+|) : CBlock rt lbl ins Undefined -> CFInstr rt outs -> CBlock rt lbl ins (Just outs)
MkBB { theLabel, phis, body, term = () } <+| term = MkBB { theLabel, phis, body, term }

export
(|++:>) : List (PhiInstr inputs, Maybe String)
       -> CBlock rt lbl Undefined outs
       -> CBlock rt lbl (Just inputs) outs
phis |++:> MkBB { theLabel, phis = (), body, term } = MkBB { theLabel, phis, body, term }

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
instr +| MkBB { theLabel, phis, body, term } = MkBB { theLabel, phis = ((instr, Nothing) :: phis), body, term }

export
(++|) : List (PhiInstr inputs)
     -> CBlock rt lbl (Just inputs) outs
     -> CBlock rt lbl (Just inputs) outs
phis ++| blk = foldl (flip (+|)) blk phis


export
implementation Connectable (CBlock rt) where
  cnct = (++)



-- TODO why implicit?
export
emptyCFG : {lbl : Label} -> CFG (CBlock rt) (Undefined lbl) (Undefined lbl)
emptyCFG = initGraph emptyCBlock
