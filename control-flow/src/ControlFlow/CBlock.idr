module ControlFlow.CBlock

import Data.Singleton

import ControlFlow.CFG

||| Constructs the type of the phi assignment list of a `CBlock` based on its
||| predecessors (`ins`).
|||
||| * For an undefined list of predecessors (`Nothing`), the "list" is of the
||| unit type, as the phi assignments are impossible to construct in such case.
|||
||| * For a defined list of predecessors (`Just ins`), the list is an actual
||| list of phi assignemtns, whose "inputs" coincide with the inputs
||| (predecessors) of the block.
|||
||| @ lbl the type of vertex identifiers / block labels
||| @ phi the type that represents a phi assignment,
|||       parametrized by its input labels
||| @ ins the predecessors of the block
public export
MbPhis : (phi : List lbl -> Type) -> (ins : Neighbors lbl) -> Type
MbPhis phi Nothing = ()
MbPhis phi (Just ins) = List (phi ins)

||| Constructs the type of the terminating instruction of a `CBlock` based on
||| its successors (`outs`)
|||
||| * For an undefined list of successors (`Nothing`), the terminator is of the
||| unit type, as it is impossible to determine its type in such case.
|||
||| * For a defined list of successors (`Just outs`), the terminator an a ctual
||| terminating instruction, whose "outputs" concide with the
||| outputs (successors) of the block.
|||
||| @ lbl the type of vertex identifiers / block labels
||| @ term the type that represents the terminating instruction,
|||        parametrized by its output labels
||| @ outs the succcessors of the block
public export
MbTerm : (term : List lbl -> Type) -> (outs : Neighbors lbl) -> Type
MbTerm term Nothing = ()
MbTerm term (Just outs) = term outs

||| A potentially incomplete basic block.
|||
||| @ l     the type of vertex identifiers / block labels
||| @ phi   the type that represents a phi assignment,
|||         parametrized by its input labels
||| @ instr the type that represents the simple (non-terminating,
|||         non-phi-assignments)) instructions that the block consists of
||| @ term  the type that represents the terminating instruction,
|||         parametrized by its output labels
||| @ lbl   the label of the block (its identifier)
||| @ ins   the potentially undefined list of the predecessors of the block
||| @ outs  the potentially undefined list of the successors of the block
public export
record CBlock
  (phi        : List l -> Type)
  (instr      : Type)
  (terminator : List l -> Type)
  (lbl        : l)
  (ins        : Neighbors l)
  (outs       : Neighbors l)
  where

  ||| Make a potentially incomplete basic block
  constructor MkBB

  ||| the runtime manifestation of the label (the identifier) of the block.
  |||
  ||| Wrapped in the `Singleton` type constructor to avoid shadowing the type
  ||| parameter by the field or vice versa.
  theLabel : Singleton lbl

  ||| The potentially undefined list of phi assignments of the block
  phis : MbPhis phi ins

  ||| The body of the block, i.e. the instructions it consists of.
  body : List instr

  ||| The potentially undefined instruction that terminates the block
  term : MbTerm terminator outs

-- TODO why implicit?
||| Create `CBlock` that has no instructions
||| @ lbl the block label
export
emptyCBlock : {lbl : l} -> CBlock phi instr trm lbl Nothing Nothing
emptyCBlock {lbl} = MkBB { theLabel = Val lbl, phis = (), body = [], term = () }




export infixr 7 <++, <+
export infixr 6 <+|, |+>, |++>
export infixr 5 +|, ++|

||| Concatenates two blocks
||| Appends a postfix with undefine inputs to a prefix with undefined outputs.
||| @ pre  the prefix
||| @ post the postfix
export
(++)
   : (pre  : CBlock phi instr terminator lbl ins     Nothing)
  -> (post : CBlock phi instr terminator lbl Nothing outs)
  ->         CBlock phi instr terminator lbl ins     outs
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

||| Append a list of simple instructions to the block
||| Leaves the type signature of the block unchanged
||| @ pre  the block        (the prefix)
||| @ post the instructions (the postfix)
export
(<++)
   : (pre  : CBlock phi instr trm lbl ins Nothing)
  -> (post : List instr)
  ->         CBlock phi instr trm lbl ins Nothing
(MkBB { theLabel, phis , body , term = () }) <++ instrs
  = MkBB { theLabel, phis, body = (body ++ instrs), term = () }

||| Append a single simple instruction to the block
||| Leaves the type signature of the block unchanged
||| @ pre  the block       (the prefix)
||| @ post the instruction (the postfix)
export
(<+)
   : (pre  : CBlock phi instr trm lbl ins Nothing)
  -> (post : instr)
  ->         CBlock phi instr trm lbl ins Nothing
blk <+ instr = blk <++ [instr]

||| Defines the outputs of a block by appending to it a terminating
||| insrtruction
||| @ pre  the block      (the prefix)
||| @ post the terminator (the postfix)
export
(<+|)
   : (pre  : CBlock phi instr trm lbl ins Nothing)
  -> (post : trm                                outs)
  ->         CBlock phi instr trm lbl ins (Just outs)
MkBB { theLabel, phis, body, term = () } <+| term = MkBB { theLabel, phis, body, term }

||| Defines the inputs of a block by prepending to it a list of phi assignemts
||| @ pre  the phi assignments (the prefix)
||| @ post the block           (the postfix)
export
(|++>)
   : (pre  : List (phi                      inputs))
  -> (post : CBlock phi instr trm lbl Nothing       outs)
  ->         CBlock phi instr trm lbl (Just inputs) outs
phis |++> MkBB { theLabel, phis = (), body, term }
        = MkBB { theLabel, phis,      body, term }

||| Defines the inputs of a block by prepending to it a single phi assignemt
||| @ pre  the phi assignment (the prefix)
||| @ post the block          (the postfix)
export
(|+>)
   : (pre  : phi                            inputs)
  -> (post : CBlock phi instr trm lbl Nothing       outs)
  ->         CBlock phi instr trm lbl (Just inputs) outs
instr |+> blk = [instr] |++> blk

||| Prepends a phi assignment to a block with already defined inputs
||| @ pre  the phi assignment (the prefix)
||| @ post the block          (the postfix)
export
(+|)
   : (pre  : phi                            inputs)
  -> (post : CBlock phi instr trm lbl (Just inputs) outs)
  ->         CBlock phi instr trm lbl (Just inputs) outs
instr +| MkBB { theLabel, phis, body, term }
  = MkBB { theLabel, phis = instr :: phis, body, term }

||| Prepends a list of phi assignments to a block with already defined inputs
||| @ pre  the phi assignments (the prefix)
||| @ post the block           (the postfix)
export
(++|)
   : (pre  : List (phi                      inputs))
  -> (post : CBlock phi instr trm lbl (Just inputs) outs)
  ->         CBlock phi instr trm lbl (Just inputs) outs
phis ++| blk = foldl (flip (+|)) blk phis

export
implementation Connectable (CBlock phi instr terminator) where
  cnct = (++)

-- TODO why implicit?
||| Make a graph that consists of a single empty block
||| @ lbl the label of the block
export
emptyCFG : {lbl : l} -> CFG (CBlock phi instr terminatorrt) (Undefined lbl) (Undefined lbl)
emptyCFG = initGraph emptyCBlock
