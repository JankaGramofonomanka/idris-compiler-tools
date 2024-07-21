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

||| Constructs the type of the phi assignment list of a `CBlock` based on its
||| predecessors (`ins`).
|||
||| * For an undefined list of predecessors (`Nothing`), the "list" is of the
||| unit type, as the phi assignments are impossible to construct in such case.
|||
||| * For a defined list of predecessors (`Just ins`), the list is an a ctual
||| list of phi assignemtns, whose "inputs" concide with the inputs
||| (predecessors) of the block.
||| Each assignment comes with an optional comment.
|||
||| @ ins the predecessors of the block
public export
MbPhis : (ins : Neighbors Label) -> Type
MbPhis Nothing = ()
MbPhis (Just ins) = List (PhiInstr ins, Maybe String)

||| Constructs the type of the terminating instruction of a `CBlock` based on
||| its successors (`outs`)
|||
||| * For an undefined list of successors (`Nothing`), the terminator is of the
||| unit type, as it is impossible to determine its type in such case.
|||
||| * For a defined list of successors (`Just outs`), the terminator an a ctual
||| "control-flow" instruction, whose "outputs" concide with the
||| outputs (successors) of the block.
|||
||| @ rt   the return type of the function, whose body the block is part of
||| @ outs the succcessors of the block
public export
MbTerm : (rt : LLType) -> (outs : Neighbors Label) -> Type
MbTerm rt Nothing = ()
MbTerm rt (Just outs) = CFInstr rt outs

||| A potentially incomplete basic block.
|||
||| @ rt   the return type of the function, whose body the block is part of,
|||        used to enforce the correct types of returned values.
||| @ lbl  the label of the block (its identifier)
||| @ ins  the potentially undefined list of the predecessors of the block
||| @ outs the potentially undefined list of the successors of the block
public export
record CBlock
  (rt   : LLType)
  (lbl  : Label)
  (ins  : Neighbors Label)
  (outs : Neighbors Label)
  where

  ||| Make a potentially incomplete basic block
  constructor MkBB

  ||| the runtime manifestation of the label (the identifier) of the block.
  |||
  ||| Wrapped in the `The` type constructor to avoid shadowing the type
  ||| parameter by the field or vice versa.
  theLabel : The lbl

  ||| The potentially undefined list of phi assignments of the block
  phis : MbPhis ins

  ||| The body of the block, i.e. the instructions it consists of.
  ||| Each instruction comes with an optional comment.
  body : List (STInstr, Maybe String)

  ||| The potentially undefined instruction that terminates the block
  term : MbTerm rt outs

  -- TODO: divide assignments between individual instructions
  ||| The context (a mapping of variables of the ciompiled language to values
  ||| of the target language) as it is after executing the instructions in the
  ||| block
  ctx : lbl :~: VarCTX

||| Make an instruction without any comment attached to it
noComment : instr -> (instr, Maybe String)
noComment instr = (instr, Nothing)

||| For each output edge of the block, makes a copy of the context stored in
||| the block, attached to that edge.
|||
||| @ lbl  the block label
||| @ outs the (defined) list of the successors of the block
||| @ blk  the block
export
contexts : {0 lbl : Label}
        -> {outs : List Label}
        -> (blk : CBlock rt lbl ins (Just outs))
        -> DList (:~: VarCTX) (lbl ~>> outs)
contexts {lbl, outs} blk = replicate' lblTo outs (\l => attach (lblTo l) (detach $ blk.ctx)) where
  0 lblTo : Label -> Edge Label
  lblTo v = lbl ~> v

||| Create `CBlock` that has no instructions
||| @ lbl the block label
||| @ ctx the context at the beginnign of the block
export
emptyCBlock : {lbl : Label} -> (ctx : lbl :~: VarCTX) -> CBlock rt lbl Undefined Undefined
emptyCBlock {lbl} ctx = MkBB { theLabel = MkThe lbl, phis = (), body = [], term = (), ctx}

||| Modifies the context stored in the block, so that the given value is
||| assigned to the gioven variable.
||| Adds an empty instruction with a comment marking the assignment
||| @ var the variable
||| @ val the value
||| @ blk the block
export
assign
   : (var : Variable t)
  -> (val : LLValue (GetLLType t))
  -> (blk : CBlock rt lbl ins Undefined)
  ->        CBlock rt lbl ins Undefined
assign var reg
  = { ctx  $= map (insert var reg)
    , body $= (++ [(LLVM.Empty, Just $ mkSentence [prt var, "~", prt reg])])
    }

infixr 7 <++, <+, <+:, <:
infixr 6 <+|, |+>, |++>, |+:>, |++:>
infixr 5 +|, ++|

||| Concatenates two blocks
||| Appends a postfix with undefine inputs to a prefix with undefined outputs.
||| @ pre  the prefix
||| @ post the postfix
export
(++)
   : (pre  : CBlock rt lbl ins Undefined)
  -> (post : CBlock rt lbl Undefined outs)
  ->         CBlock rt lbl ins       outs
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

||| Append a list of simple instructions to the block
||| Leaves the type signature of the block unchanged
||| @ pre  the block        (the prefix)
||| @ post the instructions (the postfix)
export
(<++)
   : (pre  : CBlock rt lbl ins Undefined)
  -> (post : List STInstr)
  ->         CBlock rt lbl ins Undefined
(MkBB { theLabel, phis , body , term = (), ctx }) <++ instrs
  = MkBB { theLabel, phis, body = (body ++ map noComment instrs), term = (), ctx}

||| Append a single simple instruction to the block
||| Leaves the type signature of the block unchanged
||| @ pre  the block       (the prefix)
||| @ post the instruction (the postfix)
export
(<+)
   : (pre  : CBlock rt lbl ins Undefined)
  -> (post : STInstr)
  ->         CBlock rt lbl ins Undefined
blk <+ instr = blk <++ [instr]

||| Appends a single simple instruction with a comment to a block
||| Leaves the type signature of the block unchanged
||| @ pre  the block                 (the prefix)
||| @ post the commented instruction (the postfix)
export
(<+:)
   : (pre  : CBlock rt lbl ins Undefined)
  -> (post : (STInstr, Maybe String))
  ->         CBlock rt lbl ins Undefined
(MkBB { theLabel, phis , body , term = (), ctx }) <+: instr
  = MkBB { theLabel, phis, body = (body ++ [instr]), term = (), ctx}

||| Appends a single comment (an empty instruction with a comment) to a block.
||| Leaves the type signature of the block unchanged.
||| @ pre  the block   (the prefix)
||| @ post the comment (the postfix)
export
(<:)
   : (pre  : CBlock rt lbl ins Undefined)
  -> (post : String)
  ->         CBlock rt lbl ins Undefined
blk <: cmt = blk <+: (Empty, Just cmt)

||| Defines the outputs of a block by appending to it a terminating
||| insrtruction
||| @ pre  the block      (the prefix)
||| @ post the terminator (the postfix)
export
(<+|)
   : (pre  : CBlock  rt lbl ins Undefined)
  -> (post : CFInstr rt               outs)
  ->         CBlock  rt lbl ins (Just outs)
MkBB { theLabel, phis, body, term = (), ctx } <+| term = MkBB { theLabel, phis, body, term, ctx }

||| Defines the inputs of a block by prepending to it a list of phi assignemts
||| with comments
||| @ pre  the commented phi assignments (the prefix)
||| @ post the block                     (the postfix)
export
(|++:>)
   : (pre  : List (PhiInstr      inputs, Maybe String))
  -> (post : CBlock rt lbl Undefined     outs)
  ->         CBlock rt lbl (Just inputs) outs
phis |++:> MkBB { theLabel, phis = (), body, term, ctx }
         = MkBB { theLabel, phis,      body, term, ctx }

||| Defines the inputs of a block by prepending to it a single phi assignemt
||| with a comment
||| @ pre  the commented phi assignment (the prefix)
||| @ post the block                    (the postfix)
export
(|+:>)
   : (pre  : (PhiInstr           inputs, Maybe String))
  -> (post : CBlock rt lbl Undefined     outs)
  ->         CBlock rt lbl (Just inputs) outs
instr |+:> blk = [instr] |++:> blk

||| Defines the inputs of a block by prepending to it a list of phi assignemts
||| @ pre  the phi assignments (the prefix)
||| @ post the block           (the postfix)
export
(|++>)
   : (pre  : List (PhiInstr      inputs))
  -> (post : CBlock rt lbl Undefined     outs)
  ->         CBlock rt lbl (Just inputs) outs
phis |++> blk = (map noComment phis) |++:> blk

||| Defines the inputs of a block by prepending to it a single phi assignemt
||| @ pre  the phi assignment (the prefix)
||| @ post the block          (the postfix)
export
(|+>)
   : (pre  : PhiInstr            inputs)
  -> (post : CBlock rt lbl Undefined     outs)
  ->         CBlock rt lbl (Just inputs) outs
instr |+> blk = [instr] |++> blk

||| Prepends a phi assignment to a block with already defined inputs
||| @ pre  the phi assignment (the prefix)
||| @ post the block          (the postfix)
export
(+|)
   : (pre  : PhiInstr            inputs)
  -> (post : CBlock rt lbl (Just inputs) outs)
  ->         CBlock rt lbl (Just inputs) outs
instr +| MkBB { theLabel, phis, body, term, ctx } = MkBB { theLabel, phis = ((instr, Nothing) :: phis), body, term, ctx }

||| Prepends a lsit of phi assignments to a block with already defined inputs
||| @ pre  the phi assignments (the prefix)
||| @ post the block           (the postfix)
export
(++|)
   : (pre  : List (PhiInstr inputs))
  -> (post : CBlock rt lbl (Just inputs) outs)
  ->         CBlock rt lbl (Just inputs) outs
phis ++| blk = foldl (flip (+|)) blk phis

export
implementation Connectable (CBlock rt) where
  cnct = (++)

||| Extracts the context stored in the block at the end of a graph whose
||| outputs are undefined, attached to the label label of that block
||| @ lbl the block label
||| @ cfg the block
export
getContext : {lbl : Label}
          -> (cfg : CFG (CBlock rt) ins (Undefined lbl))
          -> lbl :~: VarCTX
getContext {lbl} cfg = oget ctx cfg

||| Extracts the contexts stored in the blocks that are the sources of the
||| output edges of a graph, attached to those edges.
||| @ cfg the graph
export
getContexts : (cfg : CFG (CBlock rt) ins (Defined outs))
           -> DList (:~: VarCTX) outs
getContexts cfg = oget' contexts cfg

||| Make a graph that consists of a single empty block
||| @ lbl the label of the block
||| @ ctx the context before (and after) the block
export
emptyCFG
   : {lbl : Label}
  -> (ctx : lbl :~: VarCTX)
  -> CFG (CBlock rt) (Undefined lbl) (Undefined lbl)
emptyCFG = initGraph . emptyCBlock
