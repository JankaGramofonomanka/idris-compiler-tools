module Compile.Data.LLCBlock

import Data.Singleton

import LLVM
import public ControlFlow.CBlock
import ControlFlow.CFG

||| Given a type of things, make a type of things with a comment
||| @ t the type of things
public export
Commented : Type -> Type
Commented t = (t, Maybe String)

||| A potentially incomplete block of LLVM code
||| @ rt the return type of the function, whose body the block is part of,
|||      used to enforce the correct types of returned values.
public export
LLCBlock : LLType -> Vertex Label
LLCBlock rt = CBlock (Commented . PhiInstr) (Commented STInstr) (CFInstr rt)

||| Make an instruction without any comment attached to it
noComment : instr -> (instr, Maybe String)
noComment instr = (instr, Nothing)

export infixr 7 <++., <+., <:
export infixr 6 |+.>, |++.>
export infixr 5 +.|, ++.|

||| Append a list of simple instructions without comments to the block
||| Leaves the type signature of the block unchanged
||| @ pre  the block        (the prefix)
||| @ post the instructions (the postfix)
export
(<++.)
   : (pre  : LLCBlock rt lbl ins Nothing)
  -> (post : List STInstr)
  ->         LLCBlock rt lbl ins Nothing
blk <++. instrs = blk <++ map noComment instrs

||| Append a single simple instruction without a comment to the block
||| Leaves the type signature of the block unchanged
||| @ pre  the block       (the prefix)
||| @ post the instruction (the postfix)
export
(<+.)
   : (pre  : LLCBlock rt lbl ins Nothing)
  -> (post : STInstr)
  ->         LLCBlock rt lbl ins Nothing
blk <+. instr = blk <++. [instr]

||| Appends a single comment (an empty instruction with a comment) to a block.
||| Leaves the type signature of the block unchanged.
||| @ pre  the block   (the prefix)
||| @ post the comment (the postfix)
export
(<:)
   : (pre  : LLCBlock rt lbl ins Nothing)
  -> (post : String)
  ->         LLCBlock rt lbl ins Nothing
blk <: cmt = blk <+ (Empty, Just cmt)

||| Defines the inputs of a block by prepending to it a list of phi assignemts
||| without comments
||| @ pre  the phi assignments (the prefix)
||| @ post the block           (the postfix)
export
(|++.>)
   : (pre  : List (PhiInstr      inputs))
  -> (post : LLCBlock rt lbl Nothing       outs)
  ->         LLCBlock rt lbl (Just inputs) outs
phis |++.> blk = map noComment phis |++> blk

||| Defines the inputs of a block by prepending to it a single phi assignemt
||| without a comment
||| @ pre  the phi assignment (the prefix)
||| @ post the block          (the postfix)
export
(|+.>)
   : (pre  : PhiInstr            inputs)
  -> (post : LLCBlock rt lbl Nothing       outs)
  ->         LLCBlock rt lbl (Just inputs) outs
instr |+.> blk = [instr] |++.> blk

||| Prepends a phi assignment without a comment to a block with already defined
||| inputs
||| @ pre  the phi assignment (the prefix)
||| @ post the block          (the postfix)
export
(+.|)
   : (pre  : PhiInstr            inputs)
  -> (post : LLCBlock rt lbl (Just inputs) outs)
  ->         LLCBlock rt lbl (Just inputs) outs
instr +.| blk = (instr, Nothing) +| blk

||| Prepends a list of phi assignments without comments to a block with already
||| defined inputs
||| @ pre  the phi assignments (the prefix)
||| @ post the block           (the postfix)
export
(++.|)
   : (pre  : List (PhiInstr inputs))
  -> (post : LLCBlock rt lbl (Just inputs) outs)
  ->         LLCBlock rt lbl (Just inputs) outs
phis ++.| blk = map noComment phis ++| blk
