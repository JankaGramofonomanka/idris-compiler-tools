module LLVM.Construction

import Data.List
import Data.So

import Data.DList
import Data.Some
import LLVM
import FEq
import Utils


StartType : InputKind -> Type
StartType Entry = ()
StartType NonEntry = List (Some Reg)


-- a simple block before the addition of phi assignments
public export
record SimpleBlock
  (inputKind : InputKind)
  (label : BlockLabel inputKind)
  (cfkind : CFKind)
where
  constructor MkSimpleBlock
  
  -- a list of registers that inherit values from incoming blocks,
  -- ie. ones that need a phi assignment
  --start   : (ts : List LLType ** DList Reg ts)
  --start   : List (Some Reg)
  phis   : StartType inputKind
  
  body  : List (STInstr)
  term  : CFInstr cfkind



--data NotAVertexOf : BlockLabel k -> JumpGraph -> Type where
--  NAVNil : l `NotAVertexOf` Nil
--  NAVConsE : LEntry `NotAVertexOf` g -> LEntry `NotAVertexOf` ((MkSome $ LName s, l') :: g) 
--  NAVConsNE : So (s /= s') -> l `NotAVertexOf` g -> (LName s) `NotAVertexOf` ((MkSome $ LName s', l') :: g)


updateTBD : (label : BlockLabel kind)
         -> (cfkind : CFKind)
         -> (defined : List $ Some BlockLabel)
         -> (toBeDefined : List $ Some BlockLabel)
         -> List $ Some BlockLabel
updateTBD label Return defined toBeDefined = deleteAll (MkSome label) toBeDefined
updateTBD label (Jump labels) defined toBeDefined = let

  newLabels : List (Some BlockLabel)
  newLabels = filter (not . (\l => not $ l `elem` defined)) $ map MkSome labels

  in deleteAll (MkSome label) (newLabels ++ toBeDefined)



{-
  An intermediate control flow graph. It's purpose is to build it from blocks 
  that do not yet contain 'phi' assignments, and then based on the final graph
  determine the structure of it (a `JumpGraph`) and convert it to `LLVM.CFG` by
  adding phi assignments to blocks.
  
  Parametrs:
  * `defined` - a list of block labels that are alredy defined
  * `toBeDefined` - a list of block labels, that are not yet defined, but
    should be, based on the jump instructions that are alredy in the graph.
-}
public export
data CFG : (defined : List $ Some BlockLabel)
        -> (toBeDefined : List $ Some BlockLabel)
        -> Type where
  
  Empty : CFG [] []

  -- TODO: Enforce uniqueness of blocks
  AddBlock : SimpleBlock inputKind label cfkind
          -> CFG defined toBeDefined
          -> CFG (MkSome label :: defined) (updateTBD label cfkind defined toBeDefined)


updateGraph : BlockLabel kind -> CFKind -> JumpGraph -> JumpGraph
updateGraph label Return g = g
updateGraph label (Jump labels) g = map (\l => (MkSome label, l)) labels ++ g

-- TODO: `toBeDefined` should be `[]` but the type checker cannot unify `[]`
-- with `updateTBD ...`, this is worrysome.
0 getJumpGraph : Construction.CFG defined toBeDefined -> JumpGraph
getJumpGraph Empty = []
getJumpGraph (AddBlock block cfg {label} {cfkind}) = updateGraph label cfkind $ getJumpGraph cfg


