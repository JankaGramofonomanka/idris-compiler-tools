module Compile.Tools

import Control.Monad.State
import Control.Monad.Either

import Data.List

import Data.Some
import Data.DMap


import LNG
import LLVM


public export
GetLLType : LNGType -> LLType
GetLLType TInt = I32
GetLLType TBool = I1
GetLLType TVoid = Void



public export
data InStatus : Type where
  InOpen : InStatus
  InClosed : (ik : InputKind)
          -> (label : BlockLabel ik)
          -> (inputs : Inputs ik)
          -> InStatus

public export
data OutStatus = OutOpen | OutClosed CFKind

-- TODO: `MbPhis InOpen = List [t ** Variable t]` - list of variables that need a phi assignment

public export
MbPhis : InStatus -> Type
MbPhis InOpen = ()
MbPhis (InClosed ik label inputs) = List (PhiInstr inputs)


public export
MbTerm : OutStatus -> Type
MbTerm OutOpen = ()
MbTerm (OutClosed cfk) = CFInstr cfk

public export
record CBlock (is : InStatus) (os : OutStatus) where
  constructor MkBB
  phis : MbPhis is
  body : List STInstr
  term : MbTerm os
  
  -- TODO: divide assignments between individual instructions
  ctx : DMap Variable (LLValue . GetLLType)

export
initCBlock : CBlock InOpen OutOpen
initCBlock = MkBB () [] () DMap.empty







infixr 7 <++, <+
infixr 6 <+|, |+>, |++>
infixr 5 +|, ++|

export
(++) : CBlock is OutOpen -> CBlock InOpen os -> CBlock is os
MkBB phis body () m ++ MkBB () body' term' m' = MkBB phis (body ++ body') term' (DMap.merge m m')

export
(<++) : CBlock is OutOpen -> List STInstr -> CBlock is OutOpen
MkBB phis body () m <++ instrs = MkBB phis (body ++ instrs) () m

export
(<+) : CBlock is OutOpen -> STInstr -> CBlock is OutOpen
blk <+ instr = blk <++ [instr]

export
(<+|) : CBlock is OutOpen -> CFInstr cfk -> CBlock is (OutClosed cfk)
MkBB phis body () m <+| instr = MkBB phis body instr m

export
(|++>) : {inputs : Inputs ik}
      -> List (PhiInstr inputs)
      -> CBlock InOpen os
      -> CBlock (InClosed ik label inputs) os
phis |++> MkBB () body term m = MkBB phis body term m

export
(|+>) : {inputs : Inputs ik}
     -> PhiInstr inputs
     -> CBlock InOpen cfk
     -> CBlock (InClosed ik label inputs) cfk
instr |+> blk = [instr] |++> blk

export
(+|) : {inputs : Inputs ik}
    -> PhiInstr inputs
    -> CBlock (InClosed ik label inputs) os
    -> CBlock (InClosed ik label inputs) os
instr +| MkBB phis body term m = MkBB (instr :: phis) body term m

export
(++|) : {inputs : Inputs ik}
     -> List (PhiInstr inputs)
     -> CBlock (InClosed ik label inputs) os
     -> CBlock (InClosed ik label inputs) os
phis ++| blk = foldl (flip (+|)) blk phis








public export
record CompState where
  constructor MkCompST

public export
data Error : Type where
  NoSuchVariable : Variable t -> Error


public export
CompM : Type -> Type
CompM = StateT CompState (Either Error)

export
assign : Variable t -> LLValue (GetLLType t) -> CBlock is OutOpen -> CBlock is OutOpen
assign var reg (MkBB phis body term ctx) = MkBB phis body term $ insert var reg ctx

export
freshReg : CompM (Reg t)

export
freshLabel : CompM (BlockLabel NonEntry)

export
addBlock : CBlock (InClosed ik label inputs) (OutClosed cfk) -> CompM ()







public export
data OutStatus' = Open | Closed

public export
OpenOr : OutStatus' -> Lazy OutStatus' -> OutStatus'
OpenOr l r = case l of
  Open => Open
  Closed => r

public export
ClosedOr : OutStatus' -> Lazy OutStatus' -> OutStatus'
ClosedOr l r = case l of
  Closed => Closed
  Open => r




  
public export
data CompileResult : OutStatus' -> Type where
  SingleBLKC : (cfk ** CBlock InOpen (OutClosed cfk)) -> CompileResult Closed
  SingleBLKO : CBlock InOpen OutOpen -> CompileResult Open
  DoubleBLK : (cfk ** CBlock InOpen (OutClosed cfk))
           -> (ik ** label ** inputs ** CBlock (InClosed ik label inputs) OutOpen)
           -> CompileResult Open

export
initCR : CompileResult Open
initCR = SingleBLKO initCBlock



export
mapOO : ({is : InStatus} -> CBlock is OutOpen -> CBlock is OutOpen) -> CompileResult Open -> CompileResult Open
mapOO f (SingleBLKO blk) = SingleBLKO (f blk)
mapOO f (DoubleBLK blkIn (ik ** lbl ** ins ** blkOut))
  = DoubleBLK blkIn (ik ** lbl ** ins ** f blkOut)

export
closeCR : {cfk : CFKind} -> CFInstr cfk -> CompileResult Open -> CompM (CompileResult Closed)
closeCR {cfk} instr (SingleBLKO blk) = pure $ SingleBLKC (cfk ** blk <+| instr)
closeCR {cfk} instr (DoubleBLK blkIn (ik ** label ** inputs ** blkOut)) = do
  addBlock $ blkOut <+| instr
  pure $ SingleBLKC blkIn



export
combineCR : CompileResult Open -> CompileResult os -> CompM (CompileResult os)

combineCR (SingleBLKO blk) (SingleBLKC (cfk ** blk'))         = pure $ SingleBLKC (cfk ** blk ++ blk')
combineCR (SingleBLKO blk) (SingleBLKO blk')                  = pure $ SingleBLKO (blk ++ blk')
combineCR (SingleBLKO blk) (DoubleBLK (cfk ** blkIn) blkOut)  = pure $ DoubleBLK (cfk ** blk ++ blkIn) blkOut

combineCR (DoubleBLK blkIn (ik ** lbl ** ins ** blkOut)) (SingleBLKC (cfk ** blk)) = do
  addBlock $ blkOut ++ blk
  pure $ SingleBLKC blkIn

combineCR (DoubleBLK blkIn (ik ** lbl ** ins ** blkOut)) (SingleBLKO blk) = do
  pure $ DoubleBLK blkIn (ik ** lbl ** ins ** blkOut ++ blk)

combineCR (DoubleBLK blkIn (ik ** lbl ** ins ** blkOut)) (DoubleBLK (cfk ** blkIn') blkOut') = do
  addBlock $ blkOut ++ blkIn'
  pure $ DoubleBLK blkIn blkOut'






public export
data LabelResult : OutStatus' -> Type where
  NoLabel : LabelResult Closed
  LastLabel : Some BlockLabel -> LabelResult Open

public export
listify : LabelResult os -> List (Some BlockLabel)  
listify NoLabel = []
listify (LastLabel l) = [l]





  
