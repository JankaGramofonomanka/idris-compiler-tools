module Compile.Utils

import CFG

import Data.DList
import Data.Attached
import Data.The
import Data.Typed

import LNG.TypeChecked
import LLVM

import Theory

public export
GetLLType : LNGType -> LLType
GetLLType TInt    = I32
GetLLType TBool   = I1
GetLLType TString = Ptr I8
GetLLType TVoid   = Void

public export
FunVal : LNGType -> List LNGType -> Type
FunVal t ts = LLFun (GetLLType t) (map GetLLType ts)

public export
FunVal' : (LNGType, List LNGType) -> Type
FunVal' (t, ts) = FunVal t ts



export
addInput : (lbl : Label)
        -> LLValue t
        -> PhiExpr ins t
        -> PhiExpr (lbl :: ins) t

addInput lbl val (Phi t kvs) = Phi t $ (lbl, val) :: kvs


export
concatPhi : PhiExpr lbls t -> PhiExpr lbls' t -> PhiExpr (lbls ++ lbls') t
concatPhi (Phi t l) (Phi _ l') = rewrite revEq $ List.map_concat {f = fst} l l'
                                 in Phi t (l ++ l')

export
phiFromDList : The t
            -> (lbls : List Label)
            -> DList (:~: (LLValue t)) (lbls ~~> lbl)
            -> PhiExpr lbls t

phiFromDList (MkThe t) Nil Nil = Phi t Nil
phiFromDList theT (lbl :: lbls) (val :: vals)
= addInput lbl (detach val) (phiFromDList theT lbls vals)


export
replicatePhi : (ins : List Label) -> LLValue t -> PhiExpr ins t
replicatePhi {t} Nil val = case the (The t) (typeOf val) of { MkThe t' => Phi t' Nil }
replicatePhi (lbl :: lbls) val = addInput lbl val $ replicatePhi lbls val


