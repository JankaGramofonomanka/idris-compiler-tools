module Compile.Utils

import CFG

import Data.DList
import Data.Attached
import Data.The
import Data.Typed

import LNG.TypeChecked
import LLVM

import Theory

||| An LLVM representation of an LNG type
public export
GetLLType : LNGType -> LLType
GetLLType TInt    = I32
GetLLType TBool   = I1
GetLLType TString = Ptr I8
GetLLType TVoid   = Void

||| A type of LLVM function pointers representing a function of the given LNG
||| signature.
public export
FunVal : LNGType -> List LNGType -> Type
FunVal t ts = LLFun (GetLLType t) (map GetLLType ts)

||| An alias for `FunVal` (which is an alias for `LLFun` which is an alias for
||| `LLValue`) parametrized by a tuple instead of two separate parameters
public export
FunVal' : (LNGType, List LNGType) -> Type
FunVal' (t, ts) = FunVal t ts

||| Extend the inputs of a phi expression by adding a value to it
||| @ lbl the label of the extention
||| @ ins the inputs to be extended
||| @ val the value
||| @ phi the expression to be extended
export
addInput
   : (lbl : Label)
  -> (val : LLValue t)
  -> (phi : PhiExpr ins t)
  -> PhiExpr (lbl :: ins) t
addInput lbl val (Phi t kvs) = Phi t $ (lbl, val) :: kvs

||| Concatenate two phi expressions
||| A concatenation of two phi expressions with inputs `ins` and `ins'`
||| represents a value of in a block with inputs `ins ++ ins'`.
||| @ t     the type of the expressions
||| @ lhs   the left expression
||| @ rhs   the right expression
||| @ lbls  inputs of `lhs`
||| @ lbls' inputs of `rhs`
export
concatPhi
   : (lhs : PhiExpr lbls t)
  -> (rhs : PhiExpr lbls' t)
  -> PhiExpr (lbls ++ lbls') t
concatPhi (Phi t l) (Phi _ l') = rewrite revEq $ List.map_concat {f = fst} l l'
                                 in Phi t (l ++ l')

||| Create a phi expression from a dependent list of values tagged by their
||| respective input edges
||| @ t    the type of the expression
||| @ theT singleton of `t`
||| @ lbls the inputs if the phi expression
||| @ vals the list of values tagged by input edges
export
phiFromDList
   : (theT : The t)
  -> (lbls : List Label)
  -> (vals : DList (:~: (LLValue t)) (lbls ~~> lbl))
  -> PhiExpr lbls t
phiFromDList (MkThe t) Nil Nil = Phi t Nil
phiFromDList theT (lbl :: lbls) (val :: vals)
  = addInput lbl (detach val) (phiFromDList theT lbls vals)

||| Create a phi expression that assigns the same value for all inputs
||| @ ins the inputs
||| @ val the assigned value
export
replicatePhi : (ins : List Label) -> (val : LLValue t) -> PhiExpr ins t
replicatePhi {t} Nil val = case the (The t) (typeOf val) of { MkThe t' => Phi t' Nil }
replicatePhi (lbl :: lbls) val = addInput lbl val $ replicatePhi lbls val
