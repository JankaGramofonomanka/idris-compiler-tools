module Compile.Data.Context.Utils


import Control.Monad.State

import Data.Attached
import Data.DMap
import Data.DList
import Data.Doc
import Data.DSum
import Data.GCompare
import Data.Some
import Data.The
import Data.Typed
import LNG.TypeChecked
import LNG.TypeChecked.Render
import LLVM
import Compile.Data.CompM
import Compile.Data.Context
import Compile.Data.Error
import Compile.Utils
import CFG

||| A variable context at the merging point of multiple branches and a list of
||| phi assignments needed to be executed in order to produce that context.
|||
||| @ lbl the label of the merging block of the branches
||| @ ins the sources of the branch output edges
|||     / the labels of the last blocks in the branches
public export
record Segregated (lbl : Label) (ins : List Label) where
  constructor SG
  ||| The context after merging multiple bracnhes and executing the phi
  ||| assignments in the `phis`
  ctx : lbl :~: VarCTX
  ||| The phi assignments needed to produce `ctx`
  phis : List (PhiInstr ins, Maybe String)


-- TODO: Consider rewriting `PhiExpr` so that it equals to this type
||| A substitute for `PhiExpr` constructed from values attached to edges.
|||
||| The labels are erased as opposed to the labels in `PhiExpr`
||| @ lbl the label of the block the expression is part of
||| @ ins the labels of the input blocks
||| @ t   the type of the expression
data Phi' : (lbl : Label) -> (ins : List Label) -> (t : LLType) -> Type where

  ||| Make a `Phi'` expression
  ||| @ t    the type of the expression
  ||| @ ins  the labels of the input blocks
  ||| @ vals the list of values attached to the respective edges
  MkPhi'
     : (t    : LLType)
    -> (vals : DList (:~: LLValue t) (ins ~~> lbl))
    -> Phi' lbl ins t

implementation Typed (Phi' lbl ins) where
  typeOf (MkPhi' t _) = MkThe t

||| Given a an implicit list of input labels, convert a `Phi'` to `PhiExpr`
||| @ ins the input labels
||| @ phi the phi expression to convert
toPhi : {ins : List Label} -> (phi : Phi' lbl ins t) -> PhiExpr ins t
toPhi {ins = Nil} (MkPhi' t Nil) = Phi t Nil
toPhi {ins = lbl :: lbls} (MkPhi' t (val :: vals)) = let
    Phi t pairs = toPhi {ins = lbls} (MkPhi' t vals)
  in Phi t ((lbl, detach val) :: pairs)

||| A value or a phi expression
|||
||| Given a list of contexts a the ends of converging branches, this indicates
||| if the value of a given variable is the same across all of them or not.
ValueOrPhi : Label -> List Label -> LNGType -> Type
ValueOrPhi lbl ins t = Either (Phi' lbl ins $ GetLLType t) (LLValue $ GetLLType t)

||| A mapping from variables to values or phi expressions.
|||
||| Given a list of contexcts at the ends of converging branches, this mapping
||| tells you if the value of a given variable is the same across all of them
||| or not.
||| If not, a phi expressions is assigned to that variable, with the values of
||| that variable in the respective contexts.
|||
||| @ lbl the label of the merging block of the branches
||| @ ins the sources of the branch output edges
|||     / the labels of the last blocks in the branches
record Segregated' (lbl : Label) (ins : List Label) where
  constructor SG'
  ctx : DMap Variable (ValueOrPhi lbl ins)

||| Extend the inputs of a phi expression by adding a value to it
||| @ val the value
||| @ phi the expression to be extended
addInput'
   : (val : (lbl ~> lbl') :~: (LLValue t))
  -> (phi : Phi' lbl' ins t)
  ->        Phi' lbl' (lbl :: ins) t
addInput' val (MkPhi' t kvs) = MkPhi' t $ val :: kvs

||| Given a list of input labels and a value, make a `Phi'` assignment that
||| assigns that value regardless of the input
replicatePhi' : (ins : List Label) -> LLValue t -> Phi' lbl' ins t
replicatePhi' {t} Nil val = case the (The t) (typeOf val) of { MkThe t' => MkPhi' t' Nil }
replicatePhi' {lbl'} (lbl :: lbls) val = addInput' (attach (lbl ~> lbl') val) $ replicatePhi' lbls val

addValueOrPhi
   : (var : Variable t)
  -> (lbl ~> lbl') :~: (LLValue (GetLLType t))
  -> {ins : List Label}
  -> ValueOrPhi lbl' ins t
  -> Segregated' lbl' (lbl :: ins)
  -> Segregated' lbl' (lbl :: ins)

addValueOrPhi key val (Right val') (SG' ctx)
  = if val' == detach val then
      SG' (DMap.insert key (Right val') ctx)

    else let
      phi = addInput' val $ replicatePhi' ins val'

      in SG' (DMap.insert key (Left phi) ctx)

addValueOrPhi key val (Left phi) (SG' ctx) = let
  phi' = addInput' val phi

  in SG' (DMap.insert key (Left phi') ctx)

||| Merge a `Segregated'` mapping with a context, thus extending its input
||| list by one input label.
||| @ lbl the additional input
||| @ ctx the context coming from the `lbl` input
||| @ ins the input labels of `sg`
||| @ sg  the `Segregated'` mapping
addCTX
   : (ctx : (lbl ~> lbl') :~: VarCTX)
  -> {ins : List Label}
  -> (sg : Segregated' lbl'         ins)
  ->       Segregated' lbl' (lbl :: ins)
addCTX ctx {ins} (SG' ctx')

  -- for every varable-value pair in `ctx` merge the value with the
  -- "value or phi" from `ctx'` and insert the results into the new mapping
  = foldl handleItem (SG' DMap.empty) (distribute $ map VarCTX.toList ctx)
  where
    ||| Given a variable-value pair and a `Segregated'` mapping, merge the
    ||| value with the "value or phi" from `ctx'` and insert it to the mapping.
    ||| @ sg     the `Segregated'` mapping
    ||| @ varVal the variable-value pair
    handleItem
       : (sg     : Segregated' lbl' (lbl :: ins))
      -> (varVal : (lbl ~> lbl') :~: DSum Variable (LLValue . GetLLType))
      ->           Segregated' lbl' (lbl :: ins)
    handleItem sg item = let

      -- Extract the varaible (`key`) and the value (`val`) from the pair (`item`)
      MkSome item' = inSome $ map toSome item
      key = detach $ map fst item'
      val = map snd item'

      in case DMap.lookup key ctx' of
        -- If the variable is not present in the original mapping, it needs to be discarded
        Nothing => sg
        -- Otherwise, merge it with the "value or phi" from the original
        -- mapping and add it to the new mapping
        Just vp => addValueOrPhi key val vp sg

||| Convert a `Segregated'` mapping to a `Segregated` mapping by generating a
||| fresh register and a phi assignment for every variable with a phi
||| expression assigned.
||| @ ins the input labels
||| @ the `Segregated'` mapping to be converted
finalize
   : {ins : List Label}
  -> (sg  : Segregated' lbl ins)
  -> CompM (Segregated lbl ins)
finalize {ins, lbl} (SG' ctx)
  = foldlM handleItem (SG (attach lbl VarCTX.empty) Nil) (toList ctx) where

  ||| Given a variable--value-or-phi pair, and a `Segregated` mapping, extend
  ||| the mapping to take that pair into account
  ||| @ sg   the mapping
  ||| @ item the variable--value-or-phi pair
  handleItem
     : (sg : Segregated lbl ins)
    -> (item : DSum Variable (ValueOrPhi lbl ins))
    -> CompM (Segregated lbl ins)
  handleItem (SG ctx' phis) (key :=> vp) = case vp of

    -- Given a variable-value pair, just insert the pair to the context
    Right val => pure $ SG (map (DMap.insert key val) ctx') phis

    -- Given a variable-phi pair,
    Left phi => do
      -- generate a fresh register and construct a phi assignment
      reg <- freshRegister' (typeOf phi)
      let phi = AssignPhi reg (toPhi phi)

      -- insert the variabel and the fresh register to the context and add the
      -- phi assignemnt to the existing assignemtns
      pure $ SG (map (DMap.insert key (Var reg)) ctx') ((phi, Just $ prt key) :: phis)

||| Given a list of contexts from converging branches, constructs a
||| `Segregated'` mapping that will indicate whether the value of each variable
||| from the contexts is the same across all of them or not.
||| @ lbls the sources of the converging edges
||| @ ctxs the contexts
segregate'
   : {lbls : List Label}
  -> (ctxs : DList (:~: VarCTX) (lbls ~~> lbl))
  -> Segregated' lbl lbls
segregate' {lbls = Nil}      Nil           = SG' DMap.empty
segregate' {lbls = l :: Nil} (ctx :: Nil)  = SG' { ctx = map Right (detach ctx) }
segregate' {lbls = l :: ls}  (ctx :: ctxs) = addCTX ctx (segregate' ctxs)

-- TODO: consider another name - `merge`
||| Merge contexts from converging branches.
|||
||| Given a list of contexts, generates a context *ctx* and a list of phi
||| assignments *phis*.
||| *ctx* contains those variables that are present in all of the given
||| contexts.
||| If the value assigned to a given variable is the same across the contexts,
||| it will stay assigned to that variable in *ctx*.
||| Otherwise, a phi assignment establishing a new value based on the different
||| values is generated and added to *phis*.
||| The value established by that phi assignment is then assigned to the
||| variable in *ctx.
|||
||| The contexts are attached to the edges between the branches and their
||| merging point and the result is attached the label of that merging block.
|||
||| @ lbls the sources of the converging edges
||| @ ctxs the contexts to merge
export
segregate
   : {lbls : List Label}
  -> (ctxs : DList (:~: VarCTX) (lbls ~~> lbl))
  -> CompM $ Segregated lbl lbls
segregate ctxs = finalize (segregate' ctxs)

||| Given a list of variables, generate a context, where every variable will
||| have a fresh regtiser assigned.
||| @ vars the variable list
newRegForAll' : (vars : List (t ** Variable t)) -> CompM VarCTX'
newRegForAll' vars = foldlM addNewReg DMap.empty vars where
  addNewReg
     : VarCTX'
    -> (t ** Variable t)
    -> CompM VarCTX'
  addNewReg ctx (t ** var) = pure (VarCTX'.insert var !(freshRegister $ GetLLType t) ctx)

||| Returns a list of variables present in all the context in the given context
||| list.
||| @ ctxs the contexts
commonKeys : (ctxs : DList (:~: VarCTX) lbls) -> List (t ** Variable t)
commonKeys ctxs = VarCTX.keys (intersection' ctxs) where

  intersection' : DList (:~: VarCTX) lbls' -> VarCTX
  intersection' Nil = VarCTX.empty
  intersection' (ctx :: Nil) = detach ctx
  intersection' (ctx :: ctxs) = VarCTX.intersection (detach ctx) (intersection' ctxs)

||| Given a list of contexts, generate a new one, where every variahble present
||| in all the contexts will have a fresh regtiser assigned.
|||
||| The contexts are attached to edges converting to a single block and the
||| result is attached the label of that block.
|||
||| @ ctxs the list of contexts
export
newRegForAll
   : (ctxs : DList (:~: VarCTX) (from ~~> to))
  -> CompM (to :~: VarCTX')
newRegForAll {to} ctxs = attach to <$> newRegForAll' (commonKeys ctxs)
