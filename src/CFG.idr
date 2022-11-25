module CFG

import Data.List

import Utils
import Prop.Elem



export
record Vertex (a : Type) where
  constructor MkVertex
  ident : a
  inputs : List a
  outputs : List a

Decide : Type -> Type
Decide thm = Either (Not thm) thm


export
data CompatVVIO : Vertex a -> Vertex a -> Type where
  DisconnectedIO : Forall v.inputs (\input => Not (w.ident = input)) -> CompatVVIO v w
  ConnectedIO : w `Elem` vins -> v `Elem` wouts -> CompatVVIO (MkVertex v vins vouts) (MkVertex w wins wouts)

export
data CompatVVOI : Vertex a -> Vertex a -> Type where
  DisconnectedOI : Forall v.outputs (\output => Not (w.ident = output)) -> CompatVVOI v w
  ConnectedOI : w `Elem` vouts -> v `Elem` wins -> CompatVVOI (MkVertex v vins vouts) (MkVertex w wins wouts)

export
CompatVV : Vertex a -> Vertex a -> Type
CompatVV v w = (CompatVVIO v w, CompatVVOI v w)

mutual

  public export
  data CFG : (a : Type) -> Eq a => (inputs : List a) -> (outputs : List a) -> Type where
    Empty : Eq a => CFG a [] []
    AddVertex : Eq a
              => (v : Vertex a)
              -> (cfg : CFG a ins outs)
              -> {auto 0 prf : CompatVG v cfg newIns newOuts}
              -> CFG a (newIns ++ ins) (newOuts ++ outs)

  public export
  data CompatVG : Eq a => Vertex a -> CFG a ins outs -> List a -> List a -> Type where
    CompatEmpty : Eq a => {v : Vertex a} -> CompatVG v Empty v.inputs v.outputs
    CompatAdd : Eq a
              => {cfg : CFG a inputs outputs}
              -> {auto 0 prf : CompatVG w cfg _ _}
              -> CompatVG v cfg ins outs
              -> CompatVV v w

              -> CompatVG v (AddVertex w cfg {prf}) (delete w.ident ins) (delete w.ident outs)
  
data ForallG : Eq a => CFG a ins outs -> (Vertex a -> Type) -> Type where
  ForallGempty : (impl : Eq a) => ForallG @{impl} Empty prop
  ForallGAdd : Eq a
            
            => prop v
            
            -> {cfg : CFG a ins outs}
            -> ForallG cfg prop
            
            -> {auto 0 prf : CompatVG v cfg newIns newOuts}
            -> ForallG (AddVertex v cfg {prf}) prop

export
0 CompatGG : Eq a => CFG a ins outs -> CFG a ins' outs' -> Type
CompatGG cfg cfg' = ForallG cfg compat where
  compat : Vertex a -> Type
  compat v = (ins  ** outs  ** CompatVG v cfg' ins outs)

-- TODO: define connecting compatible graphs together

namespace Example

  Label : Type
  Label = String

  {-
    preLoop:
      jump cond
    cond
      condjump c loopBody postloop
    loopBody:
      ...
      jump cond
    postloop
      ...
  -}

  loopBody1 : CFG Label ["cond"] ["cond"]
  loopBody1 = AddVertex (MkVertex "loopBody" ["cond"] ["cond"]) {prf = CompatEmpty} Empty

  
  whileTemplate : (preLoop, firstInBody, lastInBody, postLoop : Label)
               -> CFG Label [preLoop, lastInBody] [firstInBody, postLoop]
  
  whileTemplate preLoop firstInBody lastInBody postLoop
    = AddVertex (MkVertex "cond" [preLoop, lastInBody] [firstInBody, postLoop]) {prf = CompatEmpty}
    $ Empty


