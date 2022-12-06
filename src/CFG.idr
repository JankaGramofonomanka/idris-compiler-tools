module CFG

import Data.List
import Data.So

import Prop.Elem.Eq
import Prop.Forall


public export
record Vertex (a : Type) where
  constructor MkVertex
  ident : a
  inputs : List a
  outputs : List a


export
data CompatVIVO : Eq a => Vertex a -> Vertex a -> Type where
  DisconnectedIO : Eq a
                => {w, v : Vertex a}
                -> w.ident `NotElem` v.inputs
                -> CompatVIVO v w

  ConnectedIO : Eq a
             => {w, v : Vertex a}
             -> w.ident `Elem` v.inputs
             -> v.ident `Elem` w.outputs
             -> CompatVIVO v w

export
data CompatVOVI : Vertex a -> Vertex a -> Type where
  DisconnectedOI : Eq a
                => {w, v : Vertex a}
                -> w.ident `NotElem` v.outputs
                -> CompatVOVI v w

  ConnectedOI : Eq a
             => {w, v : Vertex a}
             -> w.ident `Elem` v.outputs
             -> v.ident `Elem` w.inputs
             -> CompatVOVI v w

export
CompatVIOVIO : Eq a => Vertex a -> Vertex a -> Type
CompatVIOVIO v w = (CompatVIVO v w, CompatVOVI v w)


export
CompatVV : Eq a => Vertex a -> Vertex a -> Type
CompatVV v w = (CompatVIOVIO v w, So (not $ v.ident == w.ident))


mutual

  public export
  data CFG : (a : Type) -> Eq a => (defined : List a) -> (inputs : List a) -> (outputs : List a) -> Type where
    Empty : Eq a => CFG a [] [] []
    AddVertex : Eq a
              => (v : Vertex a)
              -> (cfg : CFG a defined ins outs)
              -> {auto 0 prf : CompatVG v cfg}
              -> CFG a
                  (v.ident :: defined)
                  (delete v.ident $ ins ++ (v.inputs \\ defined))
                  (delete v.ident $ outs ++ (v.outputs \\ defined))

  
  public export
  data CompatVG : Eq a => Vertex a -> CFG a defined ins outs -> Type where
    CompatVGEmpty : Eq a => {v : Vertex a} -> CompatVG v Empty
    CompatVGAdd : Eq a
                => {cfg : CFG a defined ins outs}
                -> {auto 0 prf : CompatVG w cfg}
                -> CompatVG v cfg
                -> CompatVV v w

                -> CompatVG v (AddVertex w cfg {prf})

public export
data CompatGG : Eq a => CFG a defined ins outs -> CFG a defined' ins' outs' -> Type where
  CompatGGEmpty : Eq a => {cfg : CFG a defined ins outs} -> CompatGG Empty cfg
  CompatGGAdd : Eq a
             => {v : Vertex a}
             -> {cfg  : CFG a defined  ins  outs}
             -> {cfg' : CFG a defined' ins' outs'}
             -> {vcfg   : CompatVG v cfg}
             
             -> (vcfg'  : CompatVG v cfg')
             -> CompatGG cfg cfg'
             -> CompatGG (AddVertex v cfg {prf = vcfg}) cfg'

export
insdefsep : {a : Type}
      -> Eq a
      => {0 defined, ins, outs : List a}
      
      -> (cfg : CFG a defined ins outs)
      -> ins \\ defined = ins
insdefsep Empty = Refl
insdefsep (AddVertex v cfg {prf}) = ?hinsdef

export
outsdefsep : {a : Type}
       -> Eq a
       => {0 defined, ins, outs : List a}
       
       -> (cfg : CFG a defined ins outs)
       -> outs \\ defined = outs

private
getCompatGG : Eq a
           => {v : Vertex a}
           -> {0 defined, defined', ins, ins', outs, outs' : List a}
           -> {cfg : CFG a defined ins outs}
           -> {cfg' : CFG a defined' ins' outs'}
           -> {prf : CompatVG v cfg}
           
           -> CompatGG (AddVertex v cfg) cfg'
           -> CompatGG cfg cfg'

getCompatGG (CompatGGAdd vcfg' cfgcfg') = cfgcfg'

private
getCompatVG : Eq a
           => {v : Vertex a}
           -> {0 defined, defined', ins, ins', outs, outs' : List a}
           -> {cfg : CFG a defined ins outs}
           -> {cfg' : CFG a defined' ins' outs'}
           -> {prf : CompatVG v cfg}

           -> CompatGG (AddVertex v cfg) cfg'
           -> CompatVG v cfg'

getCompatVG (CompatGGAdd vcfg' gg) = vcfg'


mutual
  public export
  connect : {a : Type}
        -> Eq a
        => {0 defined, defined', ins, ins', outs, outs' : List a}
        
        -> (cfg : CFG a defined ins outs)
        -> (cfg' : CFG a defined' ins' outs')
        -> {auto 0 prf : CompatGG cfg cfg'}
        
        -> let defined'' = (defined \\ defined') ++ defined'
            in CFG a defined'' (((ins \\ ins') ++ ins') \\ defined'') (((outs \\ outs') ++ outs') \\ defined'')

  connect Empty cfg = let

    total
    thm : (l : List a) -> [] \\ l = []
    thm Nil = Refl
    thm (x :: xs) = rewrite thm xs in Refl

    in rewrite thm defined'
    in rewrite thm ins'
    in rewrite thm outs'
    in rewrite insdefsep cfg
    in rewrite outsdefsep cfg in cfg

  -- TODO: get rid of the `believe_me`
  connect (AddVertex v cfg {prf = vprf}) cfg' {prf} = let
      
      total
      0 cfgcfg' : CompatGG cfg cfg'
      cfgcfg' = getCompatGG prf

      total
      0 vcfgcfg' : CompatVG v (connect {prf = cfgcfg'} cfg cfg')
      vcfgcfg' = compatVGG vprf (getCompatVG prf) (getCompatGG prf)

    in believe_me $ AddVertex v (connect cfg cfg' {prf = cfgcfg'}) {prf = vcfgcfg'}

  private
  compatVGG : Eq a
     => {v : Vertex a}
     -> {0 defined, defined', ins, ins', outs, outs' : List a}
     -> {cfg : CFG a defined ins outs}
     -> {cfg' : CFG a defined' ins' outs'}
     -> CompatVG v cfg
     -> CompatVG v cfg'
     -> CompatGG cfg cfg'
     -> CompatVG v (connect cfg cfg')
  compatVGG vcfg vcfg' cfgcfg' = ?hcompatVGG --CompatVGAdd ?h1 ?h2


