module CFG


import Data.DList
import Utils

namespace Vertex
  
  {-
  `Endpoint a` - neighbors of a vertex with identifier of type `a`
  - `Just l` means that vertices identified by labels in `l` are neighbors of
    our vertex
  - `Nothing` means that we haven't yet defined the neghbors of our vertex.
  -}
  public export
  Endpoint : Type -> Type
  Endpoint a = Maybe (List a)

  public export
  Undefined : Endpoint a
  Undefined = Nothing

  public export
  Closed : Endpoint a
  Closed = Just []

  public export
  Single : a -> Endpoint a
  Single x = Just [x]

  {-
  `Vertex a` - constructor of verteices of a directed graph, with identifiers
  of type `a`

  if `vertex : Vertex a` then `vertex l ins outs` is a type of vertex with
  identifier `l`, inputs `ins` and outputs `outs`.
  -}
  public export
  Vertex : Type -> Type
  Vertex a = a -> Endpoint a -> Endpoint a -> Type

  public export
  interface Connectable (0 vertex : Vertex a) where
    cnct : vertex v ins Undefined
        -> vertex v Undefined outs
        -> vertex v ins outs

namespace Graph

  infix 6 ~>, <~

  -- `v ~> w` - an edge from `v` to `w`
  public export
  data Edge : Type -> Type where
    (~>) : a -> a -> Edge a  

  public export
  (<~) : a -> a -> Edge a
  (<~) = flip (~>)

  public export
  Dest : Edge a -> a
  Dest (from ~> to) = to

  public export
  Origin : Edge a -> a
  Origin (from ~> to) = from

  {-
  `Endpoints a` - edges of an incomplete graph, that have only one end in the
  graph

  - `Undefined v` means the graph has one vertex labeled `v`, with undefined
  inputs (outputs). All other vertices have their inputs (outputs) in the
  graph.
  
  - `Ends edges` means the vertices that are the destinations (origins) of
  edges in `edges` have inputs (outputs) that are the origins (destitnations)
  of edges in `edges`.
  More precisely, if `v ~> w` is a n element of `edges`, then `w` (`v`) is in
  the graph and has input `v` (output `w`), but `v` (`w`) is not in the graph.
  -}
  public export
  data Endpoints a = Undefined a | Ends (List (Edge a))

  public export
  Closed : Endpoints a
  Closed = Ends []

  public export
  Single : a -> a -> Endpoints a
  Single from to = Ends [from ~> to]

  public export
  data AllLeadTo : List (Edge a) -> a -> Type where
    ALTNil : Nil `AllLeadTo` e
    ALTCons : es `AllLeadTo` to
           -> ((from ~> to) :: es) `AllLeadTo` to



  export
  alt_map : ends `AllLeadTo` lbl -> ends = map (~> lbl) (map Origin ends)
  alt_map ALTNil = Refl
  alt_map (ALTCons {es, from, to} prf) = rewrite revEq $ alt_map prf in Refl

  export
  alt_concat : ends `AllLeadTo` lbl -> ends' `AllLeadTo` lbl -> ends ++ ends' `AllLeadTo` lbl
  alt_concat ALTNil prf' = prf'
  alt_concat (ALTCons prf) prf' = ALTCons (alt_concat prf prf')


  public export
  fromVOut : a -> (e : Endpoint a) -> Endpoints a
  fromVOut v Nothing      = Undefined v
  fromVOut v (Just outs)  = Ends $ map (v ~>) outs

  public export
  fromVIn : (e : Endpoint a) -> a -> Endpoints a
  fromVIn Nothing     v = Undefined v
  fromVIn (Just ins)  v = Ends $ map (~> v) ins

  {-
  TODO: Consider adding an `data` parameter to `CFG` that would be the type of
  data that would be stored alongside vertices.
  
  The `data` could be:
    - the values of variables
    - variables that were changed
    - variables that are live
  -}
  {-
  A potentially incomplete control flow graph.
  `CFG vertex ins outs` is a graph where:
    `ins`     - edges from "to be defined" vertices to vertices in the graph
    `outs`    - edges from vertices in the graph to "to be defined" vertices
    `vertex`  - constructor of vertex types.
  -}
  public export
  data CFG : Vertex a -> Endpoints a -> Endpoints a -> Type where

    SingleVertex : {0 vertex : Vertex a}
                -> {vins, vouts : Endpoint a}
                -> vertex v vins vouts
                -> CFG vertex (fromVIn vins v) (fromVOut v vouts)

    Empty : CFG vertex (Ends es) (Ends es)
    
    Cycle : (node : CFG vertex (Ends $ (u ~> vin) :: ins) (Ends $ (vout ~> w) :: outs))
         -> (loop : CFG vertex (Single vout w) (Single u vin))
         -> CFG vertex (Ends ins) (Ends outs)

    -- TODO: Consider the following
    --Cycle : (node : Vertex v (Just $ ins ++ u :: ins') (Just $ outs ++ w :: outs'))
    --     -> (loop : CFG a (Single v w) (Single u v))
    --     -> CFG a (fromVIn (Just $ ins ++ ins') v) (fromVOut v (Just $ outs ++ outs'))


    
    Connect : CFG vertex ins (Ends edges)
           -> CFG vertex (Ends edges) outs
           -> CFG vertex ins outs
    
    Parallel : CFG vertex (Ends ins) (Ends outs)
            -> CFG vertex (Ends ins') (Ends outs')
            -> CFG vertex (Ends $ ins ++ ins') (Ends $ outs ++ outs')
    
    FlipIn : CFG vertex (Ends $ ins ++ ins') outs
          -> CFG vertex (Ends $ ins' ++ ins) outs
    
    FlipOut : CFG vertex ins (Ends $ outs ++ outs')
           -> CFG vertex ins (Ends $ outs' ++ outs)

  public export
  prepend : {0 vertex : Vertex a}
         -> {vins : Endpoint a}
         -> {vouts : List a}
         -> vertex v vins (Just vouts)
         -> CFG vertex (Ends $ map (v ~>) vouts) gouts
         -> CFG vertex (fromVIn vins v) gouts
  prepend v g = Connect (SingleVertex v) g

  public export
  append : {vins : List a}
        -> {vouts : Endpoint a}
        
        -> CFG vertex gins (Ends $ map (~> v) vins)
        -> vertex v (Just vins) vouts
        -> CFG vertex gins (fromVOut v vouts)
  append g v = Connect g (SingleVertex v)
  
  branch : {0 vertex : Vertex a}
        -> {vins : Endpoint a}
        -> {w, w' : a}
        
        -> (pre   : vertex v vins (Just [w, w']))
        -> (left  : CFG vertex (Single v w)  (Ends louts))
        -> (right : CFG vertex (Single v w') (Ends routs))
        -> CFG vertex (fromVIn vins v) (Ends $ louts ++ routs)
  branch pre left right = prepend pre $ Parallel left right

  fullBranch : {0 vertex : Vertex a}
            -> {vins, vouts : Endpoint a}
            -> {w, w', u, u' : a}

            -> (pre    : vertex v vins (Just [w, w']))
            -> (left   : CFG vertex (Single v w)  (Single u t))
            -> (right  : CFG vertex (Single v w') (Single u' t))
            -> (post   : vertex t (Just [u, u']) vouts)
            -> CFG vertex (fromVIn vins v) (fromVOut t vouts)
  fullBranch pre left right post = append (branch pre left right) post
  
  export
  imap : {0 vertex : Vertex a}
          -> {ins : Endpoint a}

          -> ({outs : Endpoint a} -> vertex v Undefined outs -> vertex v ins outs)
          -> CFG vertex (Undefined v) gouts
          -> CFG vertex (fromVIn ins v) gouts

  imap f (SingleVertex {vins = Nothing} v)  = SingleVertex (f v)
  imap f (Connect g g')                     = Connect (imap f g) g'
  imap f (FlipOut g)                        = FlipOut (imap f g)
  
  imap f (SingleVertex {vins = Just ins} v) impossible
  imap f Empty                              impossible
  imap f (Cycle node loop)                  impossible
  imap f (Parallel g g')                    impossible
  imap f (FlipIn g)                         impossible
  
  
  export
  omap : {0 vertex : Vertex a}
          -> {outs : Endpoint a}

          -> ({ins : Endpoint a} -> vertex v ins Undefined -> vertex v ins outs)
          -> CFG vertex gins (Undefined v)
          -> CFG vertex gins (fromVOut v outs)

  omap f (SingleVertex {vouts = Nothing} v)   = SingleVertex (f v)
  omap f (Connect g g')                       = Connect g (omap f g')
  omap f (FlipIn g)                           = FlipIn (omap f g)
  
  omap f (SingleVertex {vouts = Just outs} v) impossible
  omap f Empty                                impossible
  omap f (Cycle node loop)                    impossible
  omap f (Parallel g g')                      impossible
  omap f (FlipOut g)                          impossible

  export
  connect : (impl : Connectable vertex)
         => CFG vertex ins (Undefined v)
         -> CFG vertex (Undefined v) outs
         -> CFG vertex ins outs

  connect (SingleVertex {vouts = Nothing} v)  g   = imap (cnct @{impl} v) g
  connect (Connect g g')                      g'' = Connect g (connect g' g'')
  connect (FlipIn g)                          g'  = FlipIn (connect g g')

  connect (SingleVertex {vouts = Just outs} v)  g' impossible
  connect Empty                                 g' impossible
  connect (Cycle node loop)                     g' impossible
  connect (Parallel g g')                       g' impossible
  connect (FlipOut g)                           g' impossible
  

  export
  initGraph : {vertex : Vertex a}
           -> vertex v Undefined Undefined
           -> CFG vertex (Undefined v) (Undefined v)
  initGraph v = SingleVertex v


  export
  iget : {0 vertex : Vertex a}
       -> ({outs : Endpoint a} -> vertex v Undefined outs -> b)
       -> CFG vertex (Undefined v) gouts
       -> b
  iget f (SingleVertex {vins = Nothing} v)  = f v
  iget f (Connect g g')                     = iget f g
  iget f (FlipOut g)                        = iget f g
  
  iget f (SingleVertex {vins = Just ins} v) impossible
  iget f Empty                              impossible
  iget f (Cycle node loop)                  impossible
  iget f (Parallel g g')                    impossible
  iget f (FlipIn g)                         impossible

  export
  oget : {0 vertex : Vertex a}
          -> ({ins : Endpoint a} -> vertex v ins Undefined -> b)
          -> CFG vertex gins (Undefined v)
          -> b

  oget f (SingleVertex {vouts = Nothing} v)   = f v
  oget f (Connect g g')                       = oget f g'
  oget f (FlipIn g)                           = oget f g
  
  oget f (SingleVertex {vouts = Just outs} v) impossible
  oget f Empty                                impossible
  oget f (Cycle node loop)                    impossible
  oget f (Parallel g g')                      impossible
  oget f (FlipOut g)                          impossible


