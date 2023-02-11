module CFG


import Data.DList
import Utils

{-
TODO:
Consider singling out `Just []` / `Defined []` and use `List1` instead of `List`
-}

namespace Vertex  
  {-
  `Neighbors a` - neighbors of a vertex with identifier of type `a`
  - `Just l` means that vertices identified by labels in `l` are neighbors of
    our vertex
  - `Nothing` means that we haven't yet defined the neghbors of our vertex.
  -}
  public export
  Neighbors : Type -> Type
  Neighbors a = Maybe (List a)

  public export
  Undefined : Neighbors a
  Undefined = Nothing

  public export
  Closed : Neighbors a
  Closed = Just []

  public export
  Single : a -> Neighbors a
  Single x = Just [x]

  {-
  `Vertex a` - constructor of verteices of a directed graph, with identifiers
  of type `a`

  if `vertex : Vertex a` then `vertex l ins outs` is a type of vertex with
  identifier `l`, inputs `ins` and outputs `outs`.
  -}
  public export
  Vertex : Type -> Type
  Vertex a = a -> Neighbors a -> Neighbors a -> Type

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
  `Edges a` - edges of an incomplete graph, that have only one end in the
  graph

  - `Undefined v` means the graph has one vertex labeled `v`, with undefined
  inputs (outputs). All other vertices have their inputs (outputs) in the
  graph.
  
  - `Defined edges` means the vertices that are the destinations (origins) of
  edges in `edges` have inputs (outputs) that are the origins (destitnations)
  of edges in `edges`.
  More precisely, if `v ~> w` is a n element of `edges`, then `w` (`v`) is in
  the graph and has input `v` (output `w`), but `v` (`w`) is not in the graph.
  -}
  public export
  data Edges a = Undefined a | Defined (List (Edge a))

  public export
  Closed : Edges a
  Closed = Defined []

  public export
  Single : a -> a -> Edges a
  Single from to = Defined [from ~> to]


  infix 8 ~~>, ~>>, <~~, <<~

  public export
  (~~>) : List v -> v -> List (Edge v)
  vs ~~> v = map (~> v) vs

  public export
  (~>>) : v -> List v -> List (Edge v)
  v ~>> vs = map (v ~>) vs

  public export
  (<~~) : v -> List v -> List (Edge v)
  (<~~) = flip (~~>)
  
  public export
  (<<~) : List v -> v -> List (Edge v)
  (<<~) = flip (~>>)

  export
  collect_concat : (v : a) -> (vs, ws : List a) -> (vs ++ ws) ~~> v = vs ~~> v ++ ws ~~> v
  collect_concat v vs ws = map_concat {f = (~> v)} vs ws

  export
  distribute_concat : (v : a) -> (vs, ws : List a) -> v ~>> (vs ++ ws) = v ~>> vs ++ v ~>> ws
  distribute_concat v vs ws = map_concat {f = (v ~>)} vs ws

  export
  collect_append : (v : a) -> (vs : List a) -> (w : a) -> (vs ++ [w]) ~~> v = vs ~~> v ++ [w ~> v]
  collect_append v vs w = collect_concat v vs [w]

  export
  distribute_append : (v : a) -> (vs : List a) -> (w : a) -> v ~>> (vs ++ [w]) = v ~>> vs ++ [v ~> w]
  distribute_append v vs w = distribute_concat v vs [w]



  public export
  fromVOut : a -> (e : Neighbors a) -> Edges a
  fromVOut v Nothing      = Undefined v
  fromVOut v (Just outs)  = Defined (v ~>> outs)

  public export
  fromVIn : (e : Neighbors a) -> a -> Edges a
  fromVIn Nothing     v = Undefined v
  fromVIn (Just ins)  v = Defined (ins ~~> v)

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
  data CFG : Vertex a -> Edges a -> Edges a -> Type where

    SingleVertex : {0 vertex : Vertex a}
                -> {vins, vouts : Neighbors a}
                -> vertex v vins vouts
                -> CFG vertex (fromVIn vins v) (fromVOut v vouts)

    --Empty : CFG vertex (Defined es) (Defined es)
    
    Cycle : (node : CFG vertex (Defined $ ins ++ ins' ~~> vin) (Defined $ (vout ~> w) :: outs))
         -> (loop : CFG vertex (Single vout w) (Defined $ ins' ~~> vin))
         -> CFG vertex (Defined ins) (Defined outs)

    
    Connect : CFG vertex ins (Defined edges)
           -> CFG vertex (Defined edges) outs
           -> CFG vertex ins outs
    
    Connect1 : CFG vertex ins (Defined $ edges ++ edges')
            -> CFG vertex (Defined edges) (Defined outs)
            -> CFG vertex ins (Defined $ outs ++ edges')
    
    Connect2 : CFG vertex (Defined ins) (Defined edges)
            -> CFG vertex (Defined $ edges ++ edges') outs
            -> CFG vertex (Defined $ ins ++ edges') outs
    
    Parallel : CFG vertex (Defined ins) (Defined outs)
            -> CFG vertex (Defined ins') (Defined outs')
            -> CFG vertex (Defined $ ins ++ ins') (Defined $ outs ++ outs')
    
    IFlip : CFG vertex (Defined $ ins ++ ins') outs
          -> CFG vertex (Defined $ ins' ++ ins) outs
    
    OFlip : CFG vertex ins (Defined $ outs ++ outs')
          -> CFG vertex ins (Defined $ outs' ++ outs)

  public export
  prepend : {0 vertex : Vertex a}
         -> {vins : Neighbors a}
         -> {vouts : List a}
         -> vertex v vins (Just vouts)
         -> CFG vertex (Defined $ v ~>> vouts) gouts
         -> CFG vertex (fromVIn vins v) gouts
  prepend v g = Connect (SingleVertex v) g

  public export
  append : {vins : List a}
        -> {vouts : Neighbors a}
        
        -> CFG vertex gins (Defined $ vins ~~> v)
        -> vertex v (Just vins) vouts
        -> CFG vertex gins (fromVOut v vouts)
  append g v = Connect g (SingleVertex v)
  
  branch : {0 vertex : Vertex a}
        -> {vins : Neighbors a}
        -> {w, w' : a}
        
        -> (pre   : vertex v vins (Just [w, w']))
        -> (left  : CFG vertex (Single v w)  (Defined louts))
        -> (right : CFG vertex (Single v w') (Defined routs))
        -> CFG vertex (fromVIn vins v) (Defined $ louts ++ routs)
  branch pre left right = prepend pre $ Parallel left right

  fullBranch : {0 vertex : Vertex a}
            -> {vins, vouts : Neighbors a}
            -> {w, w', u, u' : a}

            -> (pre    : vertex v vins (Just [w, w']))
            -> (left   : CFG vertex (Single v w)  (Single u t))
            -> (right  : CFG vertex (Single v w') (Single u' t))
            -> (post   : vertex t (Just [u, u']) vouts)
            -> CFG vertex (fromVIn vins v) (fromVOut t vouts)
  fullBranch pre left right post = append (branch pre left right) post
  
  export
  imap : {0 vertex : Vertex a}
          -> {ins : Neighbors a}

          -> ({outs : Neighbors a} -> vertex v Undefined outs -> vertex v ins outs)
          -> CFG vertex (Undefined v) gouts
          -> CFG vertex (fromVIn ins v) gouts

  imap f (SingleVertex {vins = Nothing} v)  = SingleVertex (f v)
  imap f (Connect g g')                     = Connect (imap f g) g'
  imap f (Connect1 g g')                    = Connect1 (imap f g) g'
  
  imap f (OFlip g)                          = OFlip (imap f g)
  
  imap f (SingleVertex {vins = Just ins} v) impossible
  imap f (Cycle node loop)                  impossible
  imap f (Connect2 g g')                    impossible
  imap f (Parallel g g')                    impossible
  imap f (IFlip g)                          impossible
  
  
  export
  omap : {0 vertex : Vertex a}
          -> {outs : Neighbors a}

          -> ({ins : Neighbors a} -> vertex v ins Undefined -> vertex v ins outs)
          -> CFG vertex gins (Undefined v)
          -> CFG vertex gins (fromVOut v outs)

  omap f (SingleVertex {vouts = Nothing} v)   = SingleVertex (f v)
  omap f (Connect g g')                       = Connect g (omap f g')
  omap f (Connect2 g g')                      = Connect2 g (omap f g')
  omap f (IFlip g)                            = IFlip (omap f g)
  
  omap f (SingleVertex {vouts = Just outs} v) impossible
  omap f (Cycle node loop)                    impossible
  omap f (Connect1 g g')                      impossible
  omap f (Parallel g g')                      impossible
  omap f (OFlip g)                            impossible

  export
  connect : (impl : Connectable vertex)
         => CFG vertex ins (Undefined v)
         -> CFG vertex (Undefined v) outs
         -> CFG vertex ins outs

  connect (SingleVertex {vouts = Nothing} v)  g   = imap (cnct @{impl} v) g
  connect (Connect g g')                      g'' = Connect g (connect g' g'')
  connect (Connect2 g g')                     g'' = Connect2 g (connect g' g'')
  connect (IFlip g)                           g'  = IFlip (connect g g')

  connect (SingleVertex {vouts = Just outs} v)  g' impossible
  connect (Cycle node loop)                     g' impossible
  connect (Connect1 g g')                       g' impossible
  connect (Parallel g g')                       g' impossible
  connect (OFlip g)                             g' impossible
  

  export
  initGraph : {vertex : Vertex a}
           -> vertex v Undefined Undefined
           -> CFG vertex (Undefined v) (Undefined v)
  initGraph v = SingleVertex v


  export
  iget : {0 vertex : Vertex a}
       -> ({outs : Neighbors a} -> vertex v Undefined outs -> b)
       -> CFG vertex (Undefined v) gouts
       -> b
  iget f (SingleVertex {vins = Nothing} v)  = f v
  iget f (Connect g g')                     = iget f g
  iget f (Connect1 g g')                    = iget f g
  iget f (OFlip g)                          = iget f g
  
  iget f (SingleVertex {vins = Just ins} v) impossible
  iget f (Cycle node loop)                  impossible
  iget f (Connect2 g g')                    impossible
  iget f (Parallel g g')                    impossible
  iget f (IFlip g)                          impossible

  export
  oget : {0 vertex : Vertex a}
          -> ({ins : Neighbors a} -> vertex v ins Undefined -> b)
          -> CFG vertex gins (Undefined v)
          -> b

  oget f (SingleVertex {vouts = Nothing} v)   = f v
  oget f (Connect g g')                       = oget f g'
  oget f (Connect2 g g')                      = oget f g'
  oget f (IFlip g)                            = oget f g
  
  oget f (SingleVertex {vouts = Just outs} v) impossible
  oget f (Cycle node loop)                    impossible
  oget f (Connect1 g g')                      impossible
  oget f (Parallel g g')                      impossible
  oget f (OFlip g)                            impossible


