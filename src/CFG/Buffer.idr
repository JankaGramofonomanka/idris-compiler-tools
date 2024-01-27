module CFG.Buffer

import CFG
import Data.DList
import Theory

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
  UNeighbors : Type -> Type
  UNeighbors a = Maybe (Neighbors a)

  public export
  Undefined : UNeighbors a
  Undefined = Nothing

  public export
  Closed : UNeighbors a
  Closed = Just []

  public export
  Single : a -> UNeighbors a
  Single x = Just [x]

  {-
  `Vertex a` - constructor of verteices of a directed graph, with identifiers
  of type `a`

  if `vertex : Vertex a` then `vertex l ins outs` is a type of vertex with
  identifier `l`, inputs `ins` and outputs `outs`.
  -}
  public export
  UVertex : Type -> Type
  UVertex a = a -> UNeighbors a -> UNeighbors a -> Type

  public export
  UnU : UVertex a -> Vertex a
  UnU uvertex v ins outs = uvertex v (Just ins) (Just outs)

  public export
  interface Connectable (0 vertex : UVertex a) where
    cnct : vertex v ins Undefined
        -> vertex v Undefined outs
        -> vertex v ins outs

namespace Graph

  infix 6 ~>, <~

  -- `v ~> w` - an edge from `v` to `w`
  public export
  data UEdge a = Undefined a | Defined (Edge a)

  public export
  (~>) : a -> a -> UEdge a
  v ~> w = Defined (v ~> w)

  public export
  (<~) : a -> a -> UEdge a
  (<~) = flip (~>)

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
  UEdges : Type -> Type
  UEdges a = List (UEdge a)

  public export
  Closed : UEdges a
  Closed = []

  public export
  Single : a -> a -> UEdges a
  Single from to = [from ~> to]


  infix 8 ~~>, ~>>, <~~, <<~

  public export
  (~~>) : List v -> v -> UEdges v
  vs ~~> v = map (~> v) vs

  public export
  (~>>) : v -> List v -> UEdges v
  v ~>> vs = map (v ~>) vs

  public export
  (<~~) : v -> List v -> UEdges v
  (<~~) = flip (~~>)
  
  public export
  (<<~) : List v -> v -> UEdges v
  (<<~) = flip (~>>)

  {-
  export
  collect_concat : (v : a) -> (vs, ws : UEdges a) -> (vs ++ ws) ~~> v = vs ~~> v ++ ws ~~> v
  collect_concat v vs ws = List.map_concat {f = (~> v)} vs ws

  export
  distribute_concat : (v : a) -> (vs, ws : UEdges a) -> v ~>> (vs ++ ws) = v ~>> vs ++ v ~>> ws
  distribute_concat v vs ws = List.map_concat {f = (v ~>)} vs ws

  export
  collect_append : (v : a) -> (vs : UEdges a) -> (w : a) -> (vs ++ [w]) ~~> v = vs ~~> v ++ [w ~> v]
  collect_append v vs w = collect_concat v vs [w]

  export
  distribute_append : (v : a) -> (vs : UEdges a) -> (w : a) -> v ~>> (vs ++ [w]) = v ~>> vs ++ [v ~> w]
  distribute_append v vs w = distribute_concat v vs [w]
  -}

  public export
  fromVOut : a -> (e : UNeighbors a) -> UEdges a
  fromVOut v Nothing      = [Undefined v]
  fromVOut v (Just outs)  = v ~>> outs

  public export
  fromVIn : (e : UNeighbors a) -> a -> UEdges a
  fromVIn Nothing     v = [Undefined v]
  fromVIn (Just ins)  v = ins ~~> v

  namespace Pre
    public export
    data Specify : UEdge a -> Type where
      Noop : Specify (Defined edg)
      Outs : (outs : Neighbors a) -> Specify {a} (Undefined v)

    public export
    UnU : (edg : UEdge a) -> Specify edg -> Edges a
    UnU (Defined edg) Noop = [edg]
    UnU (Undefined v) (Outs outs) = v ~>> outs

    public export
    Apply : (edgs : UEdges a) -> DList Specify edgs -> Edges a
    Apply Nil Nil = Nil
    Apply (edg :: edgs) (spec :: specs) = Pre.UnU edg spec ++ Apply edgs specs


  namespace PreBuffer

    public export
    data Buffer : (vertex : UVertex a) -> (edg : UEdge a) -> Specify edg -> Type where
      Noop : Buffer vertex (Defined edg) Noop
      Pre : {0 v : a} -> vertex v Nothing (Just outs) -> Buffer vertex (Undefined v) (Outs outs)

    public export
    data Buffers : (vertex : UVertex a) -> (edgs : UEdges a) -> DList Specify edgs -> Type where
      Nil : Buffers vertex Nil Nil
      (::) : Buffer vertex edg spec -> Buffers vertex edgs specs -> Buffers vertex (edg :: edgs) (spec :: specs)

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
  record CFG (vertex : UVertex a) (ins : UEdges a) (outs : UEdges a) where
    constructor MkCFG
    preSpec : DList Specify ins
    pre : Buffers vertex ins preSpec
    --postSpec : DList Specify outs
    --post : Buffers vertex outs postSpec
    cfg : CFG.Graph.CFG (UnU vertex) (Apply ins preSpec) []

    --pre : ?
    --cfg : CFG.Graph.CFG (UnU vertex) (? ins) (? outs)
    --post : ?


    
  {-
  infixr 4 |-|
  public export
  (|-|) : CFG vertex (Defined ins)           (Defined outs)
       -> CFG vertex (Defined ins')          (Defined outs')
       -> CFG vertex (Defined $ ins ++ ins') (Defined $ outs ++ outs')
  (|-|) = Parallel

  infixr 5 *->
  public export
  (*->) : CFG vertex ins (Defined edges)
       -> CFG vertex (Defined edges) outs
       -> CFG vertex ins outs
  (*->) = Series
          

  public export
  prepend : {0 vertex : Vertex a}
         -> {vins : Neighbors a}
         -> {vouts : List a}
         -> vertex v vins (Just vouts)
         -> CFG vertex (Defined $ v ~>> vouts) gouts
         -> CFG vertex (fromVIn vins v) gouts
  prepend v g = (SingleVertex v) *-> g

  public export
  append : {vins : List a}
        -> {vouts : Neighbors a}
        
        -> CFG vertex gins (Defined $ vins ~~> v)
        -> vertex v (Just vins) vouts
        -> CFG vertex gins (fromVOut v vouts)
  append g v = g *-> (SingleVertex v)
  
  branch : {0 vertex : Vertex a}
        -> {vins : Neighbors a}
        -> {w, w' : a}
        
        -> (pre   : vertex v vins (Just [w, w']))
        -> (left  : CFG vertex (Single v w)  (Defined louts))
        -> (right : CFG vertex (Single v w') (Defined routs))
        -> CFG vertex (fromVIn vins v) (Defined $ louts ++ routs)
  branch pre left right = pre `prepend` (left |-| right)

  fullBranch : {0 vertex : Vertex a}
            -> {vins, vouts : Neighbors a}
            -> {w, w', u, u' : a}

            -> (pre    : vertex v vins (Just [w, w']))
            -> (left   : CFG vertex (Single v w)  (Single u t))
            -> (right  : CFG vertex (Single v w') (Single u' t))
            -> (post   : vertex t (Just [u, u']) vouts)
            -> CFG vertex (fromVIn vins v) (fromVOut t vouts)
  fullBranch pre left right post = (branch pre left right) `append` post

  public export  
  lbranch : {ls, rs : List (Edge a)}
         -> (node   : CFG vertex ins (Defined $ ls ++ rs))
         -> (branch : CFG vertex (Defined ls) (Defined ls'))
         ->           CFG vertex ins (Defined $ ls' ++ rs)
  lbranch node branch = node *-> (branch |-| Empty)

  public export
  rbranch : {ls, rs : List (Edge a)}
         -> (node   : CFG vertex ins (Defined $ ls ++ rs))
         -> (branch : CFG vertex (Defined rs) (Defined rs'))
         ->           CFG vertex ins (Defined $ ls ++ rs')
  rbranch node branch = node *-> (Empty |-| branch)

  public export
  lmerge : {ls, rs  : List (Edge a)}
        -> (branch  : CFG vertex (Defined ls) (Defined ls'))
        -> (node    : CFG vertex (Defined $ ls' ++ rs) outs)
        ->            CFG vertex (Defined $ ls ++ rs) outs
  lmerge branch node = (branch |-| Empty) *-> node

  public export
  rmerge : {ls, rs  : List (Edge a)}
        -> (branch  : CFG vertex (Defined rs) (Defined rs'))
        -> (node    : CFG vertex (Defined $ ls ++ rs') outs)
        ->            CFG vertex (Defined $ ls ++ rs) outs
  rmerge branch node = (Empty |-| branch) *-> node

  export
  imap : {0 vertex : Vertex a}
          -> {ins : Neighbors a}

          -> ({outs : Neighbors a} -> vertex v Undefined outs -> vertex v ins outs)
          -> CFG vertex (Undefined v) gouts
          -> CFG vertex (fromVIn ins v) gouts

  imap f (SingleVertex {vins = Nothing} v)  = SingleVertex (f v)
  imap f (Series g g')                      = Series (imap f g) g'
  
  imap f (OFlip g)                          = OFlip (imap f g)
  
  imap f Empty                              impossible
  imap f (SingleVertex {vins = Just ins} v) impossible
  imap f (Cycle node loop)                  impossible
  imap f (Parallel g g')                    impossible
  imap f (IFlip g)                          impossible
  
  export
  omap : {0 vertex : Vertex a}
          -> {outs : Neighbors a}

          -> ({ins : Neighbors a} -> vertex v ins Undefined -> vertex v ins outs)
          -> CFG vertex gins (Undefined v)
          -> CFG vertex gins (fromVOut v outs)

  omap f (SingleVertex {vouts = Nothing} v)   = SingleVertex (f v)
  omap f (Series g g')                        = Series g (omap f g')
  omap f (IFlip g)                            = IFlip (omap f g)
  
  omap f Empty                                impossible
  omap f (SingleVertex {vouts = Just outs} v) impossible
  omap f (Cycle node loop)                    impossible
  omap f (Parallel g g')                      impossible
  omap f (OFlip g)                            impossible

  export
  connect : (impl : Connectable vertex)
         => CFG vertex ins (Undefined v)
         -> CFG vertex (Undefined v) outs
         -> CFG vertex ins outs

  connect (SingleVertex {vouts = Nothing} v)  g   = imap (cnct @{impl} v) g
  connect (Series g g')                       g'' = Series g (connect g' g'')
  connect (IFlip g)                           g'  = IFlip (connect g g')

  connect Empty                                 g' impossible
  connect (SingleVertex {vouts = Just outs} v)  g' impossible
  connect (Cycle node loop)                     g' impossible
  connect (Parallel g g')                       g' impossible
  connect (OFlip g)                             g' impossible

  infixr 5 *~>
  export
  (*~>) : (impl : Connectable vertex)
       => CFG vertex ins (Undefined v)
       -> CFG vertex (Undefined v) outs
       -> CFG vertex ins outs
  (*~>) = connect
  

  export
  initGraph : {0 vertex : Vertex a}
           -> vertex v Undefined Undefined
           -> CFG vertex (Undefined v) (Undefined v)
  initGraph v = SingleVertex v


  export
  iget : {0 vertex : Vertex a}
      -> ({outs : Neighbors a} -> vertex v Undefined outs -> b)
      -> CFG vertex (Undefined v) gouts
      -> b
  iget f (SingleVertex {vins = Nothing} v)  = f v
  iget f (Series g g')                      = iget f g
  iget f (OFlip g)                          = iget f g
  
  iget f Empty                              impossible
  iget f (SingleVertex {vins = Just ins} v) impossible
  iget f (Cycle node loop)                  impossible
  iget f (Parallel g g')                    impossible
  iget f (IFlip g)                          impossible

  export
  oget : {0 vertex : Vertex a}
      -> ({ins : Neighbors a} -> vertex v ins Undefined -> b)
      -> CFG vertex gins (Undefined v)
      -> b

  oget f (SingleVertex {vouts = Nothing} v)   = f v
  oget f (Series g g')                        = oget f g'
  oget f (IFlip g)                            = oget f g
  
  oget f Empty                                impossible
  oget f (SingleVertex {vouts = Just outs} v) impossible
  oget f (Cycle node loop)                    impossible
  oget f (Parallel g g')                      impossible
  oget f (OFlip g)                            impossible



  export
  vmap : {0 a : Type}
      -> {0 vertex, vertex' : Vertex a}
      -> {0 ins, outs : Edges a}
      -> ( {0 v : a}
        -> {vins, vouts : Neighbors a}
        -> vertex v vins vouts
        -> vertex' v vins vouts
         )
      -> CFG vertex ins outs
      -> CFG vertex' ins outs

  vmap f Empty              = Empty
  vmap f (SingleVertex v)   = SingleVertex (f v)
  vmap f (Cycle node loop)  = Cycle (vmap f node) (vmap f loop)
  vmap f (Series g g')      = Series (vmap f g) (vmap f g')
  vmap f (Parallel g g')    = Parallel (vmap f g) (vmap f g')
  vmap f (IFlip g)          = IFlip (vmap f g)
  vmap f (OFlip g)          = OFlip (vmap f g)

  export
  vmap' : {0 a : Type}
      -> {0 vertex, vertex' : Vertex a}
      -> {0 ins, outs : List (Edge a)}
      -> ( {0 v : a}
        -> {vins, vouts : List a}
        -> vertex v (Just vins) (Just vouts)
        -> vertex' v (Just vins) (Just vouts)
         )
      -> CFG vertex (Defined ins) (Defined outs)
      -> CFG vertex' (Defined ins) (Defined outs)

  vmap' f (SingleVertex {vins = Just ins, vouts = Just outs} v) = SingleVertex (f v)
  vmap' f Empty             = Empty
  vmap' f (Cycle node loop) = Cycle (vmap' f node) (vmap' f loop)
  vmap' f (Series g g')     = Series (vmap' f g) (vmap' f g')
  vmap' f (Parallel g g')   = Parallel (vmap' f g) (vmap' f g')
  vmap' f (IFlip g)         = IFlip (vmap' f g)
  vmap' f (OFlip g)         = OFlip (vmap' f g)

  vmap' f (SingleVertex {vins  = Nothing} v) impossible
  vmap' f (SingleVertex {vouts = Nothing} v) impossible
  -}
