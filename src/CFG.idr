module CFG

import Theory


namespace Vertex  
  -- `Neighbors a` - neighbors of a vertex with identifier of type `a`
  public export
  Neighbors : Type -> Type
  Neighbors a = List a

  public export
  Closed : Neighbors a
  Closed = []

  public export
  Single : a -> Neighbors a
  Single x = [x]

  {-
  `Vertex a` - constructor of verteices of a directed graph, with identifiers
  of type `a`

  if `vertex : Vertex a` then `vertex l ins outs` is a type of vertex with
  identifier `l`, inputs `ins` and outputs `outs`.
  -}
  public export
  Vertex : Type -> Type
  Vertex a = a -> Neighbors a -> Neighbors a -> Type

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
  -}
  public export
  Edges : Type -> Type
  Edges a = List (Edge a)

  public export
  Closed : Edges a
  Closed = []

  public export
  Single : a -> a -> Edges a
  Single from to = [from ~> to]


  infix 8 ~~>, ~>>, <~~, <<~

  public export
  (~~>) : List v -> v -> Edges v
  vs ~~> v = map (~> v) vs

  public export
  (~>>) : v -> List v -> Edges v
  v ~>> vs = map (v ~>) vs

  public export
  (<~~) : v -> List v -> Edges v
  (<~~) = flip (~~>)
  
  public export
  (<<~) : List v -> v -> Edges v
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

  {-
  A potentially incomplete control flow graph.
  `CFG vertex ins outs` is a graph where:
    `ins`     - edges from "to be defined" vertices to vertices in the graph
    `outs`    - edges from vertices in the graph to "to be defined" vertices
    `vertex`  - constructor of vertex types.
  -}
  public export
  data CFG : Vertex a -> Edges a -> Edges a -> Type where

    Empty : CFG vertex edges edges
    
    SingleVertex : {0 vertex : Vertex a}
                -> {vins, vouts : Neighbors a}
                -> vertex v vins vouts
                -> CFG vertex (vins ~~> v) (v ~>> vouts)
    
    -- TODO consider `CFG (ins ++ edges) (outs ++ edges) -> CFG ins outs` instead of this
    Cycle : {ins, outs, loopIns, loopOuts : Edges a}
         -> (node : CFG vertex (ins ++ loopOuts) (loopIns ++ outs))
         -> (loop : CFG vertex loopIns loopOuts)
         -> CFG vertex ins outs
    
    Series : CFG vertex ins   edges
          -> CFG vertex edges outs
          -> CFG vertex ins   outs
    
    
    Parallel : CFG vertex ins           outs
            -> CFG vertex ins'          outs'
            -> CFG vertex (ins ++ ins') (outs ++ outs')
    
    
    -- TODO: consider removing these constructors
    IFlip : {ins, ins' : Edges a}
         -> CFG vertex (ins ++ ins') outs
         -> CFG vertex (ins' ++ ins) outs
    
    OFlip : {outs, outs' : Edges a}
         -> CFG vertex ins (outs ++ outs')
         -> CFG vertex ins (outs' ++ outs)
  
  infixr 4 |-|
  public export
  (|-|) : CFG vertex ins           outs
       -> CFG vertex ins'          outs'
       -> CFG vertex (ins ++ ins') (outs ++ outs')
  (|-|) = Parallel

  infixr 5 *->
  public export
  (*->) : CFG vertex ins edges
       -> CFG vertex edges outs
       -> CFG vertex ins outs
  (*->) = Series
          

  public export
  prepend : {0 vertex : Vertex a}
         -> {vins : Neighbors a}
         -> {vouts : List a}
         -> vertex v vins vouts
         -> CFG vertex (v ~>> vouts) gouts
         -> CFG vertex (vins ~~> v) gouts
  prepend v g = (SingleVertex v) *-> g

  public export
  append : {vins : List a}
        -> {vouts : Neighbors a}
        
        -> CFG vertex gins (vins ~~> v)
        -> vertex v (vins) vouts
        -> CFG vertex gins (v ~>> vouts)
  append g v = g *-> (SingleVertex v)
  
  branch : {0 vertex : Vertex a}
        -> {vins : Neighbors a}
        -> {w, w' : a}
        
        -> (pre   : vertex v vins [w, w'])
        -> (left  : CFG vertex (Single v w)  louts)
        -> (right : CFG vertex (Single v w') routs)
        -> CFG vertex (vins ~~> v) (louts ++ routs)
  branch pre left right = pre `prepend` (left |-| right)

  fullBranch : {0 vertex : Vertex a}
            -> {vins, vouts : Neighbors a}
            -> {w, w', u, u' : a}

            -> (pre    : vertex v vins [w, w'])
            -> (left   : CFG vertex (Single v w)  (Single u t))
            -> (right  : CFG vertex (Single v w') (Single u' t))
            -> (post   : vertex t [u, u'] vouts)
            -> CFG vertex (vins ~~> v) (t ~>> vouts)
  fullBranch pre left right post = (branch pre left right) `append` post

  public export  
  lbranch : {ls, rs : List (Edge a)}
         -> (node   : CFG vertex ins (ls ++ rs))
         -> (branch : CFG vertex ls ls')
         ->           CFG vertex ins (ls' ++ rs)
  lbranch node branch = node *-> (branch |-| Empty)

  public export
  rbranch : {ls, rs : List (Edge a)}
         -> (node   : CFG vertex ins (ls ++ rs))
         -> (branch : CFG vertex rs rs')
         ->           CFG vertex ins (ls ++ rs')
  rbranch node branch = node *-> (Empty |-| branch)

  public export
  lmerge : {ls, rs  : List (Edge a)}
        -> (branch  : CFG vertex ls ls')
        -> (node    : CFG vertex (ls' ++ rs) outs)
        ->            CFG vertex (ls ++ rs) outs
  lmerge branch node = (branch |-| Empty) *-> node

  public export
  rmerge : {ls, rs  : List (Edge a)}
        -> (branch  : CFG vertex rs rs')
        -> (node    : CFG vertex (ls ++ rs') outs)
        ->            CFG vertex (ls ++ rs) outs
  rmerge branch node = (Empty |-| branch) *-> node




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
