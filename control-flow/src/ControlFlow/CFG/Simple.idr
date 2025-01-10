||| This module contains a representation of a control-flow graph - a
||| simplified version if `CFG` that permits graphs to be incomplete, but not
||| the vertices.
module ControlFlow.CFG.Simple

import public ControlFlow.Edge

namespace Vertex
  ||| Neighbors of a vertex
  public export
  Neighbors : Type -> Type
  Neighbors a = List a

  public export
  Closed : Neighbors a
  Closed = []

  public export
  Single : a -> Neighbors a
  Single x = [x]

  ||| A constructor of verteices of a directed graph
  ||| @ a    the type of vertex identifiers
  ||| @ v    the identifier              of the vertex
  ||| @ ins  the inputs  (in-neighbors)  of the vertex
  ||| @ outs the outputs (out-neighbors) of the vertex
  public export
  Vertex : Type -> Type
  Vertex a = (v : a) -> (ins : Neighbors a) -> (outs : Neighbors a) -> Type

namespace Graph

  ||| Input or output edges of an incomplete graph
  ||| @ a the type of vertex identifiers
  public export
  Edges : Type -> Type
  Edges a = List (Edge a)

  public export
  Closed : Edges a
  Closed = []

  public export
  Single : a -> a -> Edges a
  Single from to = [from ~> to]

  ||| A potentially incomplete control flow graph.
  ||| @ ins    edges from "to be defined" vertices to vertices in the graph
  ||| @ outs   edges from vertices in the graph to "to be defined" vertices
  ||| @ vertex constructor of vertex types.
  public export
  data CFG : (vertex : Vertex a) -> (ins : Edges a) -> (outs : Edges a) -> Type where

    ||| An empty graph
    Empty : CFG vertex edges edges

    ||| A singleton graph - a graph containing a single vertex
    SingleVertex
       : {0 vertex : Vertex a}
      -> {vins, vouts : Neighbors a}
      -> vertex v vins vouts
      -> CFG vertex (vins ~~> v) (v ~>> vouts)

    ||| A graph that represents a while loop
    ||| @ node the graph in which the while condition is computed
    ||| @ loop the body of the loop
    Cycle
       : {ins, outs, loopIns, loopOuts : Edges a}
      -> (node : CFG vertex (ins ++ loopOuts) (loopIns ++ outs))
      -> (loop : CFG vertex loopIns loopOuts)
      -> CFG vertex ins outs

    ||| A sequential connection of two graphs
    ||| The output vertices of one (`pre`) are being connected to the input
    ||| vertices of the other (`post`)
    ||| @ pre  the predecessor of `post`
    ||| @ post the successor   of `pre`
    Series
       : (pre  : CFG vertex ins edges)
      -> (post : CFG vertex edges outs)
      -> CFG vertex ins outs

    ||| A parallel connection of graphs
    ||| Two graphs are combined into one without any connections beetween them
    ||| The result has the inputs and outputs of both
    ||| @ left  the left sub-graph
    ||| @ right the right sub-graph
    Parallel
       : (left  : CFG vertex ins  outs)
      -> (right : CFG vertex ins' outs')
      -> CFG vertex (ins ++ ins') (outs ++ outs')

    -- TODO: consider removing these constructors
    ||| Used to flip the inputs of a graph to make it connectable with another
    IFlip
       : {ins, ins' : Edges a}
      -> CFG vertex (ins ++ ins') outs
      -> CFG vertex (ins' ++ ins) outs

    ||| Used to flip the outputs of a graph to make it connectable with another
    OFlip
       : {outs, outs' : List (Edge a)}
      -> CFG vertex ins (outs ++ outs')
      -> CFG vertex ins (outs' ++ outs)

  export infixr 4 |-|
  ||| Alias for `Parallel`
  public export
  (|-|)
     : CFG vertex ins           outs
    -> CFG vertex ins'          outs'
    -> CFG vertex (ins ++ ins') (outs ++ outs')
  (|-|) = Parallel

  export infixr 5 *->
  ||| Alias for `Series`
  public export
  (*->)
     : CFG vertex ins edges
    -> CFG vertex edges outs
    -> CFG vertex ins outs
  (*->) = Series


  public export
  prepend
     : {0 vertex : Vertex a}
    -> {vins, vouts : Neighbors a}
    -> vertex v vins vouts
    -> CFG vertex (v ~>> vouts) gouts
    -> CFG vertex (vins ~~> v) gouts
  prepend v g = (SingleVertex v) *-> g

  public export
  append
     : {vins, vouts : Neighbors a}

    -> CFG vertex gins (vins ~~> v)
    -> vertex v vins vouts
    -> CFG vertex gins (v ~>> vouts)
  append g v = g *-> (SingleVertex v)

  branch
     : {0 vertex : Vertex a}
    -> {vins : Neighbors a}
    -> {w, w' : a}

    -> (pre   : vertex v vins [w, w'])
    -> (left  : CFG vertex [v ~> w]  louts)
    -> (right : CFG vertex [v ~> w'] routs)
    -> CFG vertex (vins ~~> v) (louts ++ routs)
  branch pre left right = pre `prepend` (left |-| right)

  fullBranch
     : {0 vertex : Vertex a}
    -> {vins, vouts : Neighbors a}
    -> {w, w', u, u' : a}

    -> (pre   : vertex v vins [w, w'])
    -> (left  : CFG vertex [v ~> w]  [u  ~> t])
    -> (right : CFG vertex [v ~> w'] [u' ~> t])
    -> (post  : vertex t [u, u'] vouts)
    -> CFG vertex (vins ~~> v) (t ~>> vouts)
  fullBranch pre left right post = (branch pre left right) `append` post

  ||| A partial sequential connection of two graphs
  ||| The left outputs of the predecessor are connected with all inputs of
  ||| the successor
  ||| @ node   the           predecessor of `branch`
  ||| @ branch the (partial) successor   of `node`
  ||| @ ls     the left  outputs of `node` / the inputs of `branch`
  ||| @ rs     the right outputs of `node`
  public export
  lbranch
     : {ls, rs : List (Edge a)}
    -> (node   : CFG vertex ins (ls ++ rs))
    -> (branch : CFG vertex ls ls')
    ->           CFG vertex ins (ls' ++ rs)
  lbranch node branch = node *-> (branch |-| Empty)

  ||| A partial sequential connection of two graphs
  ||| The right outputs of the predecessor are connected with all inputs of
  ||| the successor
  ||| @ node   the           predecessor of `branch`
  ||| @ branch the (partial) successor   of `node`
  ||| @ ls     the left  outputs of `node`
  ||| @ rs     the right outputs of `node` / the inputs of `branch`
  public export
  rbranch
     : {ls, rs : List (Edge a)}
    -> (node   : CFG vertex ins (ls ++ rs))
    -> (branch : CFG vertex rs rs')
    ->           CFG vertex ins (ls ++ rs')
  rbranch node branch = node *-> (Empty |-| branch)

  ||| A partial sequential connection of two graphs
  ||| All outputs of the predecessor are connected with the left inputs of
  ||| the successor
  ||| @ branch the           predecessor of `node`
  ||| @ node   the (partial) successor   of `branch`
  ||| @ ls'    the left  inputs of `node` / the outputs of `branch`
  ||| @ rs     the right inputs of `node`
  public export
  lmerge
     : {ls, rs : Edges a}
    -> (branch : CFG vertex ls ls')
    -> (node   : CFG vertex (ls' ++ rs) outs)
    ->           CFG vertex (ls  ++ rs) outs
  lmerge branch node = (branch |-| Empty) *-> node

  ||| A partial sequential connection of two graphs
  ||| All outputs of the predecessor are connected with the right inputs of
  ||| the successor
  ||| @ branch the           predecessor of `node`
  ||| @ node   the (partial) successor   of `branch`
  ||| @ ls     the left  inputs of `node`
  ||| @ rs'    the right inputs of `node` / the outputs of `branch`
  public export
  rmerge
     : {ls, rs : Edges a}
    -> (branch : CFG vertex rs rs')
    -> (node   : CFG vertex (ls ++ rs') outs)
    ->           CFG vertex (ls ++ rs)  outs
  rmerge branch node = (Empty |-| branch) *-> node

  export
  initGraph
     : {0 vertex : Vertex a}
    -> {ins, outs : Neighbors a}
    -> vertex v ins outs
    -> CFG vertex (ins ~~> v) (v ~>> outs)
  initGraph v = SingleVertex v

  ||| Apply a function to all vertices in a grpaph
  export
  vmap
     : {0 a : Type}
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
