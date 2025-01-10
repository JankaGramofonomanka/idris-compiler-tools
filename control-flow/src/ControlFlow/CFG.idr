||| This module contains a representation of a control-flow graph that aims to
||| enforce the correctness of jumps between vertices of graphs, i.e., blocks
||| of code.
||| The graph model permits both graphs and vertices that are incomplete and
||| facilitates easy composition of such graphs when they are compatible.
|||
||| A graph / vertex is incomplete when vertices / insrtuctions need to be
||| added to it in order for it to be a valid function body / basic block.
||| For example a graph that contains only the following pseudo-code block:
||| ```
||| L0: x = call func ()
|||     jump L1
||| ```
||| is incomplete because the code block ends with a jump to the block `L1` but
||| `L1` is not in the graph.
||| An example of a nincomplete vertex is the following:
||| ```
||| L0: x = call func ()
||| ```
||| because it does not end with a jump nor with a return instruction.
|||
||| In this model, vertices and graphs can be incomplete at the beginning or at
||| the end (or both). In other words, graphs / vertices can be completed only
||| by prepending or appending vertices / instructions to them.
module ControlFlow.CFG

import public ControlFlow.Edge

{-
TODO:
Consider singling out `Just []` / `Defined []` and use `List1` instead of `List`
-}

namespace Vertex
  ||| Neighbors of a vertex
  ||| * `Just l` represents neighbors of a vertex that is complete at the
  |||    relevant end (beginning or end)
  ||| * `Nothing` is used to mark that a vertex is incomplete at a given end
  ||| @ a the type of vertex identifiers
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

  ||| A constructor of verteices of a directed graph
  ||| @ a    the type of vertex identifiers
  ||| @ v    the identifier              of the vertex
  ||| @ ins  the inputs  (in-neighbors)  of the vertex
  ||| @ outs the outputs (out-neighbors) of the vertex
  public export
  Vertex : Type -> Type
  Vertex a = (v : a) -> (ins : Neighbors a) -> (outs : Neighbors a) -> Type

  ||| Types of vertices that allow merging undefined vertices
  public export
  interface Connectable (0 vertex : Vertex a) where
    ||| Merge two vertices undefined on opposite ends
    cnct : vertex v ins Undefined
        -> vertex v Undefined outs
        -> vertex v ins outs

namespace Graph

  ||| Input or output edges of an incomplete graph
  ||| @ a the type of vertex identifiers
  public export
  data Edges a
    = ||| `Undefined v` is used to mark that a graph has, at the a given end,
      ||| one incomplete vertex labeled `v`.
      Undefined a
    | ||| `Defined edges` represents the input or output edges of a graph in a
      ||| case when it has no incomplete vertices at the relevant end.
      |||
      ||| `edges` is then the list of edges whose destinations (origins) are in
      ||| the graph but their origins (destinations) are not.
      Defined (List (Edge a))

  public export
  Closed : Edges a
  Closed = Defined []

  public export
  Single : a -> a -> Edges a
  Single from to = Defined [from ~> to]

  ||| Given an identifier of a vertex and its out-neighbors return the output
  ||| edges of that vertex
  ||| @ v    the vertex identifier
  ||| @ outs the out-neighbors of the vertex
  public export
  fromVOut : (v : a) -> (outs : Neighbors a) -> Edges a
  fromVOut v Nothing      = Undefined v
  fromVOut v (Just outs)  = Defined (v ~>> outs)

  ||| Given an identifier of a vertex and its in-neighbors return the input
  ||| edges of that vertex
  ||| @ v   the vertex identifier
  ||| @ ins the in-neighbors of the vertex
  public export
  fromVIn : (ins : Neighbors a) -> (v : a) -> Edges a
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

  ||| A potentially incomplete control flow graph.
  ||| @ ins    edges from "to be defined" vertices to vertices in the graph
  ||| @ outs   edges from vertices in the graph to "to be defined" vertices
  ||| @ vertex constructor of vertex types.
  public export
  data CFG : (vertex : Vertex a) -> (ins : Edges a) -> (outs : Edges a) -> Type where

    ||| An empty graph
    Empty : CFG vertex (Defined edges) (Defined edges)

    ||| A singleton graph - a graph containing a single vertex
    SingleVertex
       : {0 vertex : Vertex a}
      -> {vins, vouts : Neighbors a}
      -> vertex v vins vouts
      -> CFG vertex (fromVIn vins v) (fromVOut v vouts)

    -- TODO consider `CFG (ins ++ edges) (outs ++ edges) -> CFG ins outs` instead of this
    ||| A graph that represents a while loop
    ||| @ node the graph in which the while condition is computed
    ||| @ loop the body of the loop
    Cycle
       : {ins, outs, loopIns, loopOuts : List (Edge a)}
      -> (node : CFG vertex (Defined $ ins ++ loopOuts) (Defined $ loopIns ++ outs))
      -> (loop : CFG vertex (Defined loopIns) (Defined loopOuts))
      -> CFG vertex (Defined ins) (Defined outs)

    ||| A sequential connection of two graphs
    ||| The output vertices of one (`pre`) are being connected to the input
    ||| vertices of the other (`post`)
    ||| @ pre  the predecessor of `post`
    ||| @ post the successor   of `pre`
    Series
       : (pre  : CFG vertex ins (Defined edges))
      -> (post : CFG vertex (Defined edges) outs)
      -> CFG vertex ins outs

    ||| A parallel connection of graphs
    ||| Two graphs are combined into one without any connections beetween them
    ||| The result has the inputs and outputs of both
    ||| @ left  the left sub-graph
    ||| @ right the right sub-graph
    Parallel
       : (left  : CFG vertex (Defined ins)  (Defined outs))
      -> (right : CFG vertex (Defined ins') (Defined outs'))
      -> CFG vertex (Defined $ ins ++ ins') (Defined $ outs ++ outs')

    -- TODO: consider removing these constructors
    ||| Used to flip the inputs of a graph to make it connectable with another
    IFlip
       : {ins, ins' : List (Edge a)}
      -> CFG vertex (Defined $ ins ++ ins') outs
      -> CFG vertex (Defined $ ins' ++ ins) outs

    ||| Used to flip the outputs of a graph to make it connectable with another
    OFlip
       : {outs, outs' : List (Edge a)}
      -> CFG vertex ins (Defined $ outs ++ outs')
      -> CFG vertex ins (Defined $ outs' ++ outs)

  export infixr 4 |-|
  ||| Alias for `Parallel`
  public export
  (|-|)
     : CFG vertex (Defined ins)           (Defined outs)
    -> CFG vertex (Defined ins')          (Defined outs')
    -> CFG vertex (Defined $ ins ++ ins') (Defined $ outs ++ outs')
  (|-|) = Parallel

  export infixr 5 *->
  ||| Alias for `Series`
  public export
  (*->)
     : CFG vertex ins (Defined edges)
    -> CFG vertex (Defined edges) outs
    -> CFG vertex ins outs
  (*->) = Series


  public export
  prepend
     : {0 vertex : Vertex a}
    -> {vins : Neighbors a}
    -> {vouts : List a}
    -> vertex v vins (Just vouts)
    -> CFG vertex (Defined $ v ~>> vouts) gouts
    -> CFG vertex (fromVIn vins v) gouts
  prepend v g = (SingleVertex v) *-> g

  public export
  append
     : {vins : List a}
    -> {vouts : Neighbors a}

    -> CFG vertex gins (Defined $ vins ~~> v)
    -> vertex v (Just vins) vouts
    -> CFG vertex gins (fromVOut v vouts)
  append g v = g *-> (SingleVertex v)

  branch
     : {0 vertex : Vertex a}
    -> {vins : Neighbors a}
    -> {w, w' : a}

    -> (pre   : vertex v vins (Just [w, w']))
    -> (left  : CFG vertex (Single v w)  (Defined louts))
    -> (right : CFG vertex (Single v w') (Defined routs))
    -> CFG vertex (fromVIn vins v) (Defined $ louts ++ routs)
  branch pre left right = pre `prepend` (left |-| right)

  fullBranch
     : {0 vertex : Vertex a}
    -> {vins, vouts : Neighbors a}
    -> {w, w', u, u' : a}

    -> (pre    : vertex v vins (Just [w, w']))
    -> (left   : CFG vertex (Single v w)  (Single u t))
    -> (right  : CFG vertex (Single v w') (Single u' t))
    -> (post   : vertex t (Just [u, u']) vouts)
    -> CFG vertex (fromVIn vins v) (fromVOut t vouts)
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
    -> (node   : CFG vertex ins (Defined $ ls ++ rs))
    -> (branch : CFG vertex (Defined ls) (Defined ls'))
    ->           CFG vertex ins (Defined $ ls' ++ rs)
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
    -> (node   : CFG vertex ins (Defined $ ls ++ rs))
    -> (branch : CFG vertex (Defined rs) (Defined rs'))
    ->           CFG vertex ins (Defined $ ls ++ rs')
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
     : {ls, rs  : List (Edge a)}
    -> (branch  : CFG vertex (Defined ls) (Defined ls'))
    -> (node    : CFG vertex (Defined $ ls' ++ rs) outs)
    ->            CFG vertex (Defined $ ls  ++ rs) outs
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
     : {ls, rs  : List (Edge a)}
    -> (branch  : CFG vertex (Defined rs) (Defined rs'))
    -> (node    : CFG vertex (Defined $ ls ++ rs') outs)
    ->            CFG vertex (Defined $ ls ++ rs) outs
  rmerge branch node = (Empty |-| branch) *-> node

  ||| Apply a function to the undefined input vertex
  export
  imap
     : {0 vertex : Vertex a}
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

  ||| Apply a function to the undefined output vertex
  export
  omap
     : {0 vertex : Vertex a}
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

  ||| Connect sequentialy two graphs that end and begin with an undefined vertex
  |||
  ||| Connects the two grapgs by merges the output vertex of the predecessor
  ||| with the input vertex of the successor
  export
  connect
     : (impl : Connectable vertex)
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

  export infixr 5 *~>
  ||| Alias for `connect`
  export
  (*~>)
     : (impl : Connectable vertex)
    => CFG vertex ins (Undefined v)
    -> CFG vertex (Undefined v) outs
    -> CFG vertex ins outs
  (*~>) = connect


  export
  initGraph
     : {0 vertex : Vertex a}
    -> vertex v Undefined Undefined
    -> CFG vertex (Undefined v) (Undefined v)
  initGraph v = SingleVertex v

  ||| Get data from the undefined input vertex
  export
  iget
     : {0 vertex : Vertex a}
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

  ||| Get data from the undefined output vertex
  export
  oget
     : {0 vertex : Vertex a}
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

  ||| Apply a function to all vertices in a fully defined graph
  |||
  ||| Like `vmap` but all vertices in the graph are defined an thus the applied
  ||| function works only for defined vertices
  export
  vmap'
     : {0 a : Type}
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
