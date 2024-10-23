module CFG.Interface

import Data.DList
import Theory

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

  infix 6 ~>, <~

  ||| An edge between vertices
  ||| @ a the type of vertex identifiers
  public export
  data Edge a
    = ||| `v ~> w` - an edge from `v` to `w`
      (~>) a a

  public export
  (<~) : a -> a -> Edge a
  (<~) = flip (~>)

  public export
  Dest : Edge a -> a
  Dest (from ~> to) = to

  public export
  Origin : Edge a -> a
  Origin (from ~> to) = from


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


  infix 8 ~~>, ~>>, <~~, <<~

  ||| A *collection* of `vs` by `v`
  public export
  (~~>) : (vs : List a) -> (v : a) -> List (Edge a)
  vs ~~> v = map (~> v) vs

  ||| A *distribution* of `v` to `vs`
  public export
  (~>>) : (v : a) -> (vs : List a) -> List (Edge a)
  v ~>> vs = map (v ~>) vs

  ||| Flipped `(~~>)`
  public export
  (<~~) : (v : a) -> (vs : List a) -> List (Edge a)
  (<~~) = flip (~~>)

  ||| Flipped `(~>>)`
  public export
  (<<~) : (vs : List a) -> (v : a) -> List (Edge a)
  (<<~) = flip (~>>)

  |||    A collection    of a   concatenation of two   lists by `v`
  ||| is a concatenation of the collections   of these lists by `v`
  export
  collect_concat : (v : a) -> (vs, ws : List a) -> (vs ++ ws) ~~> v = vs ~~> v ++ ws ~~> v
  collect_concat v vs ws = map_concat {f = (~> v)} vs ws

  |||    A distribution  of `v` to a   concatenation        of two   lists
  ||| is a concatenation        of the distributions of `v` to these lists
  export
  distribute_concat : (v : a) -> (vs, ws : List a) -> v ~>> (vs ++ ws) = v ~>> vs ++ v ~>> ws
  distribute_concat v vs ws = map_concat {f = (v ~>)} vs ws

  ||| A special case of `collect_concat` where `ws` is a singleton
  export
  collect_append : (v : a) -> (vs : List a) -> (w : a) -> (vs ++ [w]) ~~> v = vs ~~> v ++ [w ~> v]
  collect_append v vs w = collect_concat v vs [w]

  ||| A special case of `distribute_concat` where `ws` is a singleton
  export
  distribute_append : (v : a) -> (vs : List a) -> (w : a) -> v ~>> (vs ++ [w]) = v ~>> vs ++ [v ~> w]
  distribute_append v vs w = distribute_concat v vs [w]

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
  TODO: Consider adding an `data` parameter to `cfg` that would be the type of
  data that would be stored alongside vertices.

  The `data` could be:
    - the values of variables
    - variables that were changed
    - variables that are live
  -}

  CFGSig : Type -> Type
  CFGSig a = Vertex a -> Edges a -> Edges a -> Type

  ||| A potentially incomplete control flow graph.
  ||| @ ins    edges from "to be defined" vertices to vertices in the graph
  ||| @ outs   edges from vertices in the graph to "to be defined" vertices
  ||| @ vertex constructor of vertex types.
  public export
  interface CFG a (0 cfg : CFGSig a) where

    ||| An empty graph
    empty
       : {vertex : Vertex a}
      -> {edges : List (Edge a)}
      -> cfg vertex (Defined edges) (Defined edges)

    ||| A singleton graph - a graph containing a single vertex
    singleVertex : {0 v : a}
                -> {0 vertex : Vertex a}
                -> {vins, vouts : Neighbors a}
                -> vertex v vins vouts
                -> cfg vertex (fromVIn vins v) (fromVOut v vouts)

    -- TODO consider `cfg (ins ++ edges) (outs ++ edges) -> cfg ins outs` instead of this
    ||| A graph that represents a while loop
    ||| @ node the graph in which the while condition is computed
    ||| @ loop the body of the loop
    cycle : {0 vertex : Vertex a}
         -> {ins, outs, loopIns, loopOuts : List (Edge a)}
         -> (node : cfg vertex (Defined $ ins ++ loopOuts) (Defined $ loopIns ++ outs))
         -> (loop : cfg vertex (Defined loopIns) (Defined loopOuts))
         -> cfg vertex (Defined ins) (Defined outs)

    ||| A sequential connection of two graphs
    ||| The output vertices of one (`pre`) are being connected to the input
    ||| vertices of the other (`post`)
    ||| @ pre  the predecessor of `post`
    ||| @ post the successor   of `pre`
    series
       : {0 vertex : Vertex a}
      -> {0 ins, outs : Edges a}
      -> {0 edges : List (Edge a)}
      -> (pre  : cfg vertex ins (Defined edges))
      -> (post : cfg vertex (Defined edges) outs)
      -> cfg vertex ins outs

    ||| A parallel connection of graphs
    ||| Two graphs are combined into one without any connections beetween them
    ||| The result has the inputs and outputs of both
    ||| @ left  the left sub-graph
    ||| @ right the right sub-graph
    parallel
       : {0 vertex : Vertex a}
      -> {0 ins, ins', outs, outs' : List (Edge a)}
      -> (left  : cfg vertex (Defined ins)  (Defined outs))
      -> (right : cfg vertex (Defined ins') (Defined outs'))
      -> cfg vertex (Defined $ ins ++ ins') (Defined $ outs ++ outs')

    -- TODO: consider removing these constructors
    ||| Used to flip the inputs of a graph to make it connectable with another
    iflip
       : {0 vertex : Vertex a}
      -> {0 outs : Edges a}
      -> {ins, ins' : List (Edge a)}
      -> cfg vertex (Defined $ ins ++ ins') outs
      -> cfg vertex (Defined $ ins' ++ ins) outs

    ||| Used to flip the outputs of a graph to make it connectable with another
    oflip
       : {0 vertex : Vertex a}
      -> {0 ins : Edges a}
      -> {outs, outs' : List (Edge a)}
      -> cfg vertex ins (Defined $ outs ++ outs')
      -> cfg vertex ins (Defined $ outs' ++ outs)

    ||| Apply a function to the undefined input vertex
    imap
       : {0 v : a}
      -> {0 vertex : Vertex a}
      -> {ins : Neighbors a}
      -> {0 gouts : Edges a}

      -> ({outs : Neighbors a} -> vertex v Undefined outs -> vertex v ins outs)
      -> cfg vertex (Undefined v) gouts
      -> cfg vertex (fromVIn ins v) gouts

    ||| Apply a function to the undefined output vertex
    omap
       : {0 v : a}
      -> {0 vertex : Vertex a}
      -> {0 gins : Edges a}
      -> {outs : Neighbors a}

      -> ({ins : Neighbors a} -> vertex v ins Undefined -> vertex v ins outs)
      -> cfg vertex gins (Undefined v)
      -> cfg vertex gins (fromVOut v outs)

    ||| Connect sequentialy two graphs that end and begin with an undefined vertex
    |||
    ||| Connects the two grapgs by merges the output vertex of the predecessor
    ||| with the input vertex of the successor
    connect
       : {0 v : a}
      -> {0 vertex : Vertex a}
      -> Connectable vertex
      => {0 ins, outs : Edges a}
      -> cfg vertex ins (Undefined v)
      -> cfg vertex (Undefined v) outs
      -> cfg vertex ins outs

    ||| Get data from the undefined input vertex
    iget
       : {0 v : a}
      -> {0 vertex : Vertex a}
      -> {0 gouts : Edges a}
      -> ({outs : Neighbors a} -> vertex v Undefined outs -> b)
      -> cfg vertex (Undefined v) gouts
      -> b

    ||| Get data from the undefined output vertex
    oget
       : {0 v : a}
      -> {0 vertex : Vertex a}
      -> {0 gins : Edges a}
      -> ({ins : Neighbors a} -> vertex v ins Undefined -> b)
      -> cfg vertex gins (Undefined v)
      -> b

    ||| Apply a function to all vertices in a grpaph
    vmap
       : {0 vertex, vertex' : Vertex a}
      -> {0 ins, outs : Edges a}
      -> ( {0 v : a}
        -> {vins, vouts : Neighbors a}
        -> vertex v vins vouts
        -> vertex' v vins vouts
         )
      -> cfg vertex ins outs
      -> cfg vertex' ins outs

    ||| Apply a function to all vertices in a fully defined graph
    |||
    ||| Like `vmap` but all vertices in the graph are defined an thus the applied
    ||| function works only for defined vertices
    vmap'
       : {0 vertex, vertex' : Vertex a}
      -> {0 ins, outs : List (Edge a)}
      -> ( {0 v : a}
        -> {vins, vouts : List a}
        -> vertex v (Just vins) (Just vouts)
        -> vertex' v (Just vins) (Just vouts)
        )
      -> cfg vertex (Defined ins) (Defined outs)
      -> cfg vertex' (Defined ins) (Defined outs)

  export infixr 4 |-|
  ||| Alias for `parallel`
  public export
  (|-|)
     : (impl : CFG a cfg)
    => cfg vertex (Defined ins)           (Defined outs)
    -> cfg vertex (Defined ins')          (Defined outs')
    -> cfg vertex (Defined $ ins ++ ins') (Defined $ outs ++ outs')
  (|-|) = parallel @{impl}

  export infixr 5 *->
  ||| Alias for `Series`
  public export
  (*->) : (impl : CFG a cfg)
       => cfg vertex ins (Defined edges)
       -> cfg vertex (Defined edges) outs
       -> cfg vertex ins outs
  (*->) = series @{impl}


  public export
  prepend : (impl : CFG a cfg)
         => {0 vertex : Vertex a}
         -> {vins : Neighbors a}
         -> {vouts : List a}
         -> vertex v vins (Just vouts)
         -> cfg vertex (Defined $ v ~>> vouts) gouts
         -> cfg vertex (fromVIn vins v) gouts
  prepend v g = ((singleVertex v @{impl}) *-> g) @{impl}

  public export
  append : (impl : CFG a cfg)
        => {vins : List a}
        -> {vouts : Neighbors a}

        -> cfg vertex gins (Defined $ vins ~~> v)
        -> vertex v (Just vins) vouts
        -> cfg vertex gins (fromVOut v vouts)
  append g v = (g *-> (singleVertex v @{impl})) @{impl}

  branch : (impl : CFG a cfg)
        => {0 vertex : Vertex a}
        -> {vins : Neighbors a}
        -> {w, w' : a}

        -> (pre   : vertex v vins (Just [w, w']))
        -> (left  : cfg vertex (Single v w)  (Defined louts))
        -> (right : cfg vertex (Single v w') (Defined routs))
        -> cfg vertex (fromVIn vins v) (Defined $ louts ++ routs)
  branch pre left right = (pre `prepend` ((left |-| right) @{impl})) @{impl}

  fullBranch : (impl : CFG a cfg)
            => {0 vertex : Vertex a}
            -> {vins, vouts : Neighbors a}
            -> {w, w', u, u' : a}

            -> (pre    : vertex v vins (Just [w, w']))
            -> (left   : cfg vertex (Single v w)  (Single u t))
            -> (right  : cfg vertex (Single v w') (Single u' t))
            -> (post   : vertex t (Just [u, u']) vouts)
            -> cfg vertex (fromVIn vins v) (fromVOut t vouts)
  fullBranch pre left right post = ((branch pre left right @{impl}) `append` post) @{impl}

  ||| A partial sequential connection of two graphs
  ||| The left outputs of the predecessor are connected with all inputs of
  ||| the successor
  ||| @ node   the           predecessor of `branch`
  ||| @ branch the (partial) successor   of `node`
  ||| @ ls     the left  outputs of `node` / the inputs of `branch`
  ||| @ rs     the right outputs of `node`
  public export
  lbranch : (impl : CFG a cfg)
         => {ls, rs : List (Edge a)}
         -> (node   : cfg vertex ins (Defined $ ls ++ rs))
         -> (branch : cfg vertex (Defined ls) (Defined ls'))
         ->           cfg vertex ins (Defined $ ls' ++ rs)
  lbranch node branch = (node *-> ((branch |-| (empty @{impl})) @{impl}) @{impl})

  ||| A partial sequential connection of two graphs
  ||| The right outputs of the predecessor are connected with all inputs of1
  ||| the successor
  ||| @ node   the           predecessor of `branch`
  ||| @ branch the (partial) successor   of `node`
  ||| @ ls     the left  outputs of `node`
  ||| @ rs     the right outputs of `node` / the inputs of `branch`
  public export
  rbranch : (impl : CFG a cfg)
         => {ls, rs : List (Edge a)}
         -> (node   : cfg vertex ins (Defined $ ls ++ rs))
         -> (branch : cfg vertex (Defined rs) (Defined rs'))
         ->           cfg vertex ins (Defined $ ls ++ rs')
  rbranch node branch = (node *-> ((empty @{impl} |-| branch) @{impl})) @{impl}

  ||| A partial sequential connection of two graphs
  ||| All outputs of the predecessor are connected with the left inputs of
  ||| the successor
  ||| @ branch the           predecessor of `node`
  ||| @ node   the (partial) successor   of `branch`
  ||| @ ls'    the left  inputs of `node` / the outputs of `branch`
  ||| @ rs     the right inputs of `node`
  public export
  lmerge : (impl : CFG a cfg)
        => {ls, rs  : List (Edge a)}
        -> (branch  : cfg vertex (Defined ls) (Defined ls'))
        -> (node    : cfg vertex (Defined $ ls' ++ rs) outs)
        ->            cfg vertex (Defined $ ls  ++ rs) outs
  lmerge branch node = (branch |-| (empty @{impl})) *-> node

  ||| A partial sequential connection of two graphs
  ||| All outputs of the predecessor are connected with the right inputs of
  ||| the successor
  ||| @ branch the           predecessor of `node`
  ||| @ node   the (partial) successor   of `branch`
  ||| @ ls     the left  inputs of `node`
  ||| @ rs'    the right inputs of `node` / the outputs of `branch`
  public export
  rmerge : (impl : CFG a cfg)
        => {ls, rs  : List (Edge a)}
        -> (branch  : cfg vertex (Defined rs) (Defined rs'))
        -> (node    : cfg vertex (Defined $ ls ++ rs') outs)
        ->            cfg vertex (Defined $ ls ++ rs) outs
  rmerge branch node = (empty |-| branch) *-> node


  export infixr 5 *~>
  ||| Alias for `connect`
  export
  (*~>) : (impl : Connectable vertex)
       => cfg vertex ins (Undefined v)
       -> cfg vertex (Undefined v) outs
       -> cfg vertex ins outs
  (*~>) = connect


  export
  initGraph : {0 vertex : Vertex a}
           -> vertex v Undefined Undefined
           -> cfg vertex (Undefined v) (Undefined v)
  initGraph v = singleVertex v

