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

  namespace Buffer
    public export
    data BufferType : UEdge a -> Type where
      NoBuffer : BufferType (Defined edg)
      HalfBuffer : Neighbors a -> BufferType {a} (Undefined v)

    public export
    data Direction = Pre | Post

    public export
    data Buffer : (vertex : UVertex a) -> Direction -> (edg : UEdge a) -> BufferType edg -> Type where
      NoBuff   : Buffer vertex dir (Defined edg) NoBuffer
      PreBuff  : {0 v : a} -> vertex v Nothing    (Just outs) -> Buffer vertex Pre  (Undefined v) (HalfBuffer outs)
      PostBuff : {0 v : a} -> vertex v (Just ins) Nothing     -> Buffer vertex Post (Undefined v) (HalfBuffer ins)

    public export
    data Buffers : (vertex : UVertex a) -> Direction -> (edgs : UEdges a) -> DList BufferType edgs -> Type where
      Nil : Buffers vertex dir Nil Nil
      (::) : Buffer vertex dir edg bt -> Buffers vertex dir edgs bts -> Buffers vertex dir (edg :: edgs) (bt :: bts)
    
    public export
    (++) : Buffers vertex dir edgs bts -> Buffers vertex dir edgs' bts' -> Buffers vertex dir (edgs ++ edgs') (bts ++ bts')
    Nil             ++ buffs' = buffs'
    (buff :: buffs) ++ buffs' = buff :: (buffs ++ buffs')

    public export
    UnU : Direction -> (edg : UEdge a) -> BufferType edg -> Edges a
    UnU dir  (Defined edg) NoBuffer          = [edg]
    UnU Pre  (Undefined v) (HalfBuffer outs) = v ~>> outs
    UnU Post (Undefined v) (HalfBuffer ins)  = ins ~~> v

    public export
    Links : Direction -> (edgs : UEdges a) -> DList BufferType edgs -> Edges a
    Links dir Nil Nil = Nil
    Links dir (edg :: edgs) (bt :: bts) = UnU dir edg bt ++ Links dir edgs bts

    public export
    Ends : (edgs : UEdges a) -> DList BufferType edgs -> Edges a
    Ends = Links Pre

    public export
    Beginnings : (edgs : UEdges a) -> DList BufferType edgs -> Edges a
    Beginnings = Links Post

    public export
    links_concat : (dir : Direction)
                -> (edgs, edgs' : UEdges a)
                -> (bts : DList BufferType edgs)
                -> (bts' : DList BufferType edgs')
                -> Links dir edgs bts ++ Links dir edgs' bts'
                = Links dir (edgs ++ edgs') (bts ++ bts')

    public export
    unBuffer' : (impl : Connectable vertex)
             => Buffer vertex Post (Undefined v) (HalfBuffer ins)
             -> Buffer vertex Pre  (Undefined v) (HalfBuffer outs)
             -> UnU vertex v ins outs
    unBuffer' (PostBuff v) (PreBuff w) = (v `cnct` w) @{impl}
    
    public export
    unBuffer : (impl : Connectable vertex)
            => {edge : UEdge a}
            -> {postBT, preBT : BufferType edge}
            -> Buffer vertex Post edge postBT
            -> Buffer vertex Pre  edge preBT
            -> CFG (Vertex.UnU vertex) (Buffer.UnU Post edge postBT) (Buffer.UnU Pre edge preBT)
    unBuffer (PostBuff v) (PreBuff w) = SingleVertex $ (v `cnct` w) @{impl}
    unBuffer NoBuff NoBuff = Empty
    
    public export
    unBuffers : (impl : Connectable vertex)
             => {edgs : UEdges a}
             -> {postBTs, preBTs : DList BufferType edgs}
             -> Buffers vertex Post edgs postBTs
             -> Buffers vertex Pre  edgs preBTs
             -> CFG (Vertex.UnU vertex) (Beginnings edgs postBTs) (Ends edgs preBTs)
    unBuffers Nil Nil = Empty
    unBuffers (post :: posts) (pre :: pres) = unBuffer post pre |-| unBuffers posts pres
    

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
  record UCFG (vertex : UVertex a) (ins : UEdges a) (outs : UEdges a) where
    constructor MkCFG
    preBTs : DList BufferType ins
    pre : Buffers vertex Pre ins preBTs
    postBTs : DList BufferType outs
    post : Buffers vertex Post outs postBTs
    cfg : CFG (UnU vertex) (Ends ins preBTs) (Beginnings outs postBTs)

  
  parallel : UCFG vertex ins outs
          -> UCFG vertex ins' outs'
          -> UCFG vertex (ins ++ ins') (outs ++ outs')
  parallel cfg cfg' = MkCFG
    { preBTs  = cfg.preBTs  ++ cfg'.preBTs
    , pre     = cfg.pre     ++ cfg'.pre
    , postBTs = cfg.postBTs ++ cfg'.postBTs
    , post    = cfg.post    ++ cfg'.post
    , cfg     = rewrite revEq $ links_concat Pre  ins  ins'  cfg.preBTs  cfg'.preBTs
             in rewrite revEq $ links_concat Post outs outs' cfg.postBTs cfg'.postBTs
             in cfg.cfg |-| cfg'.cfg
    }
  
  public export
  (|-|) : UCFG vertex ins outs
       -> UCFG vertex ins' outs'
       -> UCFG vertex (ins ++ ins') (outs ++ outs')
  (|-|) = parallel

  {-
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
