module CFG

import Data.List

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
    
    Cycle : (node : CFG vertex (Defined $ ins ++ ins' ~~> vin) (Defined $ (vout ~> w) :: outs))
         -> (loop : CFG vertex (Single vout w) (Defined $ ins' ~~> vin))
         -> CFG vertex (Defined ins) (Defined outs)

    
    Series : {auto 0 prf : NonEmpty edges}
          -> CFG vertex ins (Defined edges)
          -> CFG vertex (Defined edges) outs
          -> CFG vertex ins outs
    
    
    LBranch : {ls, rs : List (Edge a)}
           -> (node   : CFG vertex ins (Defined $ ls ++ rs))
           -> (branch : CFG vertex (Defined ls) (Defined ls'))
           ->           CFG vertex ins (Defined $ ls' ++ rs)
    
    RBranch : {ls, rs : List (Edge a)}
           -> (node   : CFG vertex ins (Defined $ ls ++ rs))
           -> (branch : CFG vertex (Defined rs) (Defined rs'))
           ->           CFG vertex ins (Defined $ ls ++ rs')

    
    LMerge : {ls, rs  : List (Edge a)}
          -> (branch  : CFG vertex (Defined ls) (Defined ls'))
          -> (node    : CFG vertex (Defined $ ls' ++ rs) outs)
          ->            CFG vertex (Defined $ ls ++ rs) outs
    
    RMerge : {ls, rs  : List (Edge a)}
          -> (branch  : CFG vertex (Defined rs) (Defined rs'))
          -> (node    : CFG vertex (Defined $ ls ++ rs') outs)
          ->            CFG vertex (Defined $ ls ++ rs) outs
         
    
    Parallel : CFG vertex (Defined ins) (Defined outs)
            -> CFG vertex (Defined ins') (Defined outs')
            -> CFG vertex (Defined $ ins ++ ins') (Defined $ outs ++ outs')
    
    
    -- TODO: consider removing these constructors
    IFlip : {ins, ins' : List (Edge a)}
         -> CFG vertex (Defined $ ins ++ ins') outs
         -> CFG vertex (Defined $ ins' ++ ins) outs
    
    OFlip : {outs, outs' : List (Edge a)}
         -> CFG vertex ins (Defined $ outs ++ outs')
         -> CFG vertex ins (Defined $ outs' ++ outs)

  public export
  prepend : {0 vertex : Vertex a}
         -> {vins : Neighbors a}
         -> {vouts : List a}
         -> {auto 0 prf : NonEmpty (v ~>> vouts)}
         -> vertex v vins (Just vouts)
         -> CFG vertex (Defined $ v ~>> vouts) gouts
         -> CFG vertex (fromVIn vins v) gouts
  prepend v g = Series (SingleVertex v) g

  public export
  append : {vins : List a}
        -> {vouts : Neighbors a}
        -> {auto 0 prf : NonEmpty (vins ~~> v)}
        
        -> CFG vertex gins (Defined $ vins ~~> v)
        -> vertex v (Just vins) vouts
        -> CFG vertex gins (fromVOut v vouts)
  append g v = Series g (SingleVertex v)
  
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
  imap f (Series g g')                      = Series (imap f g) g'
  imap f (LBranch g g')                     = LBranch (imap f g) g'
  imap f (RBranch g g')                     = RBranch (imap f g) g'
  
  imap f (OFlip g)                          = OFlip (imap f g)
  
  imap f (SingleVertex {vins = Just ins} v) impossible
  imap f (Cycle node loop)                  impossible
  imap f (LMerge g g')                      impossible
  imap f (RMerge g g')                      impossible
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
  omap f (LMerge g g')                        = LMerge g (omap f g')
  omap f (RMerge g g')                        = RMerge g (omap f g')
  omap f (IFlip g)                            = IFlip (omap f g)
  
  omap f (SingleVertex {vouts = Just outs} v) impossible
  omap f (Cycle node loop)                    impossible
  omap f (LBranch g g')                       impossible
  omap f (RBranch g g')                       impossible
  omap f (Parallel g g')                      impossible
  omap f (OFlip g)                            impossible

  export
  connect : (impl : Connectable vertex)
         => CFG vertex ins (Undefined v)
         -> CFG vertex (Undefined v) outs
         -> CFG vertex ins outs

  connect (SingleVertex {vouts = Nothing} v)  g   = imap (cnct @{impl} v) g
  connect (Series g g')                       g'' = Series g (connect g' g'')
  connect (LMerge g g')                       g'' = LMerge g (connect g' g'')
  connect (RMerge g g')                       g'' = RMerge g (connect g' g'')
  connect (IFlip g)                           g'  = IFlip (connect g g')

  connect (SingleVertex {vouts = Just outs} v)  g' impossible
  connect (Cycle node loop)                     g' impossible
  connect (LBranch g g')                        g' impossible
  connect (RBranch g g')                        g' impossible
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
  iget f (Series g g')                      = iget f g
  iget f (LBranch g g')                     = iget f g
  iget f (RBranch g g')                     = iget f g
  iget f (OFlip g)                          = iget f g
  
  iget f (SingleVertex {vins = Just ins} v) impossible
  iget f (Cycle node loop)                  impossible
  iget f (LMerge g g')                      impossible
  iget f (RMerge g g')                      impossible
  iget f (Parallel g g')                    impossible
  iget f (IFlip g)                          impossible

  export
  oget : {0 vertex : Vertex a}
      -> ({ins : Neighbors a} -> vertex v ins Undefined -> b)
      -> CFG vertex gins (Undefined v)
      -> b

  oget f (SingleVertex {vouts = Nothing} v)   = f v
  oget f (Series g g')                        = oget f g'
  oget f (LMerge g g')                        = oget f g'
  oget f (RMerge g g')                        = oget f g'
  oget f (IFlip g)                            = oget f g
  
  oget f (SingleVertex {vouts = Just outs} v) impossible
  oget f (Cycle node loop)                    impossible
  oget f (LBranch g g')                       impossible
  oget f (RBranch g g')                       impossible
  oget f (Parallel g g')                      impossible
  oget f (OFlip g)                            impossible



  export
  oget' : {0 vertex : Vertex a}
       -> ({0 v : a} -> {ins : Neighbors a} -> {outs : List a} -> vertex v ins (Just outs) -> DList g (v ~>> outs))
       -> CFG vertex gins (Defined gouts)
       -> DList g gouts

  oget' f (SingleVertex {vouts = Nothing} v)      impossible

  oget' f (SingleVertex {v, vouts = Just outs} w) = f w
  oget' f (Cycle node loop)                       = tail (oget' f node)
  oget' f (Series g g')                           = oget' f g'

  oget' f (LBranch g g')                          = let (lhs, rhs) = split (oget' f g)
                                                    in oget' f g' ++ rhs
  
  oget' f (RBranch g g')                          = let (lhs, rhs) = split (oget' f g)
                                                    in lhs ++ oget' f g'
  
  oget' f (LMerge g g')                           = oget' f g'
  oget' f (RMerge g g')                           = oget' f g'
  oget' f (Parallel g g')                         = oget' f g ++ oget' f g'
  oget' f (IFlip g)                               = oget' f g
  
  oget' f (OFlip g)                               = let (lres, rres) = split (oget' f g)
                                                    in rres ++ lres




