module CFGNew

--import Data.DList
import Theory
import Data.ListEq

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

  namespace Edge
    -- `v ~> w` - an edge from `v` to `w`
    public export
    data Edge a = (~>) a a

    public export
    (<~) : a -> a -> Edge a
    (<~) = flip (~>)

    public export
    Dest : Edge a -> a
    Dest (from ~> to) = to

    public export
    Origin : Edge a -> a
    Origin (from ~> to) = from

  namespace Edge'
    public export
    data Edge' a = Undefined a | Defined (Edge a)

    public export
    (~>) : a -> a -> Edge' a
    v ~> w = Defined (v ~> w)

    public export
    (<~) : a -> a -> Edge' a
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
  Edges : Type -> Type
  Edges a = List (Edge' a)

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

  public export
  fromVOut : a -> (e : Neighbors a) -> Edges a
  fromVOut v Nothing      = [Undefined v]
  fromVOut v (Just outs)  = v ~>> outs

  public export
  fromVIn : (e : Neighbors a) -> a -> Edges a
  fromVIn Nothing     v = [Undefined v]
  fromVIn (Just ins)  v = ins ~~> v

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

    Empty : {edges : Edges a}
         -> CFG vertex edges edges
    
    SingleVertex : {0 vertex : Vertex a}
                -> {vins, vouts : Neighbors a}
                -> vertex v vins vouts
                -> CFG vertex (fromVIn vins v) (fromVOut v vouts)

    
    -- TODO consider `CFG (ins ++ edges) (outs ++ edges) -> CFG ins outs` instead of this
    Cycle : {ins, outs, loopIns, loopOuts : Edges a}
         -> (node : CFG vertex (ins ++ loopOuts) (loopIns ++ outs))
         -> (loop : CFG vertex loopIns loopOuts)
         -> CFG vertex ins outs

    
    Series : {ins, edges, outs : Edges a}
          -> CFG vertex ins   edges
          -> CFG vertex edges outs
          -> CFG vertex ins   outs
    
    
    Parallel : {ins, ins', outs, outs' : Edges a}
            -> CFG vertex ins           outs
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
  (|-|) : {ins, ins', outs, outs' : Edges a}
       -> CFG vertex ins           outs
       -> CFG vertex ins'          outs'
       -> CFG vertex (ins ++ ins') (outs ++ outs')
  (|-|) = Parallel

  infixr 5 *->
  public export
  (*->) : {ins, edges, outs : Edges a}
       -> CFG vertex ins   edges
       -> CFG vertex edges outs
       -> CFG vertex ins   outs
  (*->) = Series

  {-
  public export
  prepend'' : {0 vertex : Vertex a}
         -> {vins : Neighbors a}
         -> {vouts : List a}
         -> vertex v vins (Just vouts)
         -> CFG vertex (v ~>> vouts) gouts
         -> CFG vertex (fromVIn vins v) gouts
  prepend'' v g = (SingleVertex v) *-> g

  public export
  append : {vins : List a}
        -> {vouts : Neighbors a}
        
        -> CFG vertex gins (vins ~~> v)
        -> vertex v (Just vins) vouts
        -> CFG vertex gins (fromVOut v vouts)
  append g v = g *-> (SingleVertex v)
  
  branch : {0 vertex : Vertex a}
        -> {vins : Neighbors a}
        -> {w, w' : a}
        
        -> (pre   : vertex v vins (Just [w, w']))
        -> (left  : CFG vertex [v ~> w]  (louts))
        -> (right : CFG vertex [v ~> w'] (routs))
        -> CFG vertex (fromVIn vins v) (louts ++ routs)
  branch pre left right = pre `prepend''` (left |-| right)

  fullBranch : {0 vertex : Vertex a}
            -> {vins, vouts : Neighbors a}
            -> {w, w', u, u' : a}

            -> (pre    : vertex v vins (Just [w, w']))
            -> (left   : CFG vertex [v ~> w]  [u  ~> t])
            -> (right  : CFG vertex [v ~> w'] [u' ~> t])
            -> (post   : vertex t (Just [u, u']) vouts)
            -> CFG vertex (fromVIn vins v) (fromVOut t vouts)
  fullBranch pre left right post = (branch pre left right) `append` post
  -}

  public export  
  lbranch : {ins, ls, ls', rs : Edges a}
         -> (node   : CFG vertex ins (ls ++ rs))
         -> (branch : CFG vertex ls  ls')
         ->           CFG vertex ins (ls' ++ rs)
  lbranch node branch = node *-> (branch |-| Empty)

  public export
  rbranch : {ins, ls, rs, rs' : Edges a}
         -> (node   : CFG vertex ins (ls ++ rs))
         -> (branch : CFG vertex rs  rs')
         ->           CFG vertex ins (ls ++ rs')
  rbranch node branch = node *-> (Empty |-| branch)

  public export
  lmerge : {ls, ls', rs, outs : Edges a}
        -> (branch  : CFG vertex ls          ls')
        -> (node    : CFG vertex (ls' ++ rs) outs)
        ->            CFG vertex (ls  ++ rs) outs
  lmerge branch node = (branch |-| Empty) *-> node

  public export
  rmerge : {ls, rs, rs', outs : Edges a}
        -> (branch  : CFG vertex rs rs')
        -> (node    : CFG vertex (ls ++ rs') outs)
        ->            CFG vertex (ls ++ rs)  outs
  rmerge branch node = (Empty |-| branch) *-> node

  {-
  export
  imap : {0 vertex : Vertex a}
          -> {ins : Neighbors a}

          -> ({outs : Neighbors a} -> vertex v Undefined outs -> vertex v ins outs)
          -> CFG vertex [Undefined v] gouts
          -> CFG vertex (fromVIn ins v) gouts

  imap f (SingleVertex {vins = Nothing} v)  = SingleVertex (f v)
  imap f (Series g g')                      = Series (imap f g) g'
  
  imap f (OFlip g)                          = OFlip (imap f g)
  
  imap f Empty                              impossible
  imap f (SingleVertex {vins = Just ins} v) impossible
  imap f (Cycle node loop)                  impossible
  imap f (Parallel g g')                    impossible
  imap f (IFlip g)                          impossible
  -}

  prepend
     : (impl : Connectable vertex)
    => {lbl : a}
    -> {vins : Neighbors a}
    -> {lgins, rgins : Edges a}
    -> ListEq (lgins ++ Undefined lbl :: rgins) gins
    -> vertex lbl vins Undefined
    -> CFG {a} vertex gins gouts
    -> CFG {a} vertex (lgins ++ fromVIn vins lbl ++ rgins) gouts
  
  prepend prf v (Empty) = rewrite revEq $ toEq prf
                          in Empty |-| SingleVertex v |-| Empty

  prepend prf u (SingleVertex {vins = Nothing, v} w) = let
    
    0 lgins_empty : (lgins = Nil)
    lgins_empty = concat_cons_is_single_then_prefix_is_nil lgins rgins (Undefined lbl) (Undefined v) (toEq prf)
    0 rgins_empty : (rgins = Nil)
    rgins_empty = concat_cons_is_single_then_postfix_is_nil lgins rgins (Undefined lbl) (Undefined v) (toEq prf)
    0 v_is_lbl : (v = lbl)
    v_is_lbl = case concat_cons_is_single_then_mid_is_the_elem lgins rgins (Undefined lbl) (Undefined v) (toEq prf) of
      Refl => Refl

    in rewrite lgins_empty
    in rewrite rgins_empty
    in rewrite v_is_lbl
    in rewrite concat_nil (fromVIn vins lbl)
    in SingleVertex (cnct @{impl} u (rewrite revEq v_is_lbl in w))

  prepend prf v (SingleVertex {vins = Just vins} w) = ?hsingleD
  prepend prf v (Cycle {loopIns, loopOuts} node loop) = let
      
      prf' : ListEq (lgins ++ Undefined lbl :: (rgins ++ loopOuts)) (gins ++ loopOuts)
      prf' = rewrite concat_assoc lgins (Undefined lbl :: rgins) loopOuts
            in prf ++ fromEq Refl
  
      node' : CFG vertex ((lgins ++ (fromVIn vins lbl ++ rgins)) ++ loopOuts) (loopIns ++ gouts)
      node' = rewrite revEq $ concat_assoc lgins (fromVIn vins lbl ++ rgins) loopOuts
           in rewrite revEq $ concat_assoc (fromVIn vins lbl) rgins loopOuts
           in prepend {rgins = rgins ++ loopOuts, gouts = loopIns ++ gouts} prf' v node
      
    in Cycle node' loop

  prepend prf v (Series g g')     = Series (prepend prf v g) g'
  prepend prf v (OFlip g)         = OFlip (prepend prf v g)
  
  prepend prf v (Parallel {ins, ins', outs, outs'} g g') = case split' prf of
    Left (lrys ** rrys ** (prf0, prf1, prf2))
      => rewrite the (lgins = ins ++ lrys) (toEq prf0)
      in rewrite revEq $ concat_assoc ins lrys (fromVIn vins lbl ++ rgins)
      in rewrite the (rgins = rrys) (toEq prf1)
      in Parallel g (prepend (rev prf2) v g')

    Right (llys ** rlys ** (prf0, prf1, prf2))
      => rewrite toEq prf0
      in rewrite toEq prf1
      in rewrite concat_assoc (fromVIn vins lbl) rlys ins'
      in rewrite concat_assoc llys (fromVIn vins lbl ++ rlys) ins'
      in Parallel (prepend (rev prf2) v g) g'
  
  prepend prf v (IFlip {ins, ins'} g) = case split' prf of
    Left (lrys ** rrys ** (prf0, prf1, prf2))
      => let
        prf' = rewrite concat_assoc lrys (Undefined lbl :: rrys) ins' in rev prf2 ++ fromEq Refl

        g' : CFG vertex ((lrys ++ (fromVIn vins lbl ++ rrys)) ++ ins') gouts
        g' = rewrite revEq $ concat_assoc lrys (fromVIn vins lbl ++ rrys) ins'
          in rewrite revEq $ concat_assoc (fromVIn vins lbl) rrys ins'
          in prepend {lgins = lrys, rgins = rrys ++ ins'} prf' v g

      in rewrite the (lgins = ins' ++ lrys) (toEq prf0)
      in rewrite revEq $ concat_assoc ins' lrys (fromVIn vins lbl ++ rgins)
      in rewrite the (rgins = rrys) (toEq prf1)
      in IFlip g'

    Right (llys ** rlys ** (prf0, prf1, prf2))
      => let
        prf' = rewrite revEq $ concat_assoc ins llys (Undefined lbl :: rlys)
            in fromEq Refl ++ (rev prf2)

        g' : CFG vertex (ins ++ (llys ++ (fromVIn vins lbl ++ rlys))) gouts
        g' = rewrite concat_assoc ins llys (fromVIn vins lbl ++ rlys)
          in prepend {lgins = ins ++ llys, rgins = rlys} prf' v g
      in rewrite toEq prf0
      in rewrite toEq prf1
      in rewrite concat_assoc (fromVIn vins lbl) rlys ins
      in rewrite concat_assoc llys (fromVIn vins lbl ++ rlys) ins
      in IFlip g'
  


  prepend'
     : (impl : Connectable vertex)
    => {lbl : a}
    -> {vins : Neighbors a}
    -> {lgins, rgins : Edges a}
    -> vertex lbl vins Undefined
    -> CFG {a} vertex (lgins ++ Undefined lbl :: rgins) gouts
    -> CFG {a} vertex (lgins ++ fromVIn vins lbl ++ rgins) gouts
  prepend' = prepend (fromEq Refl)



  {-
  export
  omap : {0 vertex : Vertex a}
          -> {outs : Neighbors a}

          -> ({ins : Neighbors a} -> vertex v ins Undefined -> vertex v ins outs)
          -> CFG vertex gins [Undefined v]
          -> CFG vertex gins (fromVOut v outs)

  omap f (SingleVertex {vouts = Nothing} v)   = SingleVertex (f v)
  omap f (Series g g')                        = Series g (omap f g')
  omap f (IFlip g)                            = IFlip (omap f g)
  
  omap f Empty                                impossible
  omap f (SingleVertex {vouts = Just outs} v) impossible
  omap f (Cycle node loop)                    impossible
  omap f (Parallel g g')                      impossible
  omap f (OFlip g)                            impossible
  -}

  {-
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
