module CFG

import Utils

namespace Vertex
  
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

  public export
  data CFG : Vertex a -> Endpoints a -> Endpoints a -> Type where

    SingleVertex : {0 vertex : Vertex a}
                -> {vins, vouts : Endpoint a}
                -> vertex v vins vouts
                -> CFG vertex (fromVIn vins v) (fromVOut v vouts)

    Empty : CFG vertex (Ends es) (Ends es)
    
    Cycle : (node : vertex v (Just $ u :: ins) (Just $ w :: outs))
         -> (loop : CFG vertex (Single v w) (Single u v))
         -> CFG vertex (fromVIn (Just ins) v) (fromVOut v (Just outs))

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
  mapIn : {0 vertex : Vertex a}
          -> {ins : Endpoint a}

          -> ({outs : Endpoint a} -> vertex v Undefined outs -> vertex v ins outs)
          -> CFG vertex (Undefined v) gouts
          -> CFG vertex (fromVIn ins v) gouts

  mapIn f (SingleVertex {vins = Nothing} v) = SingleVertex (f v)
  mapIn f (Connect g g')                    = Connect (mapIn f g) g'
  mapIn f (FlipOut g)                       = FlipOut (mapIn f g)
  
  mapIn f (SingleVertex {vins = Just ins} v)  impossible
  mapIn f Empty                               impossible
  mapIn f (Cycle node loop)                   impossible
  mapIn f (Parallel g g')                     impossible
  mapIn f (FlipIn g)                          impossible
  
  
  export
  mapOut : {0 vertex : Vertex a}
          -> {outs : Endpoint a}

          -> ({ins : Endpoint a} -> vertex v ins Undefined -> vertex v ins outs)
          -> CFG vertex gins (Undefined v)
          -> CFG vertex gins (fromVOut v outs)

  mapOut f (SingleVertex {vouts = Nothing} v) = SingleVertex (f v)
  mapOut f (Connect g g')                     = Connect g (mapOut f g')
  mapOut f (FlipIn g)                         = FlipIn (mapOut f g)
  
  mapOut f (SingleVertex {vouts = Just outs} v) impossible
  mapOut f Empty                                impossible
  mapOut f (Cycle node loop)                    impossible
  mapOut f (Parallel g g')                      impossible
  mapOut f (FlipOut g)                          impossible

  export
  connect : (impl : Connectable vertex)
         => CFG vertex ins (Undefined v)
         -> CFG vertex (Undefined v) outs
         -> CFG vertex ins outs

  connect (SingleVertex {vouts = Nothing} v)  g   = mapIn (cnct @{impl} v) g
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

