module CFG.Simple


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

namespace Graph

  public export
  data Edge a = MkEdge a a

  infix 6 ~>, <~
  public export
  (~>) : a -> a -> Edge a
  (~>) = MkEdge

  public export
  (<~) : a -> a -> Edge a
  (<~) = flip (~>)

  public export
  Dest : Edge a -> a
  Dest (MkEdge from to) = to

  public export
  Origin : Edge a -> a
  Origin (MkEdge from to) = from

  public export
  data Endpoints a = Undefined a | Ends (List (Edge a))

  public export
  Closed : Endpoints a
  Closed = Ends []

  public export
  Single : a -> a -> Endpoints a
  Single from to = Ends [from ~> to]


  public export
  fromVOut : a -> (e : Endpoint a) -> Endpoints a
  fromVOut v Nothing      = Undefined v
  fromVOut v (Just outs)  = Ends $ map (v ~>) outs

  public export
  fromVIn : (e : Endpoint a) -> a -> Endpoints a
  fromVIn Nothing     v = Undefined v
  fromVIn (Just ins)  v = Ends $ map (~> v) ins


  data Graph : Vertex a -> Endpoints a -> Endpoints a -> Type where

    SingleVertex : {0 vertex : Vertex a}
                -> vertex v vins vouts
                -> Graph vertex (fromVIn vins v) (fromVOut v vouts)

    
    
    Cycle : (node : vertex v (Just $ u :: ins) (Just $ w :: outs))
         -> (loop : Graph vertex (Single v w) (Single u v))
         -> Graph vertex (fromVIn (Just ins) v) (fromVOut v (Just outs))

    -- TODO: Consider the following
    --Cycle : (node : Vertex v (Just $ ins ++ u :: ins') (Just $ outs ++ w :: outs'))
    --     -> (loop : Graph a (Single v w) (Single u v))
    --     -> Graph a (fromVIn (Just $ ins ++ ins') v) (fromVOut v (Just $ outs ++ outs'))


    
    Connect : Graph vertex ins (Ends edges)
           -> Graph vertex (Ends edges) outs
           -> Graph vertex ins outs
    
    Parallel : Graph vertex (Ends ins) (Ends outs)
            -> Graph vertex (Ends ins') (Ends outs')
            -> Graph vertex (Ends $ ins ++ ins') (Ends $ outs ++ outs')


  prepend : {0 vertex : Vertex a}
         -> vertex v vins (Just vouts)
         -> Graph vertex (Ends $ map (v ~>) vouts) gouts
         -> Graph vertex (fromVIn vins v) gouts
  prepend v g = Connect (SingleVertex v) g

  append : Graph vertex gins (Ends $ map (~> v) vins)
        -> vertex v (Just vins) vouts
        -> Graph vertex gins (fromVOut v vouts)
  append g v = Connect g (SingleVertex v)
  
  branch : {0 vertex : Vertex a}
        -> (pre   : vertex v vins (Just [w, w']))
        -> (left  : Graph vertex (Single v w)  (Ends louts))
        -> (right : Graph vertex (Single v w') (Ends routs))
        -> Graph vertex (fromVIn vins v) (Ends $ louts ++ routs)
  branch pre left right = prepend pre $ Parallel left right

  fullBranch : {0 vertex : Vertex a}
            -> (pre    : vertex v vins (Just [w, w']))
            -> (left   : Graph vertex (Single v w)  (Single u t))
            -> (right  : Graph vertex (Single v w') (Single u' t))
            -> (post   : vertex t (Just [u, u']) vouts)
            -> Graph vertex (fromVIn vins v) (fromVOut t vouts)
  fullBranch pre left right post = append (branch pre left right) post
  
  
