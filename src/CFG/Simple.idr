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
  Endpoints : Type -> Type
  Endpoints a = Maybe (List (Edge a))

  public export
  Undefined : Endpoints a
  Undefined = Nothing

  public export
  Closed : Endpoints a
  Closed = Just []

  public export
  Single : a -> a -> Endpoints a
  Single from to = Just [from ~> to]


  public export
  fromVOut : a -> (e : Endpoint a) -> Endpoints a
  fromVOut v Nothing      = Nothing
  fromVOut v (Just outs)  = Just $ map (v ~>) outs

  public export
  fromVIn : (e : Endpoint a) -> a -> Endpoints a
  fromVIn Nothing     v = Nothing
  fromVIn (Just ins)  v = Just $ map (~> v) ins


  data Graph : Vertex a -> Endpoints a -> Endpoints a -> Type where

    SingleVertex : {0 vertex : Vertex a}
                -> vertex v vin vout
                -> Graph vertex (fromVIn vin v) (fromVOut v vout)

    -- TODO: maybe this will be better than `SingleVertex`
    --Empty : Graph a es es

    -- add vertices
    Prepend : {0 vertex : Vertex a}
           -> vertex v vins (Just vouts)
           -> Graph vertex (Just $ map (v ~>) vouts) gouts
           -> Graph vertex (fromVIn vins v) gouts

    Append : Graph vertex gins (Just $ map (~> v) vins)
          -> vertex v (Just vins) vouts
          -> Graph vertex gins (fromVOut v vouts)
    

    
    Cycle : (node : vertex v (Just $ u :: ins) (Just $ w :: outs))
         -> (loop : Graph vertex (Single v w) (Single u v))
         -> Graph vertex (fromVIn (Just ins) v) (fromVOut v (Just outs))

    -- TODO: Consider the following
    --Cycle : (node : Vertex v (Just $ ins ++ u :: ins') (Just $ outs ++ w :: outs'))
    --     -> (loop : Graph a (Single v w) (Single u v))
    --     -> Graph a (fromVIn (Just $ ins ++ ins') v) (fromVOut v (Just $ outs ++ outs'))


    
    Connect : Graph a ins (Just edges)
           -> Graph a (Just edges) outs
           -> Graph a ins outs
    
    Parallel : Graph a (Just ins) (Just outs)
            -> Graph a (Just ins') (Just outs')
            -> Graph a (Just $ ins ++ ins') (Just $ outs ++ outs')


  branch : {0 vertex : Vertex a}
        -> (pre   : vertex v vins (Just [w, w']))
        -> (left  : Graph vertex (Single v w)  (Just louts))
        -> (right : Graph vertex (Single v w') (Just routs))
        -> Graph vertex (fromVIn vins v) (Just $ louts ++ routs)
  branch pre left right = Prepend pre $ Parallel left right

  fullBranch : {0 vertex : Vertex a}
            -> (pre    : vertex v vins (Just [w, w']))
            -> (left   : Graph vertex (Single v w)  (Single u t))
            -> (right  : Graph vertex (Single v w') (Single u' t))
            -> (post   : vertex t (Just [u, u']) vouts)
            -> Graph vertex (fromVIn vins v) (fromVOut t vouts)
  fullBranch pre left right post = Append (branch pre left right) post

  