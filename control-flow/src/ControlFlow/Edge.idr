module ControlFlow.Edge

import Theory

export infix 6 ~>, <~

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

export infix 8 ~~>, ~>>, <~~, <<~

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
