{- Copied from haskell's dependent-map package -}
module Data.DMap'

import Control.Monad.State
import Data.Maybe

import Data.DSum
import Data.GCompare
import Data.GEq
import Data.ShowS
import Data.Some

{--------------------------------------------------------------------
---------------------------------------------------------------------
  Data.Dependent.Map
---------------------------------------------------------------------
--------------------------------------------------------------------}
export
data DMap : (k : a -> Type) -> (f : a -> Type) -> Type where
    Tip : DMap k f
    Bin : (sz    : Int)
       -> (key   : k v)
       -> (value : f v)
       -> (left  : DMap k f)
       -> (right : DMap k f)
       -> DMap k f

{--------------------------------------------------------------------
  Construction
--------------------------------------------------------------------}

-- | /O(1)/. The empty map.
--
-- > empty      == fromList []
-- > size empty == 0
export
empty : DMap k f
empty = Tip

-- | /O(1)/. A map with a single element.
--
-- > singleton 1 'a'        == fromList [(1, 'a')]
-- > size (singleton 1 'a') == 1
export
singleton : {0 v : a} -> k v -> f v -> DMap k f
singleton k x = Bin 1 k x Tip Tip

{--------------------------------------------------------------------
---------------------------------------------------------------------
  Data.Dependent.Map
---------------------------------------------------------------------
--------------------------------------------------------------------}

{--------------------------------------------------------------------
  Query
--------------------------------------------------------------------}

-- | /O(1)/. Is the map empty?
export
null : DMap k f -> Bool
null Tip              = True
null (Bin _ _ _ _ _)  = False

-- | /O(1)/. The number of elements in the map.
export
size : DMap k f -> Int
size Tip                = 0
size (Bin n _ _ _ _)    = n

-- | /O(log n)/. Lookup the value at a key in the map.
--
-- The function will return the corresponding value as @('Just' value)@,
-- or 'Nothing' if the key isn't in the map.
export
lookup : (impl : GCompare k) => k v -> DMap k f -> Maybe (f v)
lookup k Tip = Nothing
lookup k (Bin _ kx x l r) = case gcompare k kx @{impl} of
  GLT => lookup k l
  GGT => lookup k r
  GEQ => Just x

private
lookupAssoc : (impl : GCompare k) => Some k -> DMap k f -> Maybe (DSum k f)
lookupAssoc sk = withSome sk $ \key =>
  let
    go : DMap k f -> Maybe (DSum k f)
    go Tip = Nothing
    go (Bin _ kx x l r) =
        case gcompare key kx @{impl} of
            GLT => go l
            GGT => go r
            GEQ => Just (kx :=> x)
  in go

{--------------------------------------------------------------------
  Utility functions that maintain the balance properties of the tree.
  All constructors assume that all values in [l] < [k] and all values
  in [r] > [k], and that [l] and [r] are valid trees.

  In order of sophistication:
    [Bin sz k x l r]  The type constructor.
    [bin k x l r]     Maintains the correct size, assumes that both [l]
                      and [r] are balanced with respect to each other.
    [balance k x l r] Restores the balance and size.
                      Assumes that the original tree was balanced and
                      that [l] or [r] has changed by at most one element.
    [combine k x l r] Restores balance and size.

  Furthermore, we can construct a new tree from two trees. Both operations
  assume that all values in [l] < all values in [r] and that [l] and [r]
  are valid:
    [glue l r]        Glues [l] and [r] together. Assumes that [l] and
                      [r] are already balanced with respect to each other.
    [merge l r]       Merges two trees and restores balance.

  Note: in contrast to Adam's paper, we use (<=) comparisons instead
  of (<) comparisons in [combine], [merge] and [balance].
  Quickcheck (on [difference]) showed that this was necessary in order
  to maintain the invariants. It is quite unsatisfactory that I haven't
  been able to find out why this is actually the case! Fortunately, it
  doesn't hurt to be a bit more conservative.
--------------------------------------------------------------------}
private
delta, ratio : Int
delta = 4
ratio = 2


{--------------------------------------------------------------------
  The bin constructor maintains the size of the tree
--------------------------------------------------------------------}
private
bin : {0 v : a} -> k v -> f v -> DMap k f -> DMap k f -> DMap k f
bin k x l r
  = Bin (size l + size r + 1) k x l r



-- basic rotations
private
singleL, singleR : {0 v : a} -> k v -> f v -> DMap k f -> DMap k f -> DMap k f
singleL k1 x1 t1 (Bin _ k2 x2 t2 t3)  = bin k2 x2 (bin k1 x1 t1 t2) t3
singleL _ _ _ Tip = assert_total $ idris_crash "error: singleL Tip"
singleR k1 x1 (Bin _ k2 x2 t1 t2) t3  = bin k2 x2 t1 (bin k1 x1 t2 t3)
singleR _ _ Tip _ = assert_total $ idris_crash "error: singleR Tip"

private
doubleL, doubleR : {0 v : a} -> k v -> f v -> DMap k f -> DMap k f -> DMap k f
doubleL k1 x1 t1 (Bin _ k2 x2 (Bin _ k3 x3 t2 t3) t4) = bin k3 x3 (bin k1 x1 t1 t2) (bin k2 x2 t3 t4)
doubleL _ _ _ _ = assert_total $ idris_crash "error: doubleL"
doubleR k1 x1 (Bin _ k2 x2 t1 (Bin _ k3 x3 t2 t3)) t4 = bin k3 x3 (bin k2 x2 t1 t2) (bin k1 x1 t3 t4)
doubleR _ _ _ _ = assert_total $ idris_crash "error: doubleR"


-- rotate
private
rotateL : {0 v : a} -> k v -> f v -> DMap k f -> DMap k f -> DMap k f
rotateL k x l r@(Bin _ _ _ ly ry)
  = if size ly < ratio*size ry then singleL k x l r
                               else doubleL k x l r
rotateL _ _ _ Tip = assert_total $ idris_crash "error: rotateL Tip"

private
rotateR : {0 v : a} -> k v -> f v -> DMap k f -> DMap k f -> DMap k f
rotateR k x l@(Bin _ _ _ ly ry) r
  = if size ry < ratio*size ly then singleR k x l r
                               else doubleR k x l r
rotateR _ _ Tip _ = assert_total $ idris_crash "error: rotateR Tip"


{--------------------------------------------------------------------
  [balance l x r] balances two trees with value x.
  The sizes of the trees should balance after decreasing the
  size of one of them. (a rotation).

  [delta] is the maximal relative difference between the sizes of
          two trees, it corresponds with the [w] in Adams' paper.
  [ratio] is the ratio between an outer and inner sibling of the
          heavier subtree in an unbalanced setting. It determines
          whether a double or single rotation should be performed
          to restore balance. It corresponds with the inverse
          of $\alpha$ in Adam's article.

  Note that:
  - [delta] should be larger than 4.646 with a [ratio] of 2.
  - [delta] should be larger than 3.745 with a [ratio] of 1.534.

  - A lower [delta] leads to a more 'perfectly' balanced tree.
  - A higher [delta] performs less rebalancing.

  - Balancing is automatic for random data and a balancing
    scheme is only necessary to avoid pathological worst cases.
    Almost any choice will do, and in practice, a rather large
    [delta] may perform better than smaller one.

  Note: in contrast to Adam's paper, we use a ratio of (at least) [2]
  to decide whether a single or double rotation is needed. Although
  he actually proves that this ratio is needed to maintain the
  invariants, his implementation uses an invalid ratio of [1].
--------------------------------------------------------------------}
private
balance : {0 v : a} -> k v -> f v -> DMap k f -> DMap k f -> DMap k f
balance k x l r
  =    if sizeL + sizeR <= 1   then Bin sizeX k x l r
  else if sizeR >= delta*sizeL then rotateL k x l r
  else if sizeL >= delta*sizeR then rotateR k x l r
  else                              Bin sizeX k x l r

  where
    sizeL, sizeR, sizeX : Int
    sizeL = size l
    sizeR = size r
    sizeX = sizeL + sizeR + 1


{--------------------------------------------------------------------
  Combine
--------------------------------------------------------------------}

-- insertMin and insertMax don't perform potentially expensive comparisons.
private
insertMax, insertMin : {0 v : a} -> k v -> f v -> DMap k f -> DMap k f
insertMax kx x t
  = case t of
      Tip => singleton kx x
      Bin _ ky y l r
          => balance ky y l (insertMax kx x r)

insertMin kx x t
  = case t of
      Tip => singleton kx x
      Bin _ ky y l r
          => balance ky y (insertMin kx x l) r

private
combine : GCompare k => k v -> f v -> DMap k f -> DMap k f -> DMap k f
combine kx x Tip r  = insertMin kx x r
combine kx x l Tip  = insertMax kx x l
combine kx x l@(Bin sizeL ky y ly ry) r@(Bin sizeR kz z lz rz)
  =    if delta*sizeL <= sizeR then balance kz z (combine kx x l lz) rz
  else if delta*sizeR <= sizeL then balance ky y ly (combine kx x ry r)
  else                              bin kx x l r

-- | /O(log n)/. Retrieves the minimal (key :=> value) entry of the map, and
-- the map stripped of that element, or 'Nothing' if passed an empty map.
export
minViewWithKey : DMap k f -> Maybe (DSum k f, DMap k f)
minViewWithKey Tip = Nothing
minViewWithKey (Bin _ k0 x0 l0 r0) = Just $ go k0 x0 l0 r0
  where
    go : {0 k, f : a -> Type} -> k v -> f v -> DMap k f -> DMap k f -> (DSum k f, DMap k f)
    go k x Tip r = (k :=> x, r)
    go k x (Bin _ kl xl ll lr) r =
      let (km, l') = go kl xl ll lr
      in (km, balance k x l' r)

-- | /O(log n)/. Retrieves the maximal (key :=> value) entry of the map, and
-- the map stripped of that element, or 'Nothing' if passed an empty map.
export
maxViewWithKey : DMap k f -> Maybe (DSum k f, DMap k f)
maxViewWithKey Tip = Nothing
maxViewWithKey (Bin _ k0 x0 l0 r0) = Just $ go k0 x0 l0 r0
  where
    go : k v -> f v -> DMap k f -> DMap k f -> (DSum k f, DMap k f)
    go k x l Tip = (k :=> x, l)
    go k x l (Bin _ kr xr rl rr) =
      let (km, r') = go kr xr rl rr
      in (km, balance k x l r')

-- | /O(log n)/. Delete and find the maximal element.
--
-- > deleteFindMax (fromList [(5,"a"), (3,"b"), (10,"c")]) == ((10,"c"), fromList [(3,"b"), (5,"a")])
-- > deleteFindMax empty                                      Error: can not return the maximal element of an empty map
export
deleteFindMax : DMap k f -> (DSum k f, DMap k f)
deleteFindMax t
  = case t of
      Bin _ k x l Tip => (k :=> x,l)
      Bin _ k x l r   => let (km,r') = deleteFindMax r in (km,balance k x l r')
      --Tip             => (error "Map.deleteFindMax: can not return the maximal element of an empty map", Tip)
      Tip             => (assert_total $ idris_crash "Map.deleteFindMax: can not return the maximal element of an empty map", Tip)

-- | /O(log n)/. Delete and find the minimal element.
--
-- > deleteFindMin (fromList [(5,"a"), (3,"b"), (10,"c")]) == ((3,"b"), fromList[(5,"a"), (10,"c")])
-- > deleteFindMin                                            Error: can not return the minimal element of an empty map
export
deleteFindMin : DMap k f -> (DSum k f, DMap k f)
deleteFindMin t = case minViewWithKey t of
  Nothing => (assert_total $ idris_crash "Map.deleteFindMin: can not return the minimal element of an empty map", Tip)
  Just p => p

{--------------------------------------------------------------------
  [glue l r]: glues two trees together.
  Assumes that [l] and [r] are already balanced with respect to each other.
--------------------------------------------------------------------}
private
glue : DMap k f -> DMap k f -> DMap k f
glue Tip r = r
glue l Tip = l
glue l r =
  if size l > size r then case deleteFindMax l of (km :=> m, l') => balance km m l' r
                     else case deleteFindMin r of (km :=> m, r') => balance km m l r'

{--------------------------------------------------------------------
  [merge l r]: merges two trees.
--------------------------------------------------------------------}
private
merge : DMap k f -> DMap k f -> DMap k f
merge Tip r   = r
merge l Tip   = l
merge l@(Bin sizeL kx x lx rx) r@(Bin sizeR ky y ly ry)
  =    if delta*sizeL <= sizeR then balance ky y (merge l ly) ry
  else if delta*sizeR <= sizeL then balance kx x lx (merge rx r)
  else                              glue l r


{--------------------------------------------------------------------
  Utility functions that return sub-ranges of the original
  tree. Some functions take a comparison function as argument to
  allow comparisons against infinite values. A function [cmplo k]
  should be read as [compare lo k].

  [trim cmplo cmphi t]  A tree that is either empty or where [cmplo k == LT]
                        and [cmphi k == GT] for the key [k] of the root.
  [filterGt cmp t]      A tree where for all keys [k]. [cmp k == LT]
  [filterLt cmp t]      A tree where for all keys [k]. [cmp k == GT]

  [split k t]           Returns two trees [l] and [r] where all keys
                        in [l] are <[k] and all keys in [r] are >[k].
  [splitLookup k t]     Just like [split] but also returns whether [k]
                        was found in the tree.
--------------------------------------------------------------------}

{--------------------------------------------------------------------
  [trim lo hi t] trims away all subtrees that surely contain no
  values between the range [lo] to [hi]. The returned tree is either
  empty or the key of the root is between @lo@ and @hi@.
--------------------------------------------------------------------}
private
trim : (Some k -> Ordering) -> (Some k -> Ordering) -> DMap k f -> DMap k f
trim _     _     Tip = Tip
trim cmplo cmphi t@(Bin _ kx _ l r)
  = case cmplo (MkSome kx) of
      LT => case cmphi (MkSome kx) of
              GT => t
              _  => trim cmplo cmphi l
      _  => trim cmplo cmphi r

private
trimLookupLo : GCompare k => Some k -> (Some k -> Ordering) -> DMap k f -> (Maybe (DSum k f), DMap k f)
trimLookupLo _  _     Tip = (Nothing,Tip)
trimLookupLo lo cmphi t@(Bin _ kx x l r)
  = case compare lo (MkSome kx) @{viaGCompare} of
      LT => case cmphi (MkSome kx) of
              GT => (lookupAssoc lo t, t)
              _  => trimLookupLo lo cmphi l
      GT => trimLookupLo lo cmphi r
      EQ => (Just (kx :=> x), trim (compare lo @{viaGCompare}) cmphi r)

{--------------------------------------------------------------------
  [filterGt k t] filter all keys >[k] from tree [t]
  [filterLt k t] filter all keys <[k] from tree [t]
--------------------------------------------------------------------}
private
filterGt : GCompare k => (Some k -> Ordering) -> DMap k f -> DMap k f
filterGt cmp = go
  where
    go : DMap k f -> DMap k f
    go Tip              = Tip
    go (Bin _ kx x l r) = case cmp (MkSome kx) of
              LT => combine kx x (go l) r
              GT => go r
              EQ => r

private
filterLt : GCompare k => (Some k -> Ordering) -> DMap k f -> DMap k f
filterLt cmp = go
  where
    go : DMap k f -> DMap k f
    go Tip              = Tip
    go (Bin _ kx x l r) = case cmp (MkSome kx) of
          LT => go l
          GT => combine kx x l (go r)
          EQ => l



{--------------------------------------------------------------------
  Query
--------------------------------------------------------------------}

-- | /O(log n)/. Is the key a member of the map? See also 'notMember'.
export
member : GCompare k => k a -> DMap k f -> Bool
member k = isJust . lookup k

-- | /O(log n)/. Is the key not a member of the map? See also 'member'.
export
notMember : GCompare k => k v -> DMap k f -> Bool
notMember k m = not (member k m)

-- | /O(log n)/. Find the value at a key.
-- Calls 'error' when the element can not be found.
-- Consider using 'lookup' when elements may not be present.
private
find : GCompare k => k v -> DMap k f -> f v
find k m = case lookup k m of
    --Nothing => error "DMap.find: element not in the map"
    Nothing => assert_total $ prim__crash (f v) "DMap.find: element not in the map"
    Just v  => v

-- | /O(log n)/. The expression @('findWithDefault' def k map)@ returns
-- the value at key @k@ or returns default value @def@
-- when the key is not in the map.
export
findWithDefault : GCompare k => f v -> k v -> DMap k f -> f v
findWithDefault def k m = case lookup k m of
    Nothing => def
    Just v  => v

{--------------------------------------------------------------------
  Insertion
--------------------------------------------------------------------}

-- | /O(log n)/. Insert a new key and value in the map.
-- If the key is already present in the map, the associated value is
-- replaced with the supplied value. 'insert' is equivalent to
-- @'insertWith' 'const'@.
export
insert : (impl : GCompare k) => k v -> f v -> DMap k f -> DMap k f
insert kx x = evalState False . go
  where
    go : DMap k f -> State Bool (DMap k f)
    go Tip = put True >> pure (singleton kx x)
    go t@(Bin sz ky y l r) = case gcompare kx ky @{impl} of
      GLT => do
        l' <- go l
        sizeChange <- get
        -- originally pointer equality was used to see if the tree was modified
        if sizeChange then pure (balance ky y l' r)
                      else pure t
      GGT => do
        r' <- go r
        sizeChange <- get
        -- as above
        if sizeChange then pure (balance ky y l r')
                      else pure t
      GEQ => pure (Bin sz kx x l r)

-- | /O(log n)/. Insert a new key and value in the map if the key
-- is not already present. If the key is already present, @insertR@
-- does nothing.
private
insertR : (impl : GCompare k) => k v -> f v -> DMap k f -> DMap k f
insertR kx x = go
    where
        go : DMap k f -> DMap k f
        go Tip = singleton kx x
        go t@(Bin sz ky y l r) = case gcompare kx ky @{impl} of
            GLT => let l' = go l
                   -- ponter equality used before on trees
                   in if size l' == size l
                      then t
                      else balance ky y l' r
            GGT => let r' = go r
                   -- as above
                   in if size r' == size r
                   then t
                   else balance ky y l r'
            GEQ => t

-- | /O(log n)/. Insert with a function, combining key, new value and old value.
-- @'insertWithKey' f key value mp@
-- will insert the entry @key :=> value@ into @mp@ if key does
-- not exist in the map. If the key does exist, the function will
-- insert the entry @key :=> f key new_value old_value@.
-- Note that the key passed to f is the same key passed to 'insertWithKey'.
export
insertWithKey : (impl : GCompare k) => (k v -> f v -> f v -> f v) -> k v -> f v -> DMap k f -> DMap k f
insertWithKey func kx x = go
  where
    go : DMap k f -> DMap k f
    go Tip = singleton kx x
    go (Bin sy ky y l r) =
        case gcompare kx ky @{impl} of
            GLT => balance ky y (go l) r
            GGT => balance ky y l (go r)
            GEQ => Bin sy kx (func kx x y) l r

-- | /O(log n)/. Insert with a function, combining new value and old value.
-- @'insertWith' f key value mp@
-- will insert the entry @key :=> value@ into @mp@ if key does
-- not exist in the map. If the key does exist, the function will
-- insert the entry @key :=> f new_value old_value@.
export
insertWith : GCompare k => (f v -> f v -> f v) -> k v -> f v -> DMap k f -> DMap k f
insertWith f = insertWithKey (\_ => \x' => \y' => f x' y')

-- | /O(log n)/. Combines insert operation with old value retrieval.
-- The expression (@'insertLookupWithKey' f k x map@)
-- is a pair where the first element is equal to (@'lookup' k map@)
export
insertLookupWithKey : (impl : GCompare k)
                   => (k v -> f v -> f v -> f v)
                   -> k v
                   -> f v
                   -> DMap k f
                   -> (Maybe (f v), DMap k f)
insertLookupWithKey func kx x = go
  where
    go : DMap k f -> (Maybe (f v), DMap k f)
    go Tip = (Nothing, singleton kx x)
    go (Bin sy ky y l r) =
        case gcompare kx ky @{impl} of
            GLT => let (found, l') = go l
                  in (found, balance ky y l' r)
            GGT => let (found, r') = go r
                  in (found, balance ky y l r')
            GEQ => (Just y, Bin sy kx (func kx x y) l r)

{--------------------------------------------------------------------
  Deletion
  [delete] is the inlined version of [deleteWith (\k x -> Nothing)]
--------------------------------------------------------------------}

-- | /O(log n)/. Delete a key and its value from the map. When the key is not
-- a member of the map, the original map is returned.
--delete :: forall k f v. GCompare k => k v -> DMap k f -> DMap k f
export
delete : (impl : GCompare k) => k v -> DMap k f -> DMap k f
delete k' = go
  where
    go : DMap k f -> DMap k f
    go Tip = Tip
    go (Bin _ kx x l r) =
        case gcompare k' kx @{impl} of
            GLT => balance kx x (go l) r
            GGT => balance kx x l (go r)
            GEQ => glue l r

-- | /O(log n)/. Adjust a value at a specific key. When the key is not
-- a member of the map, the original map is returned.
adjustWithKey : (impl : GCompare k) => (k v -> f v -> f v) -> k v -> DMap k f -> DMap k f
adjustWithKey f0 k0 = go f0 k0
  where
    go : (k v -> f v -> f v) -> k v -> DMap k f -> DMap k f
    go f k Tip = Tip
    go f k (Bin sx kx x l r) =
      case gcompare k kx @{impl} of
        GLT => Bin sx kx x (go f k l) r
        GGT => Bin sx kx x l (go f k r)
        GEQ => Bin sx kx (f kx x) l r

-- | /O(log n)/. Update a value at a specific key with the result of the provided function.
-- When the key is not
-- a member of the map, the original map is returned.
adjust : GCompare k => (f v -> f v) -> k v -> DMap k f -> DMap k f
adjust f = adjustWithKey (\_ => \x => f x)

-- | /O(log n)/. The expression (@'updateWithKey' f k map@) updates the
-- value @x@ at @k@ (if it is in the map). If (@f k x@) is 'Nothing',
-- the element is deleted. If it is (@'Just' y@), the key @k@ is bound
-- to the new value @y@.
export
updateWithKey : (impl : GCompare k) => (k v -> f v -> Maybe (f v)) -> k v -> DMap k f -> DMap k f
updateWithKey func key = go
  where
    go : DMap k f -> DMap k f
    go Tip = Tip
    go (Bin sx kx x l r) =
        case gcompare key kx @{impl} of
           GLT => balance kx x (go l) r
           GGT => balance kx x l (go r)
           GEQ => case func kx x of
                   Just x' => Bin sx kx x' l r
                   Nothing => glue l r

-- | /O(log n)/. The expression (@'update' f k map@) updates the value @x@
-- at @k@ (if it is in the map). If (@f x@) is 'Nothing', the element is
-- deleted. If it is (@'Just' y@), the key @k@ is bound to the new value @y@.
export
update : GCompare k => (f v -> Maybe (f v)) -> k v -> DMap k f -> DMap k f
update f = updateWithKey (\_ => \x => f x)

-- | /O(log n)/. Lookup and update. See also 'updateWithKey'.
-- The function returns changed value, if it is updated.
-- Returns the original key value if the map entry is deleted.
export
updateLookupWithKey : (impl : GCompare k) => (k v -> f v -> Maybe (f v)) -> k v -> DMap k f -> (Maybe (f v), DMap k f)
updateLookupWithKey func key = go
 where
   go : DMap k f -> (Maybe (f v), DMap k f)
   go Tip = (Nothing,Tip)
   go (Bin sx kx x l r) =
          case gcompare key kx @{impl} of
               GLT => let (found,l') = go l in (found,balance kx x l' r)
               GGT => let (found,r') = go r in (found,balance kx x l r')
               GEQ => case func kx x of
                       Just x' => (Just x',Bin sx kx x' l r)
                       Nothing => (Just x,glue l r)

-- | /O(log n)/. The expression (@'alter' f k map@) alters the value @x@ at @k@, or absence thereof.
-- 'alter' can be used to insert, delete, or update a value in a 'Map'.
-- In short : @'lookup' k ('alter' f k m) = f ('lookup' k m)@.
export
alter : (impl : GCompare k) => (Maybe (f v) -> Maybe (f v)) -> k v -> DMap k f -> DMap k f
alter func key = go
  where
    go : DMap k f -> DMap k f
    go Tip = case func Nothing of
               Nothing => Tip
               Just x  => singleton key x

    go (Bin sx kx x l r) = case gcompare key kx @{impl} of
               GLT => balance kx x (go l) r
               GGT => balance kx x l (go r)
               GEQ => case func (Just x) of
                       Just x' => Bin sx kx x' l r
                       Nothing => glue l r

-- | Works the same as 'alter' except the new value is returned in some 'Functor' @f@.
-- In short : @(\v' -> alter (const v') k dm) <$> f (lookup k dm)@
export
alterF : (impl : GCompare k) => Functor f => k v -> (Maybe (g v) -> f (Maybe (g v))) -> DMap k g -> f (DMap k g)
alterF key func = go
  where
    go : DMap k g -> f (DMap k g)
    go Tip = maybe Tip (singleton key) <$> func Nothing

    go (Bin sx kx x l r) = case gcompare key kx @{impl} of
      GLT => (\l' => balance kx x l' r) <$> go l
      GGT => (\r' => balance kx x l r') <$> go r
      GEQ => maybe (glue l r) (\x' => Bin sx kx x' l r) <$> func (Just x)

{--------------------------------------------------------------------
  Indexing
--------------------------------------------------------------------}

-- | /O(log n)/. Lookup the /index/ of a key. The index is a number from
-- /0/ up to, but not including, the 'size' of the map.
export
lookupIndex : (impl : GCompare k) => k v -> DMap k f -> Maybe Int
lookupIndex key = go 0
  where
    go : Int -> DMap k f -> Maybe Int
    go idx Tip  = Nothing
    go idx (Bin _ kx _ l r)
      = case gcompare key kx @{impl} of
          GLT => go idx l
          GGT => go (idx + size l + 1) r
          GEQ => Just (idx + size l)

-- | /O(log n)/. Return the /index/ of a key. The index is a number from
-- /0/ up to, but not including, the 'size' of the map. Calls 'error' when
-- the key is not a 'member' of the map.
export
findIndex : GCompare k => k v -> DMap k f -> Int
findIndex k t
  = case lookupIndex k t of
      Nothing  => assert_total $ idris_crash "Map.findIndex: element is not in the map"
      Just idx => idx

-- | /O(log n)/. Retrieve an element by /index/. Calls 'error' when an
-- invalid index is used.
export
elemAt : Int -> DMap k f -> DSum k f
elemAt _ Tip = assert_total $ idris_crash "Map.elemAt: index out of range"
elemAt i (Bin _ kx x l r)
  = case compare i sizeL of
      LT => elemAt i l
      GT => elemAt (i - sizeL - 1) r
      EQ => kx :=> x
  where
    sizeL : Int
    sizeL = size l

-- | /O(log n)/. Update the element at /index/. Does nothing when an
-- invalid index is used.
export
updateAt : ({0 v : a} -> k v -> f v -> Maybe (f v)) -> Int -> DMap k f -> DMap k f
updateAt func i0 t = go i0 t
 where
    go : Int -> DMap k f -> DMap k f
    go _ Tip  = Tip
    go i (Bin sx kx x l r) = case compare i sizeL of
      LT => balance kx x (go i l) r
      GT => balance kx x l (go (i-sizeL-1) r)
      EQ => case func kx x of
              Just x' => Bin sx kx x' l r
              Nothing => glue l r
      where
        sizeL : Int
        sizeL = size l

-- | /O(log n)/. Delete the element at /index/.
-- Defined as (@'deleteAt' i map = 'updateAt' (\k x -> 'Nothing') i map@).
export
deleteAt : Int -> DMap k f -> DMap k f
deleteAt i m
  = updateAt (\_ => \_ => Nothing) i m

{--------------------------------------------------------------------
  Minimal, Maximal
--------------------------------------------------------------------}

export
lookupMin : DMap k f -> Maybe (DSum k f)
lookupMin m = case m of
      Tip => Nothing
      Bin _ kx x l _ => Just $ go kx x l
  where
    go : k v -> f v -> DMap k f -> DSum k f
    go kx x Tip = kx :=> x
    go _  _ (Bin _ kx x l _) = go kx x l

-- | /O(log n)/. The minimal key of the map. Calls 'error' is the map is empty.
export
findMin : DMap k f -> DSum k f
findMin m = case lookupMin m of
  Just x => x
  Nothing => assert_total $ idris_crash "Map.findMin: empty map has no minimal element"

export
lookupMax : DMap k f -> Maybe (DSum k f)
lookupMax m = case m of
      Tip => Nothing
      Bin _ kx x _ r => Just $ go kx x r
  where
    go : k v -> f v -> DMap k f -> DSum k f
    go kx x Tip = kx :=> x
    go _  _ (Bin _ kx x _ r) = go kx x r

-- | /O(log n)/. The maximal key of the map. Calls 'error' is the map is empty.
export
findMax : DMap k f -> DSum k f
findMax m = case lookupMax m of
  Just x => x
  Nothing => assert_total $ idris_crash "Map.findMax: empty map has no maximal element"

-- | /O(log n)/. Delete the minimal key. Returns an empty map if the map is empty.
export
deleteMin : DMap k f -> DMap k f
deleteMin (Bin _ _  _ Tip r)  = r
deleteMin (Bin _ kx x l r)    = balance kx x (deleteMin l) r
deleteMin Tip                 = Tip

-- | /O(log n)/. Delete the maximal key. Returns an empty map if the map is empty.
export
deleteMax : DMap k f -> DMap k f
deleteMax (Bin _ _  _ l Tip)  = l
deleteMax (Bin _ kx x l r)    = balance kx x l (deleteMax r)
deleteMax Tip                 = Tip

-- | /O(log n)/. Update the value at the minimal key.
export
updateMinWithKey : ({0 v : a} -> k v -> f v -> Maybe (f v)) -> DMap k f -> DMap k f
updateMinWithKey func = go
 where
  go : DMap k f -> DMap k f
  go (Bin sx kx x Tip r) = case func kx x of
                            Nothing => r
                            Just x' => Bin sx kx x' Tip r
  go (Bin _ kx x l r)    = balance kx x (go l) r
  go Tip                 = Tip

-- | /O(log n)/. Update the value at the maximal key.
export
updateMaxWithKey : ({0 v : a} -> k v -> f v -> Maybe (f v)) -> DMap k f -> DMap k f
updateMaxWithKey func = go
 where
  go : DMap k f -> DMap k f
  go (Bin sx kx x l Tip) = case func kx x of
                            Nothing => l
                            Just x' => Bin sx kx x' l Tip
  go (Bin _ kx x l r)    = balance kx x l (go r)
  go Tip                 = Tip

{--------------------------------------------------------------------
  Split
--------------------------------------------------------------------}

-- | /O(log n)/. The expression (@'split' k map@) is a pair @(map1,map2)@ where
-- the keys in @map1@ are smaller than @k@ and the keys in @map2@ larger than @k@.
-- Any key equal to @k@ is found in neither @map1@ nor @map2@.
export
split : (impl : GCompare k) => k v -> DMap k f -> (DMap k f, DMap k f)
split key = go
  where
    go : DMap k f -> (DMap k f, DMap k f)
    go Tip              = (Tip, Tip)
    go (Bin _ kx x l r) = case gcompare key kx @{impl} of
          GLT => let (lt, gt) = go l in (lt, combine kx x gt r)
          GGT => let (lt, gt) = go r in (combine kx x l lt, gt)
          GEQ => (l, r)

-- | /O(log n)/. The expression (@'splitLookup' k map@) splits a map just
-- like 'split' but also returns @'lookup' k map@.
export
splitLookup : (impl : GCompare k) => k v -> DMap k f -> (DMap k f, Maybe (f v), DMap k f)
splitLookup key = go
  where
    go : DMap k f -> (DMap k f, Maybe (f v), DMap k f)
    go Tip              = (Tip, Nothing, Tip)
    go (Bin _ kx x l r) = case gcompare key kx @{impl} of
      GLT => let (lt, z, gt) = go l in (lt, z, combine kx x gt r)
      GGT => let (lt, z, gt) = go r in (combine kx x l lt, z, gt)
      GEQ => (l, Just x, r)

-- | /O(log n)/. The expression (@'splitMember' k map@) splits a map just
-- like 'split' but also returns @'member' k map@.
private
splitMember : (impl : GCompare k) => k v -> DMap k f -> (DMap k f, Bool, DMap k f)
splitMember key = go
  where
    go : DMap k f -> (DMap k f, Bool, DMap k f)
    go Tip              = (Tip, False, Tip)
    go (Bin _ kx x l r) = case gcompare key kx @{impl} of
      GLT => let (lt, z, gt) = go l in (lt, z, combine kx x gt r)
      GGT => let (lt, z, gt) = go r in (combine kx x l lt, z, gt)
      GEQ => (l, True, r)

-- | /O(log n)/.
private
splitLookupWithKey : (impl : GCompare k) => k v -> DMap k f -> (DMap k f, Maybe (k v, f v), DMap k f)
splitLookupWithKey key = go
  where
    go : DMap k f -> (DMap k f, Maybe (k v, f v), DMap k f)
    go Tip              = (Tip, Nothing, Tip)
    go (Bin _ kx x l r) = case gcompare key kx @{impl} of
      GLT => let (lt, z, gt) = go l in (lt, z, combine kx x gt r)
      GGT => let (lt, z, gt) = go r in (combine kx x l lt, z, gt)
      GEQ => (l, Just (kx, x), r)

{--------------------------------------------------------------------
  Eq converts the tree to a list. In a lazy setting, this
  actually seems one of the faster methods to compare two trees
  and it is certainly the simplest :-)
--------------------------------------------------------------------}
{-
instance (GEq k, Has' Eq k f) => Eq (DMap k f) where
  t1 == t2  = (size t1 == size t2) && (toAscList t1 == toAscList t2)
-}

{--------------------------------------------------------------------
  Union.
--------------------------------------------------------------------}

-- | /O(m*log(n\/m + 1)), m <= n/.
-- The expression (@'union' t1 t2@) takes the left-biased union of @t1@ and @t2@.
-- It prefers @t1@ when duplicate keys are encountered,
-- i.e. (@'union' == 'unionWith' 'const'@).
export
union : GCompare k => DMap k f -> DMap k f -> DMap k f
union t1 Tip  = t1
union t1 (Bin _ kx x Tip Tip) = insertR kx x t1
union Tip t2  = t2
union (Bin _ kx x Tip Tip) t2 = insert kx x t2
union t1@(Bin _ k1 x1 l1 r1) t2 = case split k1 t2 of
  (l2, r2) => combine k1 x1 (l1 `union` l2) (r1 `union` r2)

-- | The union of a list of maps:
--   (@'unions' == 'Prelude.foldl' 'union' 'empty'@).
export
unions : GCompare k => List (DMap k f) -> DMap k f
unions ts = foldl union empty ts

{--------------------------------------------------------------------
  Semigroup, Monoid
--------------------------------------------------------------------}

export
implementation (GCompare k) => Semigroup (DMap k f) where
  (<+>) = union

export
implementation (GCompare k) => Monoid (DMap k f) where
    neutral = empty

{--------------------------------------------------------------------
  Union with a combining function
--------------------------------------------------------------------}

-- | /O(n+m)/.
-- Union with a combining function.
export
unionWithKey : GCompare k => ({0 v : a} -> k v -> f v -> f v -> f v) -> DMap k f -> DMap k f -> DMap k f
unionWithKey _ t1 Tip  = t1
unionWithKey _ Tip t2  = t2
unionWithKey f (Bin _ k1 x1 l1 r1) t2 = case splitLookup k1 t2 of
  (l2, mx2, r2) => let 
      l1l2 = unionWithKey f l1 l2
      r1r2 = unionWithKey f r1 r2
    in case mx2 of
      Nothing => combine k1 x1 l1l2 r1r2
      Just x2 => combine k1 (f k1 x1 x2) l1l2 r1r2
    
-- | The union of a list of maps, with a combining operation:
--   (@'unionsWithKey' f == 'Prelude.foldl' ('unionWithKey' f) 'empty'@).
export
unionsWithKey : GCompare k => ({0 v : a} -> k v -> f v -> f v -> f v) -> List (DMap k f) -> DMap k f
unionsWithKey f ts = foldl (unionWithKey f) empty ts

{--------------------------------------------------------------------
  Difference
--------------------------------------------------------------------}

-- | /O(m * log (n\/m + 1)), m <= n/. Difference of two maps.
-- Return elements of the first map not existing in the second map.
export
difference : GCompare k => DMap k f -> DMap k g -> DMap k f
difference Tip _   = Tip
difference t1 Tip  = t1
difference t1 (Bin _ k2 x2 l2 r2) = case split k2 t1 of
  (l1, r1) => let
      l1l2 = l1 `difference` l2
      r1r2 = r1 `difference` r2
    in if size t1 == size l1l2 + size r1r2 then t1
                                           else merge l1l2 r1r2

-- | /O(n+m)/. Difference with a combining function. When two equal keys are
-- encountered, the combining function is applied to the key and both values.
-- If it returns 'Nothing', the element is discarded (proper set difference). If
-- it returns (@'Just' y@), the element is updated with a new value @y@.
export
differenceWithKey : (impl : GCompare k)
                 => ({0 v : a} -> k v -> f v -> g v -> Maybe (f v))
                 -> DMap k f
                 -> DMap k g
                 -> DMap k f
differenceWithKey _ Tip _   = Tip
differenceWithKey _ t1 Tip  = t1
differenceWithKey f (Bin _ k1 x1 l1 r1) t2 = case splitLookup k1 t2 of
  (l2, mx2, r2) => let
      l1l2 = differenceWithKey f l1 l2
      r1r2 = differenceWithKey f r1 r2
    in case mx2 of
      Nothing => combine k1 x1 l1l2 r1r2
      Just x2 => case f k1 x1 x2 of
        Nothing   => merge l1l2 r1r2
        Just x1x2 => combine k1 x1x2 l1l2 r1r2
    

{--------------------------------------------------------------------
  Intersection
--------------------------------------------------------------------}

-- | /O(m * log (n\/m + 1), m <= n/. Intersection of two maps.
-- Return data in the first map for the keys existing in both maps.
-- (@'intersection' m1 m2 == 'intersectionWith' 'const' m1 m2@).
export
intersection : GCompare k => DMap k f -> DMap k f -> DMap k f
intersection Tip _ = Tip
intersection _ Tip = Tip
intersection t1@(Bin s1 k1 x1 l1 r1) t2 =
  let (l2, found, r2) = splitMember k1 t2
      l1l2 = intersection l1 l2
      r1r2 = intersection r1 r2
  in if found
     then if size l1l2 == size l1 && size r1r2 == size r1
          then t1
          else combine k1 x1 l1l2 r1r2
     else merge l1l2 r1r2


-- | /O(m * log (n\/m + 1), m <= n/. Intersection with a combining function.
export
intersectionWithKey : GCompare k => ({0 v : a} -> k v -> f v -> g v -> h v) -> DMap k f -> DMap k g -> DMap k h
intersectionWithKey _ Tip _ = Tip
intersectionWithKey _ _ Tip = Tip
intersectionWithKey f (Bin s1 k1 x1 l1 r1) t2 =
  let (l2, found, r2) = splitLookup k1 t2
      l1l2 = intersectionWithKey f l1 l2
      r1r2 = intersectionWithKey f r1 r2
  in case found of
       Nothing => merge l1l2 r1r2
       Just x2 => combine k1 (f k1 x1 x2) l1l2 r1r2

{--------------------------------------------------------------------
  Submap
--------------------------------------------------------------------}
private
submap' : GCompare k => ({0 v : a} -> k v -> k v -> f v -> g v -> Bool) -> DMap k f -> DMap k g -> Bool
submap' _ Tip _ = True
submap' _ _ Tip = False
submap' f (Bin _ kx x l r) t
  = let
      (lt, found, gt) = splitLookupWithKey kx t
    in case found of
      Nothing => False
      Just (ky, y) => f kx ky x y && submap' f l lt && submap' f r gt

{- | /O(n+m)/.
 The expression (@'isSubmapOfBy' f t1 t2@) returns 'True' if
 all keys in @t1@ are in tree @t2@, and when @f@ returns 'True' when
 applied to their respective keys and values.
-}
export
isSubmapOfBy : GCompare k => ({0 v : a} -> k v -> k v -> f v -> g v -> Bool) -> DMap k f -> DMap k g -> Bool
isSubmapOfBy f t1 t2 = (size t1 <= size t2) && (submap' f t1 t2)

{-
-- | /O(n+m)/.
-- This function is defined as (@'isSubmapOf' = 'isSubmapOfBy' 'eqTagged')@).
--
export
isSubmapOf
  :: forall k f
  .  (GCompare k, Has' Eq k f)
  => DMap k f -> DMap k f -> Bool
isSubmapOf m1 m2 = isSubmapOfBy (\k _ x0 x1 -> has' @Eq @f k (x0 == x1)) m1 m2
-}

{- | /O(n+m)/. Is this a proper submap? (ie. a submap but not equal).
 The expression (@'isProperSubmapOfBy' f m1 m2@) returns 'True' when
 @m1@ and @m2@ are not equal,
 all keys in @m1@ are in @m2@, and when @f@ returns 'True' when
 applied to their respective keys and values.
-}
export
isProperSubmapOfBy : GCompare k => ({0 v : a} -> k v -> k v -> f v -> g v -> Bool) -> DMap k f -> DMap k g -> Bool
isProperSubmapOfBy f t1 t2 = (size t1 < size t2) && (submap' f t1 t2)

{-
-- | /O(n+m)/. Is this a proper submap? (ie. a submap but not equal).
-- Defined as (@'isProperSubmapOf' = 'isProperSubmapOfBy' 'eqTagged'@).
export
isProperSubmapOf
  :: forall k f
  .  (GCompare k, Has' Eq k f)
  => DMap k f -> DMap k f -> Bool
isProperSubmapOf m1 m2
  = isProperSubmapOfBy (\k _ x0 x1 -> has' @Eq @f k (x0 == x1)) m1 m2
-}

{--------------------------------------------------------------------
  Filter and partition
--------------------------------------------------------------------}
-- | /O(n)/. Filter all keys\/values that satisfy the predicate.
export
filterWithKey : GCompare k => ({0 v : a} -> k v -> f v -> Bool) -> DMap k f -> DMap k f
filterWithKey p = go
  where
    go : DMap k f -> DMap k f
    go Tip = Tip
    go t@(Bin _ kx x l r)
      = let
          l' = go l
          r' = go r
        in if p kx x then if size l' == size l && size r' == size r
                          then t
                          else combine kx x l' r'
                     else merge l' r'

-- | /O(n)/. Partition the map according to a predicate. The first
-- map contains all elements that satisfy the predicate, the second all
-- elements that fail the predicate. See also 'split'.
export
partitionWithKey : (impl : GCompare k) => ({0 v : a} -> k v -> f v -> Bool) -> DMap k f -> (DMap k f, DMap k f)
partitionWithKey p0 m0 = go p0 m0
  where
    go : ({0 v : a} -> k v -> f v -> Bool) -> DMap k f -> (DMap k f, DMap k f)
    go _ Tip = (Tip, Tip)
    go p (Bin _ kx x l r) = let
        (l1, l2) = go p l
        (r1, r2) = go p r
      in if p kx x then (combine kx x l1 r1, merge l2 r2)
                   else (merge l1 r1, combine kx x l2 r2)

-- | /O(n)/. Map keys\/values and collect the 'Just' results.
mapMaybeWithKey : (impl : GCompare k) => ({0 v : a} -> k v -> f v -> Maybe (g v)) -> DMap k f -> DMap k g
mapMaybeWithKey func = go
  where
    go : DMap k f -> DMap k g
    go Tip = Tip
    go (Bin _ kx x l r) = case func kx x of
        Just y  => combine kx y (go l) (go r)
        Nothing => merge (go l) (go r)

-- | /O(n)/. Map values and collect the 'Just' results.
export
mapMaybe : GCompare k => ({0 v : a} -> f v -> Maybe (g v)) -> DMap k f -> DMap k g
mapMaybe f = mapMaybeWithKey (const f)

-- | /O(n)/. Map keys\/values and separate the 'Left' and 'Right' results.
export
mapEitherWithKey : GCompare k =>
  ({0 v : a} -> k v -> f v -> Either (g v) (h v)) -> DMap k f -> (DMap k g, DMap k h)
mapEitherWithKey f0 = go f0
  where
    go : ({0 v : a} -> k v -> f v -> Either (g v) (h v))
      -> DMap k f
      -> (DMap k g, DMap k h)
    go _ Tip = (Tip, Tip)
    go f (Bin _ kx x l r) = let
        (l1, l2) = mapEitherWithKey f l
        (r1, r2) = mapEitherWithKey f r
      in case f kx x of
        Left y  => (combine kx y l1 r1, merge l2 r2)
        Right z => (merge l1 r1, combine kx z l2 r2)

{--------------------------------------------------------------------
  Folds
--------------------------------------------------------------------}

-- | /O(n)/. Post-order fold.  The function will be applied from the lowest
-- value to the highest.
export
foldrWithKey : ({0 v : a} -> k v -> f v -> b -> b) -> b -> DMap k f -> b
foldrWithKey func = go
  where
    go : b -> DMap k f -> b
    go z Tip              = z
    go z (Bin _ kx x l r) = go (func kx x (go z r)) l

-- | /O(n)/. Pre-order fold.  The function will be applied from the highest
-- value to the lowest.
export
foldlWithKey : ({0 v : a} -> b -> k v -> f v -> b) -> b -> DMap k f -> b
foldlWithKey func = go
  where
    go : b -> DMap k f -> b
    go z Tip              = z
    go z (Bin _ kx x l r) = go (func (go z l) kx x) r

{--------------------------------------------------------------------
  Lists
  use [foldlStrict] to reduce demand on the control-stack
--------------------------------------------------------------------}

-- | /O(n*log n)/. Build a map from a list of key\/value pairs. See also 'fromAscList'.
-- If the list contains more than one value for the same key, the last value
-- for the key is retained.
export
fromList : GCompare k => List (DSum k f) -> DMap k f
fromList xs
  = foldl ins empty xs
  where
    ins : DMap k f -> DSum k f -> DMap k f
    ins t (k :=> x) = insert k x t

-- | /O(n*log n)/. Build a map from a list of key\/value pairs with a combining function. See also 'fromAscListWithKey'.
export
fromListWithKey : GCompare k => ({0 v : a} -> k v -> f v -> f v -> f v) -> List (DSum k f) -> DMap k f
fromListWithKey func xs
  = foldl (ins func) empty xs
  where
    ins : ({0 v : a} -> k v -> f v -> f v -> f v) -> DMap k f -> DSum k f -> DMap k f
    ins func t (k :=> x) = insertWithKey func k x t

-- | /O(n)/. Convert to an ascending list.
export
toAscList : DMap k f -> List (DSum k f)
toAscList t = foldrWithKey (\k => \x => \xs => (k :=> x) :: xs) [] t

-- | /O(n)/. Convert to a list of key\/value pairs.
export
toList : DMap k f -> List (DSum k f)
toList t = toAscList t

-- | /O(n)/. Convert to a descending list.
export
toDescList : DMap k f -> List (DSum k f)
toDescList t  = foldlWithKey (\xs => \k => \x => (k :=> x) :: xs) [] t

{--------------------------------------------------------------------
  Building trees from ascending/descending lists can be done in linear time.

  Note that if [xs] is ascending that:
    fromAscList xs       == fromList xs
    fromAscListWith f xs == fromListWith f xs
--------------------------------------------------------------------}

-- | /O(n)/. Build a map from an ascending list of distinct elements in linear time.
-- /The precondition is not checked./
export
fromDistinctAscList : List (DSum k f) -> DMap k f
fromDistinctAscList xs = build const (cast $ length xs) xs
  where
    -- 1) use continutations so that we use heap space instead of stack space.
    -- 2) special case for n==5 to build bushier trees.

    buildB : DMap k f -> k v -> f v -> (DMap k f -> a -> b) -> DMap k f -> a -> b
    buildB l k x c r zs = c (bin k x l r) zs

    mutual
      build : (DMap k f -> List (DSum k f) -> b) -> Int -> List (DSum k f) -> b
      build c 0 xs' = c Tip xs'
      build c 5 xs' = case xs' of
        ((k1 :=> x1) :: (k2 :=> x2) :: (k3 :=> x3) :: (k4 :=> x4) :: (k5 :=> x5) :: xx)
          => c (bin k4 x4 (bin k2 x2 (singleton k1 x1) (singleton k3 x3)) (singleton k5 x5)) xx
        _ => assert_total $ idris_crash "fromDistinctAscList build"
      build c n xs' = build (buildR nr c) nl xs'
        where
          nl, nr : Int  
          nl = n `div` 2
          nr = n - nl - 1

      buildR : Int -> (DMap k f -> List (DSum k f) -> b) -> DMap k f -> List (DSum k f) -> b
      buildR n c l ((k :=> x) :: ys) = build (buildB l k x c) n ys
      buildR _ _ _ []                = assert_total $ idris_crash "fromDistinctAscList buildR []"

    

-- | /O(n)/. Build a map from an ascending list in linear time with a
-- combining function for equal keys.
-- /The precondition (input list is ascending) is not checked./
export
fromAscListWithKey : (impl : GEq k) => ({0 v : a} -> k v -> f v -> f v -> f v) -> List (DSum k f) -> DMap k f
fromAscListWithKey func xs = fromDistinctAscList (combineEq func xs)
  where
    combineEq' : ({0 v : a} -> k v -> f v -> f v -> f v) -> DSum k f -> List (DSum k f) -> List (DSum k f)
    combineEq' f z [] = [z]
    combineEq' f z@(kz :=> zz) (x@(kx :=> xx) :: xs') = case geq kx kz @{impl} of
      Just Refl   => let yy = func kx xx zz in combineEq' f (kx :=> yy) xs'
      Nothing     => z :: combineEq' func x xs'
    
    -- [combineEq f xs] combines equal elements with function [f] in an ordered list [xs]
    combineEq : ({0 v : a} -> k v -> f v -> f v -> f v) -> List (DSum k f) -> List (DSum k f)
    combineEq _ xs' = case xs' of
      []        => []
      [x]       => [x]
      (x :: xx) => combineEq' func x xx


-- | /O(n)/. Build a map from an ascending list in linear time.
-- /The precondition (input list is ascending) is not checked./
export
fromAscList : GEq k => List (DSum k f) -> DMap k f
fromAscList xs = fromAscListWithKey (\_ => \x => \_ => x) xs

{--------------------------------------------------------------------
  List variations
--------------------------------------------------------------------}

-- | /O(n)/. Return all key\/value pairs in the map in ascending key order.
export
assocs : DMap k f -> List (DSum k f)
assocs m = toList m

-- | /O(n)/. Return all keys of the map in ascending order.
--
-- > keys (fromList [(5,"a"), (3,"b")]) == [3,5]
-- > keys empty == []
export
keys : DMap k f -> List (Some k)
keys m = [MkSome k | (k :=> _) <- assocs m]

{--------------------------------------------------------------------
  Mapping
--------------------------------------------------------------------}

-- | /O(n)/. Map a function over all values in the map.
export
map : ({0 v : a} -> f v -> g v) -> DMap k f -> DMap k g
map func = go
  where
    go : DMap k f -> DMap k g
    go Tip = Tip
    go (Bin sx kx x l r) = Bin sx kx (func x) (go l) (go r)

-- | /O(n)/.
-- @'ffor' == 'flip' 'map'@ except we cannot actually use
-- 'flip' because of the lack of impredicative types.
export
ffor : DMap k f -> ({0 v : a} -> f v -> g v) -> DMap k g
ffor m f = map f m

-- | /O(n)/. Map a function over all values in the map.
export
mapWithKey : ({0 v : a} -> k v -> f v -> g v) -> DMap k f -> DMap k g
mapWithKey func = go
  where
    go : DMap k f -> DMap k g
    go Tip = Tip
    go (Bin sx kx x l r) = Bin sx kx (func kx x) (go l) (go r)

-- | /O(n)/.
-- @'fforWithKey' == 'flip' 'mapWithKey'@ except we cannot actually use
-- 'flip' because of the lack of impredicative types.
export
fforWithKey : DMap k f -> ({0 v : a} -> k v -> f v -> g v) -> DMap k g
fforWithKey m f = mapWithKey f m

-- | /O(n)/.
-- @'traverseWithKey' f m == 'fromList' <$> 'traverse' (\(k, v) -> (,) k <$> f k v) ('toList' m)@
-- That is, behaves exactly like a regular 'traverse' except that the traversing
-- function also has access to the key associated with a value.
export
traverseWithKey_ : Applicative t => ({0 v : a} -> k v -> f v -> t ()) -> DMap k f -> t ()
traverseWithKey_ func = go
  where
    go : DMap k f -> t ()
    go Tip = pure ()
    go (Bin 1 k v _ _) = func k v
    go (Bin s k v l r) = go l *> func k v *> go r

-- | /O(n)/.
-- @'forWithKey' == 'flip' 'traverseWithKey'@ except we cannot actually use
-- 'flip' because of the lack of impredicative types.
export
forWithKey_ : Applicative t => DMap k f -> ({0 v : a} -> k v -> f v -> t ()) -> t ()
forWithKey_ m f = traverseWithKey_ f m

-- | /O(n)/.
-- @'traverseWithKey' f m == 'fromList' <$> 'traverse' (\(k, v) -> (,) k <$> f k v) ('toList' m)@
-- That is, behaves exactly like a regular 'traverse' except that the traversing
-- function also has access to the key associated with a value.
export
traverseWithKey : Applicative t => ({0 v : a} -> k v -> f v -> t (g v)) -> DMap k f -> t (DMap k g)
traverseWithKey func = go
  where
    go : DMap k f -> t (DMap k g)
    go Tip = pure Tip
    go (Bin 1 k v _ _) = (\v' => Bin 1 k v' Tip Tip) <$> func k v
    go (Bin s k v l r) = flip (Bin s k) <$> go l <*> func k v <*> go r

-- | /O(n)/.
-- @'forWithKey' == 'flip' 'traverseWithKey'@ except we cannot actually use
-- 'flip' because of the lack of impredicative types.
export
forWithKey : Applicative t => DMap k f -> ({0 v : a} -> k v -> f v -> t (g v)) -> t (DMap k g)
forWithKey m f = traverseWithKey f m

-- | /O(n)/. The function 'mapAccumLWithKey' threads an accumulating
-- argument through the map in ascending order of keys.
export
mapAccumLWithKey : ({0 v : a'} -> a -> k v -> f v -> (a, g v)) -> a -> DMap k f -> (a, DMap k g)
mapAccumLWithKey func = go
  where
    go : a -> DMap k f -> (a, DMap k g)
    go a Tip               = (a,Tip)
    go a (Bin sx kx x l r) =
                 let (a1, l') = go a l
                     (a2, x') = func a1 kx x
                     (a3, r') = go a2 r
                 in (a3, Bin sx kx x' l' r')

-- | /O(n)/. The function 'mapAccumRWithKey' threads an accumulating
-- argument through the map in descending order of keys.
export
mapAccumRWithKey : ({0 v : a'} -> a -> k v -> f v -> (a, g v)) -> a -> DMap k f -> (a, DMap k g)
mapAccumRWithKey func = go
  where
    go : a -> DMap k f -> (a, DMap k g)
    go a Tip = (a,Tip)
    go a (Bin sx kx x l r) =
                 let (a1, r') = go a r
                     (a2, x') = func a1 kx x
                     (a3, l') = go a2 l
                 in (a3, Bin sx kx x' l' r')

-- | /O(n*log n)/.
-- @'mapKeysWith' c f s@ is the map obtained by applying @f@ to each key of @s@.
--
-- The size of the result may be smaller if @f@ maps two or more distinct
-- keys to the same new key.  In this case the associated values will be
-- combined using @c@.
export
mapKeysWith : GCompare k2
           => ({0 v : a} -> k2 v -> f v -> f v -> f v)
           -> ({0 v : a} -> k1 v -> k2 v) -> DMap k1 f -> DMap k2 f
mapKeysWith c func = fromListWithKey c . Prelude.map fFirst . toList
  where
    fFirst : DSum k1 f -> DSum k2 f
    fFirst (x :=> y) = (func x :=> y)

-- | /O(n)/.
-- @'mapKeysMonotonic' f s == 'mapKeys' f s@, but works only when @f@
-- is strictly monotonic.
-- That is, for any values @x@ and @y@, if @x@ < @y@ then @f x@ < @f y@.
-- /The precondition is not checked./
-- Semi-formally, we have:
--
-- > and [x < y ==> f x < f y | x <- ls, y <- ls]
-- >                     ==> mapKeysMonotonic f s == mapKeys f s
-- >     where ls = keys s
--
-- This means that @f@ maps distinct original keys to distinct resulting keys.
-- This function has better performance than 'mapKeys'.
export
mapKeysMonotonic : ({0 v : a} -> k1 v -> k2 v) -> DMap k1 f -> DMap k2 f
mapKeysMonotonic _ Tip = Tip
mapKeysMonotonic f (Bin sz k x l r) =
    Bin sz (f k) x (mapKeysMonotonic f l) (mapKeysMonotonic f r)

{-
{--------------------------------------------------------------------
  Ord
--------------------------------------------------------------------}

instance (GCompare k, Has' Eq k f, Has' Ord k f) => Ord (DMap k f) where
  compare m1 m2 = compare (toAscList m1) (toAscList m2)

{--------------------------------------------------------------------
  Read
--------------------------------------------------------------------}

instance (GCompare k, GRead k, Has' Read k f) => Read (DMap k f) where
  readPrec = parens $ prec 10 $ do
    Ident "fromList" <- lexP
    xs <- readPrec
    return (fromList xs)

  readListPrec = readListPrecDefault
-}

{--------------------------------------------------------------------
  Show
--------------------------------------------------------------------}
{-
instance (GShow k, Has' Show k f) => Show (DMap k f) where
    showsPrec p m = showParen (p>10)
        ( showString "fromList "
        . showsPrec 11 (toList m)
        )

-- | /O(n)/. Show the tree that implements the map. The tree is shown
-- in a compressed, hanging format. See 'showTreeWith'.
export
showTree :: (GShow k, Has' Show k f) => DMap k f -> String
showTree m
  = showTreeWith showElem True False m
  where
    showElem :: (GShow k, Has' Show k f) => k v -> f v -> String
    showElem k x  = show (k :=> x)
-}

private
showWide : Bool -> List (String) -> String -> String
showWide wide bars
  = if wide then showString (concat (reverse bars)) . showString "|\n"
            else id

private
node : String
node = "+--"

private
showsBars : List (String) -> ShowS
showsBars bars
  = case bars of
      [] => id
      (bar :: bars)  => showString (concat (reverse bars)) . showString node

private
withBar, withEmpty : List (String) -> List (String)
withBar bars   = "|  " :: bars
withEmpty bars = "   " :: bars

private
showsTreeHang : ({0 v : a} -> k v -> f v -> String) -> Bool -> List (String) -> DMap k f -> ShowS
showsTreeHang showelem wide bars t
  = case t of
      Tip => showsBars bars . showString "|\n"
      Bin _ kx x Tip Tip
          => showsBars bars . showString (showelem kx x) . showString "\n"
      Bin _ kx x l r
          => showsBars bars . showString (showelem kx x) . showString "\n" .
             showWide wide bars .
             showsTreeHang showelem wide (withBar bars) l .
             showWide wide bars .
             showsTreeHang showelem wide (withEmpty bars) r

private
showsTree : ({0 v : a} -> k v -> f v -> String) -> Bool -> List (String) -> List (String) -> DMap k f -> ShowS
showsTree showelem wide lbars rbars t
  = case t of
      Tip => showsBars lbars . showString "|\n"
      Bin _ kx x Tip Tip
          => showsBars lbars . showString (showelem kx x) . showString "\n"
      Bin _ kx x l r
          => showsTree showelem wide (withBar rbars) (withEmpty rbars) r .
             showWide wide rbars .
             showsBars lbars . showString (showelem kx x) . showString "\n" .
             showWide wide lbars .
             showsTree showelem wide (withEmpty lbars) (withBar lbars) l

{- | /O(n)/. The expression (@'showTreeWith' showelem hang wide map@) shows
 the tree that implements the map. Elements are shown using the @showElem@ function. If @hang@ is
 'True', a /hanging/ tree is shown otherwise a rotated tree is shown. If
 @wide@ is 'True', an extra wide version is shown.
-}
export
showTreeWith : ({0 v : a} -> k v -> f v -> String) -> Bool -> Bool -> DMap k f -> String
showTreeWith showelem hang wide t
  = if hang then (showsTreeHang showelem wide [] t) ""
            else (showsTree showelem wide [] [] t) ""

{--------------------------------------------------------------------
  Assertions
--------------------------------------------------------------------}

private
ordered : GCompare k => DMap k f -> Bool
ordered t
  = bounded (const True) (const True) t
  where
    bounded : (Some k -> Bool) -> (Some k -> Bool) -> DMap k f -> Bool
    bounded lo hi t'
      = case t' of
          Tip             => True
          Bin _ kx _ l r  => lo (MkSome kx)
                          && hi (MkSome kx)
                          && bounded lo (\s => (<) @{viaGCompare} s (MkSome kx)) l
                          && bounded (\s => (>) @{viaGCompare} s (MkSome kx)) hi r

-- | Exported only for "Debug.QuickCheck"
private
balanced : DMap k f -> Bool
balanced t
  = case t of
      Tip            => True
      Bin _ _ _ l r  => (size l + size r <= 1 || (size l <= delta*size r && size r <= delta*size l)) &&
                        balanced l && balanced r

private
validsize : DMap k f -> Bool
validsize t
  = (realsize t == Just (size t))
  where
    realsize : DMap k f -> Maybe Int
    realsize t'
      = case t' of
          Tip            => Just 0
          Bin sz _ _ l r => case (realsize l,realsize r) of
                            (Just n, Just m) => if n + m + 1 == sz then Just sz
                                                                   else Nothing
                            _                => Nothing

-- | /O(n)/. Test if the internal map structure is valid.
export
valid : GCompare k => DMap k f -> Bool
valid t = balanced t && ordered t && validsize t
