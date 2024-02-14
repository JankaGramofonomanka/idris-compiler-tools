module Data.ListEq

import Theory


public export
data ListEq : List a -> List a -> Type where
  Nil : ListEq Nil Nil
  (::) : (0 prf : x = y) -> ListEq xs ys -> ListEq (x :: xs) (y :: ys)

infix 6 :=:
public export
(:=:) : List a -> List a -> Type
(:=:) = ListEq

total
export
toEq : ListEq xs ys -> xs = ys
toEq Nil = Refl
toEq (prf :: prfs) = rewrite prf
                  in rewrite toEq prfs
                  in Refl

total
export
fromEq : {xs : List a} -> (xs = ys) -> ListEq xs ys
fromEq {xs = Nil} Refl = Nil
fromEq {xs = x :: xs} Refl = Refl :: fromEq {xs} Refl

total
export
rev : ListEq xs ys -> ListEq ys xs
rev Nil = Nil
rev (prf :: prfs) = revEq prf :: rev prfs

total
export
(++) : ListEq xs ys -> ListEq xs' ys' -> ListEq (xs ++ xs') (ys ++ ys')
Nil ++ prfs' = prfs'
(prf :: prfs) ++ prfs' = prf :: prfs ++ prfs'

total
export
split
   : {lxs, rxs, lys, rys : List a}
  -> ListEq (lxs ++ rxs) (lys ++ rys)
  -> Either
      ( lrys
     ** rrys
     ** ( lxs :=: (lys ++ lrys)
        , rxs :=: rrys
        , rys :=: (lrys ++ rrys)
        )
      )
      ( llys 
     ** rlys
     ** ( lxs :=: llys
        , rxs :=: (rlys ++ rys)
        , lys :=: (llys ++ rlys)
        )
      )

split {lxs = Nil, rxs = Nil, lys = Nil, rys = Nil} Nil = Right (Nil ** Nil ** (Nil, Nil, Nil))

split {lxs = Nil, rxs = (rx :: rxs), lys = Nil, rys = Nil} (prf :: prfs) impossible
split {lxs = Nil, rxs = (rx :: rxs), lys = Nil, rys = (ry :: rys)} (prf :: prfs)
  = Right (Nil ** Nil ** (Nil, prf :: prfs, Nil))
split {lxs = Nil, rxs = (rx :: rxs), lys = (ly :: lys), rys} (prf :: prfs)
  = Right (Nil ** ly :: lys ** (Nil, prf :: prfs, fromEq Refl))

split {lxs = (lx :: lxs), rxs, lys = Nil, rys = Nil} (prf :: prfs) impossible
split {lxs = (lx :: lxs), rxs, lys = Nil, rys = (ry :: rys)} (prf :: prfs)
  = Left ((lx :: lxs) ** rxs ** (fromEq Refl, fromEq Refl, revEq prf :: rev prfs))
split {lxs = (lx :: lxs), rxs, lys = (ly :: lys), rys} (prf :: prfs)
  = case split prfs of
    Left (lrys ** rrys ** (prf0, prf1, prf2)) => Left (lrys ** rrys ** (prf :: prf0, prf1, prf2))
    Right (llys ** rlys ** (prf0, prf1, prf2)) => Right (ly :: llys ** rlys ** (prf :: prf0, prf1, Refl :: prf2))

total
export
split' : {x : a}
      -> {lxs, rxs, lys, rys : List a}
      -> ListEq (lxs ++ (x :: rxs)) (lys ++ rys)
      -> Either
          ( lrys
         ** rrys
         ** ( lxs :=: lys ++ lrys
            , rxs :=: rrys
            , rys :=: lrys ++ x :: rrys
            )
          )
          ( llys
         ** rlys
         ** ( lxs :=: llys
            , rxs :=: rlys ++ rys
            , lys :=: llys ++ x :: rlys
            )
          )
split' {x, lxs, rxs, lys, rys} prf = case split {lxs, rxs = x :: rxs, lys, rys} prf of
  Left (lrys ** rrys ** (prf0, prf1, prf2)) => case rrys of
    rry :: rrys => case prf1 of
      prf1 :: prfs1 => Left (lrys ** rrys ** (prf0, prfs1, rewrite prf1 in prf2))

  Right (llys ** rlys ** (prf0, prf1, prf2)) => case rlys of
    rly :: rlys => case prf1 of
      prf1 :: prfs1 => Right (llys ** rlys ** (prf0, prfs1, rewrite prf1 in prf2))
    
    Nil => let
      prf0' : ListEq lxs lys
      prf0' = rewrite toEq prf2
           in rewrite concat_nil llys
           in prf0
      in Left (Nil ** rxs ** (rewrite concat_nil lys in prf0', fromEq Refl, rev prf1))
      
namespace Eq

  total
  export
  split
     : {lxs, rxs, lys, rys : List a}
    -> (lxs ++ rxs = lys ++ rys)
    -> Either
        ( lrys
       ** rrys
       ** ( lxs = (lys ++ lrys)
          , rxs = rrys
          , rys = (lrys ++ rrys)
          )
        )
        ( llys 
       ** rlys
       ** ( lxs = llys
          , rxs = (rlys ++ rys)
          , lys = (llys ++ rlys)
          )
        )

  split {lxs = Nil, rxs = Nil, lys = Nil, rys = Nil} prf = Right (Nil ** Nil ** (Refl, Refl, Refl))

  split {lxs = Nil, rxs = (rx :: rxs), lys = Nil, rys = Nil} prf impossible
  split {lxs = Nil, rxs = (rx :: rxs), lys = Nil, rys = (ry :: rys)} prf
    = Right (Nil ** Nil ** (Refl, prf, Refl))
  split {lxs = Nil, rxs = (rx :: rxs), lys = (ly :: lys), rys} prf
    = Right (Nil ** ly :: lys ** (Refl, prf, Refl))

  split {lxs = (lx :: lxs), rxs, lys = Nil, rys = Nil} prf impossible
  split {lxs = (lx :: lxs), rxs, lys = Nil, rys = (ry :: rys)} prf
    = Left ((lx :: lxs) ** rxs ** (Refl, Refl, revEq prf))
  split {lxs = (lx :: lxs), rxs, lys = (ly :: lys), rys} prf
    = case split (tail_eq prf) of
        Left  (lrys ** rrys ** (prf0, prf1, prf2)) => Left  (lrys       ** rrys ** (rewrite head_eq prf in cong (ly ::) prf0, prf1, prf2))
        Right (llys ** rlys ** (prf0, prf1, prf2)) => Right (ly :: llys ** rlys ** (rewrite head_eq prf in cong (ly ::) prf0, prf1, cong (ly ::) prf2))

  total
  export
  split' : {x : a}
        -> {lxs, rxs, lys, rys : List a}
        -> (lxs ++ (x :: rxs) = lys ++ rys)
        -> Either
            ( lrys
          ** rrys
          ** ( lxs = lys ++ lrys
              , rxs = rrys
              , rys = lrys ++ x :: rrys
              )
            )
            ( llys
          ** rlys
          ** ( lxs = llys
              , rxs = rlys ++ rys
              , lys = llys ++ x :: rlys
              )
            )
  split' {x, lxs, rxs, lys, rys} prf = case split {lxs, rxs = x :: rxs, lys, rys} prf of
    Left (lrys ** rrys ** (prf0, prf1, prf2)) => case rrys of
      rry :: rrys => Left (lrys ** rrys ** (prf0, tail_eq prf1, rewrite head_eq prf1 in prf2))

    Right (llys ** rlys ** (prf0, prf1, prf2)) => case rlys of
      rly :: rlys => Right (llys ** rlys ** (prf0, tail_eq prf1, rewrite head_eq prf1 in prf2))
      
      Nil => let
        prf0' : (lxs = lys ++ [])
        prf0' = rewrite concat_nil lys
             in rewrite prf2
             in rewrite concat_nil llys
             in prf0
        in Left (Nil ** rxs ** (prf0', Refl, revEq prf1))
