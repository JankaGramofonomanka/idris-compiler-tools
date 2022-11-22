module StackMachine

import Data.So

import Data.DList

data JType = TInt | TDouble

data JValue : JType -> Type where
  VInt : Int -> JValue TInt
  VDouble : Double -> JValue TDouble

implementation Num (JValue TInt) where
  fromInteger n = VInt (fromInteger n)

  VInt x + VInt y = VInt (x + y)
  VInt x * VInt y = VInt (x * y)

implementation Neg (JValue TInt) where
  negate (VInt n) = VInt (negate n)

  VInt x - VInt y = VInt (x - y)

implementation Integral (JValue TInt) where
  VInt x `div` VInt y = VInt (x `div` y)
  VInt x `mod` VInt y = VInt (x `mod` y)


implementation Num (JValue TDouble) where
  fromInteger n = VDouble (fromInteger n)

  VDouble x + VDouble y = VDouble (x + y)
  VDouble x * VDouble y = VDouble (x * y)

implementation Neg (JValue TDouble) where
  negate (VDouble n) = VDouble (negate n)

  VDouble x - VDouble y = VDouble (x - y)

implementation Fractional (JValue TDouble) where
  VDouble x / VDouble y = VDouble (x / y)
  recip (VDouble x) = VDouble (recip x)

Stack : List JType -> Type
Stack = DList JValue

namespace Semantics
  public export
  Semantics : List JType -> List JType -> Type
  Semantics ts1 ts2 = Stack ts1 -> Stack ts2

  public export
  ipush : JValue TInt -> Semantics s (TInt :: s)
  ipush x s = x :: s

  public export
  dpush : JValue TDouble -> Semantics s (TDouble :: s)
  dpush x s = x :: s


  public export
  iadd : Semantics (TInt :: TInt :: ts) (TInt :: ts)
  iadd (x :: y :: s) = x + y :: s

  public export
  isub : Semantics (TInt :: TInt :: ts) (TInt :: ts)
  isub (x :: y :: s) = x - y :: s

  public export
  imul : Semantics (TInt :: TInt :: ts) (TInt :: ts)
  imul (x :: y :: s) = x * y :: s


  public export
  dadd : Semantics (TDouble :: TDouble :: ts) (TDouble :: ts)
  dadd (x :: y :: s) = x + y :: s

  public export
  dsub : Semantics (TDouble :: TDouble :: ts) (TDouble :: ts)
  dsub (x :: y :: s) = x - y :: s

  public export
  dmul : Semantics (TDouble :: TDouble :: ts) (TDouble :: ts)
  dmul (x :: y :: s) = x * y :: s

  public export
  swap : Semantics (t1 :: t2 :: ts) (t2 :: t1 :: ts)
  swap (x :: y :: s) = (y :: x :: s)


data Instr : Semantics ts1 ts2 -> Type where
  
  IPush : (x : JValue TInt) -> Instr (ipush x)
  DPush : (x : JValue TDouble) -> Instr (dpush x)

  IAdd : Instr Semantics.iadd
  ISub : Instr Semantics.isub
  IMul : Instr Semantics.imul

  DAdd : Instr Semantics.dadd
  DSub : Instr Semantics.dsub
  DMul : Instr Semantics.dmul

  Swap : Instr Semantics.swap

infixl 7 :+:
data Program : Semantics ts1 ts2 -> Type where
  Empty : Program (\s => s)
  (:+:) : Program progSemantics -> Instr instrSemantics -> Program (instrSemantics . progSemantics)


twoPlusTwo : Program (\s => (VInt 4) :: s)
twoPlusTwo = Empty :+: IPush 2 :+: IPush 2 :+: IAdd

add : (x : JValue TInt) -> (y : JValue TInt) -> Program (\s => y + x :: s)
add x y = Empty :+: IPush x :+: IPush y :+: IAdd

Optimisation : Semantics ts1 ts2 -> Type
Optimisation semantics = Program semantics -> Program semantics

example : Optimisation semantics
example (prog :+: IPush x :+: IPush y :+: IPush z :+: IAdd) = prog :+: IPush y :+: IPush z :+: IAdd :+: IPush x :+: Swap
example (prog :+: instr) = example prog :+: instr
example Empty = Empty

