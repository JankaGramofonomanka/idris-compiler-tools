module Interpreter.Semantics

import Data.DList
import LNG.Parsed

public export
Value : LNGType -> Type
Value TInt    = Int
Value TBool   = Bool
Value TString = String
Value TVoid   = ()

public export
Fun : LNGType -> List LNGType -> (Type -> Type) -> Type
Fun t ts m = DList Value ts -> m (Value t)

public export
add, sub, mul, div, mod : Value TInt -> Value TInt -> Value TInt
add = (+)
sub = (-)
mul = (*)
div = Prelude.div
mod = Prelude.mod

public export
and, or : Value TBool -> Value TBool -> Value TBool
and p q = p && q
or  p q = p || q

public export
beq : Value TBool -> Value TBool -> Value TBool
beq = (==)

public export
streq : Value TString -> Value TString -> Value TBool
streq = (==)

public export
ieq, le, lt, ge, gt : Value TInt -> Value TInt -> Value TBool
ieq = (==)
le = (<=)
lt = (<)
ge = (>=)
gt = (>)

public export
neg : Value TInt -> Value TInt
neg = negate

public export
not : Value TBool -> Value TBool
not = Prelude.not

public export
conc : Value TString -> Value TString -> Value TString
conc = (++)
