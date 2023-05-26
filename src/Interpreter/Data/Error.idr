module Interpreter.Data.Error

import LNG.Parsed
import Parse.Data.Position

data Error'
  = NoSuchVariable Ident
  | NoSuchFunction Ident
  | TypeError LNGType LNGType
  | TypeError' (List LNGType) LNGType
  | NumParamsMismatch Nat Nat
  | ReturnPrecedingInstructions
  | MissingReturnInstr
  | NoMainFunction
  | VariableAlreadyDeclared Ident Pos
  --| FunctionAlreadyDefined Ident DefPos

export
Error : Type
Error = ^Error'

export
noSuchVariable : ^Ident -> Error
noSuchVariable (p |^ ident) = p |^ NoSuchVariable ident

export
noSuchFunction : ^Ident -> Error
noSuchFunction (p |^ ident) = p |^ NoSuchFunction ident

export
typeError : Pos -> LNGType -> LNGType -> Error
typeError p expected actual = p |^ TypeError expected actual

export
typeError' : Pos -> List LNGType -> LNGType -> Error
typeError' p expected actual = p |^ TypeError' expected actual

export
numParamsMismatch : Pos -> Nat -> Nat -> Error
numParamsMismatch p expected actual = (p |^ NumParamsMismatch expected actual)

export
returnPrecedingInstructions : Pos -> Error
returnPrecedingInstructions = (|^ ReturnPrecedingInstructions)

export
missingReturnInstr : Pos -> Error
missingReturnInstr = (|^ MissingReturnInstr)

export
noMainFunction : Pos -> Error
noMainFunction = (|^ NoMainFunction)

export
variableAlreadyDeclared : ^Ident -> Pos -> Error
variableAlreadyDeclared (p |^ ident) p' = p |^ VariableAlreadyDeclared ident p'

--export
--fuctionAlreadyDefined : ^Ident -> DefPos -> Error
--fuctionAlreadyDefined (p |^ ident) p' = p |^ FunctionAlreadyDefined ident p'



