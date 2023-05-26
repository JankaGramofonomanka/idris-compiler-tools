module TypeCheck.Data.Error

import LNG.Parsed               as LNG
import LNG.TypeChecked          as TC
import Parse.Data.Position
import TypeCheck.Data.Context

data Error'
  = NoSuchVariable Ident
  | NoSuchFunction Ident
  | TypeError TC.LNGType TC.LNGType
  | BinOpTypeError TC.LNGType TC.LNGType
  | UnOpTypeError TC.LNGType
  | NumParamsMismatch Nat Nat
  | ReturnPrecedingInstructions
  | MissingReturnInstr
  | NoMainFunction
  | VariableAlreadyDeclared Ident Pos
  | FunctionAlreadyDefined Ident DefPos

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
typeError : Pos -> TC.LNGType -> TC.LNGType -> Error
typeError p expected actual = p |^ TypeError expected actual

export
binOpTypeError : Pos -> TC.LNGType -> TC.LNGType -> Error
binOpTypeError p lt rt = p |^ BinOpTypeError lt rt

export
unOpTypeError : Pos -> TC.LNGType -> Error
unOpTypeError p t = p |^ UnOpTypeError t

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

export
fuctionAlreadyDefined : ^Ident -> DefPos -> Error
fuctionAlreadyDefined (p |^ ident) p' = p |^ FunctionAlreadyDefined ident p'


