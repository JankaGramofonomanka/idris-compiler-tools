module TypeCheck.Data.Error

import Data.String

import Data.Doc

import LLVM.Render
import LNG.Parsed               as LNG
import LNG.Parsed.Render
import LNG.TypeChecked          as TC
import LNG.TypeChecked.Render
import Parse.Data.Position
import TypeCheck.Data.Context

data Error'
  = NoSuchVariable Ident
  | NoSuchFunction Ident
  | TypeError TC.LNGType TC.LNGType
  | BinOpTypeError BinOperator TC.LNGType TC.LNGType
  | UnOpTypeError UnOperator TC.LNGType
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
binOpTypeError : Pos -> BinOperator -> TC.LNGType -> TC.LNGType -> Error
binOpTypeError p op lt rt = p |^ BinOpTypeError op lt rt

export
unOpTypeError : Pos -> UnOperator -> TC.LNGType -> Error
unOpTypeError p op t = p |^ UnOpTypeError op t

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

headerAndContents : String -> List String -> Doc
headerAndContents header contents = MkDoc { lines = [Right (simple header), Left (fromLines $ map simple contents)] }

implementation Document Error' where
  print (NoSuchVariable id) = fromLines [simple $ unwords ["no such variable:", prt id @{ticks}]]
  print (NoSuchFunction id) = fromLines [simple $ unwords ["no such function:", prt id @{ticks}]]
  print (TypeError expected actual)
    = headerAndContents "type error:"
                        [ unwords ["expected:", prt expected @{ticks}]
                        , unwords ["actual:  ", prt actual   @{ticks}]
                        ]

  print (BinOpTypeError op lt rt)
    = headerAndContents (unwords ["operator", prt op @{ticks}, "does not support the following operand types:"])
                        [ unwords ["left  operand type:", prt lt @{ticks}]
                        , unwords ["right operand type:", prt rt @{ticks}]
                        ]

  print (UnOpTypeError op t)
    = fromLines [simple $ unwords ["operator", prt op @{ticks}, "does not support the following operand type:", prt t @{ticks}]]

  print (NumParamsMismatch expected actual)
    = fromLines [simple $ unwords ["expected", show expected, "parameters, but got", show actual]]

  print ReturnPrecedingInstructions = fromLines [simple "return instruction preceding other instructinos"]
  print MissingReturnInstr = fromLines [simple "missing return instruction"]
  print NoMainFunction = fromLines [simple "`main` function not found"]
  print (VariableAlreadyDeclared id declaredAt)
    = fromLines [simple $ unwords ["variable", prt id @{ticks}, "already declared at", prt declaredAt]]

  print (FunctionAlreadyDefined id declaredAt) = case declaredAt of
    DefinedAt p => fromLines [simple $ unwords ["function", prt id @{ticks}, "already declared at", prt p]]
    BuiltIn => fromLines [simple $ unwords ["cannot redefine the built-in function", prt id @{ticks}]]

export
implementation Document Error where
  print (p |^ err) = let
    lines = [ Right (simple $ "Error " ++ prt p ++ ":")
            , Left (print err)
            ]
    in MkDoc { lines }

