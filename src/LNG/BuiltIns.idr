module LNG.BuiltIns

import Control.Monad.Either
import Control.Monad.State

import Data.SortedMap

import Data.Console
import Data.DList
import Data.The
import LNG.Parsed as LNG
import LNG.TypeChecked as TC
import LLVM
import Compile.Utils
import Interpreter.Semantics

printInt', printString', error', readInt', readString' : String
printInt'    = "printInt"
printString' = "printString"
error'       = "error"
readInt'     = "readInt"
readString'  = "readString"



namespace TypeCheck
  
  export
  builtIns : List (TC.LNGType, List TC.LNGType, LNG.Ident)
  builtIns
    = [ (TVoid,   [TInt],     MkId printInt')
      , (TVoid,   [TString],  MkId printString')
      , (TVoid,   [],         MkId error')
      , (TInt,    [],         MkId readInt')
      , (TString, [],         MkId readString')
      ]

  
namespace Compile


  strconcat' : String
  strconcat' = ".strconcat"

  strcompare' : String
  strcompare' = ".strcompare"
  

  -- LNG function ids
  printInt : Fun TVoid [TInt]
  printInt = MkFun TVoid [TInt] (MkFunId printInt')

  printString : Fun TVoid [TString]
  printString = MkFun TVoid [TString] (MkFunId printString')
  
  error : Fun TVoid []
  error = MkFun TVoid [] (MkFunId error')
  
  readInt : Fun TInt []
  readInt = MkFun TInt [] (MkFunId readInt')
  
  readString : Fun TString []
  readString = MkFun TString [] (MkFunId readString')

  -- LLVM function constatns
  llPrintInt : Const $ FunType Void [I32]
  llPrintInt = (MkConst (FunType Void [I32]) (MkConstId printInt'))

  llPrintString : Const $ FunType Void [Ptr I8]
  llPrintString = (MkConst (FunType Void [Ptr I8]) (MkConstId printString'))
  
  llError : Const $ FunType Void []
  llError = (MkConst (FunType Void []) (MkConstId error'))

  llReadInt :  Const $ FunType I32 []
  llReadInt = (MkConst (FunType I32 []) (MkConstId readInt'))

  llReadString : Const $ FunType (Ptr I8) []
  llReadString = (MkConst (FunType (Ptr I8) []) (MkConstId readString'))

  export
  strconcat : Const $ FunType (Ptr I8) [Ptr I8, Ptr I8]
  strconcat = MkConst (FunType (Ptr I8) [Ptr I8, Ptr I8]) (MkConstId strconcat')

  export
  strcompare : Const $ FunType I1 [Ptr I8, Ptr I8]
  strcompare = MkConst (FunType I1 [Ptr I8, Ptr I8]) (MkConstId strcompare')


  export
  builtIns : List (t ** ts ** (Fun t ts, FunVal t ts))
  builtIns
    -- TODO: the imported names of function constants might be different
    = [ (TVoid    ** [TInt]     ** (printInt,     ConstPtr llPrintInt))
      , (TVoid    ** [TString]  ** (printString,  ConstPtr llPrintString))
      , (TVoid    ** []         ** (error,        ConstPtr llError))
      , (TInt     ** []         ** (readInt,      ConstPtr llReadInt))
      , (TString  ** []         ** (readString,   ConstPtr llReadString))
      ]
  
  
  export
  builtInDecls : List LLVM.FunDecl
  builtInDecls
    = [ MkFunDecl {retT = Void,     paramTs = [I32],            name = llPrintInt}
      , MkFunDecl {retT = Void,     paramTs = [Ptr I8],         name = llPrintString}
      , MkFunDecl {retT = Void,     paramTs = [],               name = llError}
      , MkFunDecl {retT = I32,      paramTs = [],               name = llReadInt}
      , MkFunDecl {retT = (Ptr I8), paramTs = [],               name = llReadString}
      , MkFunDecl {retT = (Ptr I8), paramTs = [Ptr I8, Ptr I8], name = strconcat}
      , MkFunDecl {retT = I1,       paramTs = [Ptr I8, Ptr I8], name = strcompare}
      ]
  

  
namespace Interpreter


  export
  defPrintInt : Monad m => ConsoleO m => Int -> m ()
  defPrintInt = Console.printInt

  export
  defPrintString : Monad m => ConsoleO m => String -> m ()
  defPrintString = Console.printStr

  export
  defReadInt : Monad m => ConsoleI m => m Int
  defReadInt = Console.readInt

  export
  defReadString : Monad m => ConsoleI m => m String
  defReadString = Console.readStr

  export
  defError : MonadError String m => m ()
  defError = throwError "error'"


  export
  builtIns : MonadError String m
          => ConsoleI m
          => ConsoleO m
          => SortedMap Ident (t : LNG.LNGType ** ts : List LNG.LNGType ** Fun t ts m)
  builtIns
    = insert (MkId printInt') (TVoid ** [TInt] ** defPrintInt . head)
    $ insert (MkId printString') (TVoid ** [TString] ** defPrintString . head)
    $ insert (MkId error') (TVoid ** [] ** const defError)
    $ insert (MkId error') (TInt ** [] ** const defReadInt)
    $ insert (MkId error') (TString ** [] ** const defReadString)
    $ empty
