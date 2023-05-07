module LNG.BuiltIns

import Data.DList
import LNG.Parsed as LNG
import LNG.TypeChecked as TC
import LLVM
import Compile.Utils

printInt, printString, error, readInt, readString : String
printInt    = "printInt"
printString = "printString"
error       = "error"
readInt     = "readInt"
readString  = "readString"



namespace TypeCheck
  
  export
  builtIns : List (TC.LNGType, List TC.LNGType, LNG.Ident)
  builtIns
    = [ (TVoid, [TInt], MkId printInt)
    --, (TVoid, [TStr], MkId printString)
      , (TVoid, [],     MkId error)
      , (TInt,  [],     MkId readInt)
    --, (TStr,  [],     MkId readString)
      ]

  
namespace Compile

  export
  builtIns : List (t ** ts ** (Fun t ts, FunVal t ts))
  builtIns
    -- TODO: the imported names of function constants might be different
    = [ (TVoid ** [TInt] ** (MkFun TVoid [TInt]  (MkFunId printInt),     ConstPtr (MkConst (FunType Void      [I32])    (MkConstId printInt))))
    --, (TVoid ** [TStr] ** (MkFun TVoid [TStr]  (MkFunId printString),  ConstPtr (MkConst (FunType Void      [Ptr I8]) (MkConstId printString))))
      , (TVoid ** []     ** (MkFun TVoid []      (MkFunId error),        ConstPtr (MkConst (FunType Void      [])       (MkConstId error))))
      , (TInt  ** []     ** (MkFun TInt  []      (MkFunId readInt),      ConstPtr (MkConst (FunType I32       [])       (MkConstId readInt))))
    --, (TStr  ** []     ** (MkFun TStr  []      (MkFunId readString),   ConstPtr (MkConst (FunType (Ptr I8)  [])       (MkConstId readString))))
      ]
