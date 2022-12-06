module Compile.Tools

import LNG
import LLVM

public export
GetLLType : LNGType -> LLType
GetLLType TInt = I32
GetLLType TBool = I1
GetLLType TVoid = Void















