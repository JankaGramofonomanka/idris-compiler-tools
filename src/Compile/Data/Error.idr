module Compile.Data.Error

import Data.Doc
import LNG.TypeChecked
import LNG.TypeChecked.Render
import Utils

||| An error that can be thrown during the compilation phase
public export
data Error : Type where
  NoSuchVariable : Variable t -> Error
  NoSuchFunction : FunId t ts -> Error
  Impossible : String -> Error

export
implementation Document Error where
  print err
    = MkDoc
      { lines = [ Right $ simple "Compilation error:"
                , Left $ print' err
                ]
      }

    where
      print' : Error -> Doc
      print' (NoSuchVariable var) = fromLines [simple $ mkSentence ["No such variable:", prt var @{ticks}]]
      print' (NoSuchFunction fun) = fromLines [simple $ mkSentence ["No such function:", prt fun @{ticks}]]
      print' (Impossible msg)
        = MkDoc
          { lines = [ Right $ simple "Impossible error:"
                    , Left $ fromLines [simple msg]
                    ]
          }

