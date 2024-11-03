module Main

import Test.Parse.Tokenize
import Test.Compile.Data.Context.Utils

main : IO ()
main = Parse.Tokenize.main
    >> Test.Compile.Data.Context.Utils.main
