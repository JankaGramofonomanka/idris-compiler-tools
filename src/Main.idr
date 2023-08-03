module Main

import System
import System.File

import Data.Doc
import LLVM
import LLVM.Generalized
import LLVM.Render
import LNG.Parse
import LNG.Parsed
import LNG.TypeChecked
import Parse.Data.Parser
import Parse.Data.Position
import Parse.Data.Token
import Parse.Tokenize
import TypeCheck
import TypeCheck.Data.Error
import Compile
import Compile.Data.Error

error : String -> a
error e = assert_total (idris_crash e)

main : IO ()
main = do

  _ :: source :: dest :: _ <- getArgs
                            | _ => error "expected source and destination file paths"

  Right file <- readFile source
              | Left err => error (show err)
  
  let Just tokens = tokenize file
                  | Nothing => error "tokenize error"

  let Just pprog = posParse program tokens
                 | Nothing => error "parse error"

  let Right tcprog = typeCheck pprog
                   | Left err => error $ render 4 100 (print err)

  let Right llprog = compile tcprog
                   | Left err => error $ render 4 100 (print err)

  let llvm = render 4 100 $ print llprog
  
  _ <- writeFile dest llvm
  
  putStrLn "success"
