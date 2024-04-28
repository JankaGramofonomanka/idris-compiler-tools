module Main

import System
import System.File

import Data.Doc
import LLVM
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

||| Run the compiler: read the file, parse, type-check, compile and write the output
main : IO ()
main = do

  -- read args
  _ :: source :: dest :: _ <- getArgs
                            | _ => error "expected source and destination file paths"

  -- read the source file
  Right file <- readFile source
              | Left err => error (show err)

  -- tokenize
  let Just tokens = tokenize file
                  | Nothing => error "tokenize error"

  -- parse the tokens
  let Just pprog = posParse program tokens
                 | Nothing => error "parse error"

  -- check semantic correctness
  let Right tcprog = typeCheck pprog
                   | Left err => error $ render 4 100 (print err)

  -- compile the checked program
  let Right llprog = compile tcprog
                   | Left err => error $ render 4 100 (print err)

  -- render the compiled program to text format
  let llvm = render 4 100 $ print llprog

  -- write the output to a file
  _ <- writeFile dest llvm

  putStrLn "success"
