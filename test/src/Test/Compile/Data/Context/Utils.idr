module Test.Compile.Data.Context.Utils

import Control.Monad.Either
import Control.Monad.State

import Tester
import Tester.Runner

import Compile.Data.Context
import Compile.Data.Context.Utils
import Compile.Data.CompM
import Compile.Data.Error
import Compile.Utils
import Data.Attached
import Data.DList
import Data.Doc
import Data.DSum
import Data.GEq
import CFG
import LLVM
import LNG.TypeChecked
import Utils

||| Executes a compiler computation on an empty state. Fails in case of errors
runCompM : CompM a -> TestFunc (CompState, a)
runCompM comp = case runStateT emptyState comp of
  Left e => throw $ "the computation fails with error: " ++ render 2 80 (print e)
  Right (s, x) => pure (s, x)

segregateSingleContext : Test
segregateSingleContext = let
    x : Variable TInt
    x = MkVar TInt (MkVarId "x")
    xval : LLValue I32
    xval = Lit (ILit 0)

    l0, l1 : Label
    l0 = MkLabel "L0"
    l1 = MkLabel "L1"

    ctx = VarCTX.insert x xval VarCTX.empty
    ctxs : DList (:~: VarCTX) [l0 ~> l1]
    ctxs = [ attach (l0 ~> l1) ctx ]

  in test "segragating a single context results in the same context" $ do
    (_, sg) <- the (TestFunc (CompState, Segregated l1 [l0])) (runCompM (segregate ctxs))
    let ctx = VarCTX.toList (detach sg.ctx)

    the (TestFunc ()) (assertEq @{?impl} ctx [x :=> xval])

allTests : List Test
allTests = [ segregateSingleContext ]

export
main : IO ()
main = do
  putStrLn "Testing `Compile.Data.Context.Utils`"
  success <- runTests allTests
  pure ()
