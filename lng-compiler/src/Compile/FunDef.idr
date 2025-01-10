module Compile.FunDef

import Control.Monad.State
import Control.Monad.Either

import Data.Attached
import Data.DList
import Data.DFunctor
import Data.Singleton
import Data.Singleton.Extra
import Data.Typed

import LLVM
import LNG.TypeChecked as LNG
import ControlFlow.CFG
import Compile.Instr
import Compile.Data.CBlock
import Compile.Data.CompM
import Compile.Data.CompileResult
import Compile.Data.Context
import Compile.Data.Error
import Compile.Utils

||| Compile the body of a function
||| @ labelIn the entry label of the compiled function body
||| @ ctx     the context with the parameter values
||| @ instr   the function body
compileBody
   : (labelIn : Label)
  -> (ctx     : labelIn :~: VarCTX)
  -> (instr   : Instr rt Returning)
  -> CompM (CFG (CBlock $ GetLLType rt) Closed Closed)

compileBody labelIn ctx instr = do
  -- TODO get rid of this "" hack
  -- TODO consider using `compileInstrDD`
  CRR g <- compileInstrUD labelIn (MkLabel "") ctx instr
  pure $ imap {ins = Just []} ([] |++>) g

||| Given an LNG function identidfier, make an LLVM function constant
||| representing it.
||| @ fun the LNG function identifier
mkFunConst
   : (fun : Fun t ts)
  -> Const $ FunType (GetLLType t) (map GetLLType ts)
mkFunConst (MkFun t ts (MkFunId name))
  = MkConst (Val $ FunType (GetLLType t) (map GetLLType ts)) (MkConstId name)

||| Compile a semantically correct LNG function definition
||| @ def the function definition
export
compileFunDef
   : (def : LNG.FunDef)
  -> CompM LLVM.FunDef
compileFunDef func = do

  -- generate a new register for every parameter
  varRegPairs <- dtraverse getReg func.params

  let -- chose an entry label
      entryLabel = MkLabel "entry"

      -- create the context with the parameter values
      ctx        = attach entryLabel $ contextify varRegPairs

      -- get the parameters of the compiled LLVM function
      regs       = dmap snd varRegPairs
      regs'      = decompose regs

  -- compile the body of the function
  cfg <- compileBody entryLabel ctx func.body

  -- convert the `CBlock`s to `BasicBlock`s
  let cfg' = vmap' toLLVM cfg

  pure
    $ LLVM.MkFunDef
    { retT   = GetLLType func.retType
    , name   = mkFunConst func.funId
    , params = regs'
    , body   = cfg'
    }

  where
    ||| A tuple of consisting of an LNG variable and an LLVM value of the
    ||| corresponding type.
    VRPair : LNGType -> Type
    VRPair t = (Variable t, Reg (GetLLType t))

    ||| Generate a fresh register for a given variable and return it paried
    ||| with that variable
    ||| @ var the variable
    getReg : (var : Variable t) -> CompM (VRPair t)
    getReg {t} var = do
      reg <- freshRegister' (GetLLType <$> typeOf var)
      pure (var, reg)

    ||| Construct a variable context from a list of variable-value paris
    contextify : DList VRPair ts -> VarCTX
    contextify pairs = dfoldr insert' empty pairs where
      insert' : VRPair t' -> VarCTX -> VarCTX
      insert' (k, v) = insert k (Var v)

    ||| Convert a completed `CBlock` to a `BasicBlock`
    toLLVM : {ins, outs : List Label}
          -> (CBlock rt) lbl (Just ins) (Just outs)
          -> BlockVertex rt lbl (Just ins) (Just outs)

    toLLVM (MkBB { theLabel, phis, body, term })
      = MkBasicBlock { theLabel, phis, body, term }

    decompose : DList (f . g) ts -> DList f (map g ts)
    -- TODO is there a better way?
    decompose xs = believe_me xs
