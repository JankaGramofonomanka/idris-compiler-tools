module Compile.FunDecl

import Control.Monad.State
import Control.Monad.Either

import Data.Attached
import Data.DList
import Data.The
import Data.Typed

import LLVM
import LNG
import CFG
import Compile.Instr
import Compile.Tools
import Compile.Tools.CBlock
import Compile.Tools.CompM
import Compile.Tools.CompileResult
import Compile.Tools.VariableCTX


compileBody : (labelIn : BlockLabel)
           -> (ctx : labelIn :~: VarCTX)
           -> (instr : Instr)
           -> CompM (CFG CBlock Closed Closed)

compileBody labelIn ctx instr = do
  -- TODO get rid of this "" hack
  -- TODO consider using `compileInstrDD`
  res <- compileInstrUD labelIn (MkBlockLabel "") ctx instr
  handleRes res

  where
    handleRes : CompileResultUD lbl lbl' cr
             -> CompM (CFG CBlock Closed Closed)
    handleRes (CRUDC g) = pure $ imap {ins = Just []} ([] |++>) g
    -- TODO: Get rid of this error. It is against the whole idea behind this
    -- project. This might require significant modification of the `LNG`
    -- structure.
    handleRes (CRUDO _) = throwError UnexpectedOpenGraph

export
compileFunDecl : FunDecl retType paramTypes funId
              -> CompM $ FunDecl (GetLLType retType) (map GetLLType paramTypes)
compileFunDecl func {paramTypes} = do
  
  varRegPairs <- dtraverse getReg func.params
  let entryLabel  = MkBlockLabel "entry"
      ctx         = attach entryLabel $ contextify varRegPairs
      regs        = dmap snd varRegPairs
      regs'       = decompose regs
      
  cfg <- compileBody entryLabel ctx func.body
  let cfg' = vmap' toLLVM cfg
  
  let MkFunId name = unThe func.theId
  pure $ LLVM.MkFunDecl { name, theRetType = The.map GetLLType func.theRetType, params = regs', body = cfg' }

  where

    VRPair : LNGType -> Type
    VRPair t = (Variable t, Reg (GetLLType t))

    getReg : Variable t -> CompM (VRPair t)
    getReg {t} var = do
      reg <- freshRegister' (The.map GetLLType $ typeOf var)
      pure (var, reg)

    contextify : DList VRPair ts -> VarCTX
    contextify pairs = dfoldr insert' emptyCtx pairs where
      insert' : VRPair t' -> VarCTX -> VarCTX
      insert' (k, v) = insert k (Var v)
    
    toLLVM : {ins, outs : List BlockLabel}
          -> CBlock lbl (Just ins) (Just outs)
          -> BlockVertex lbl (Just ins) (Just outs)
    
    toLLVM {outs = []} (MkBB { theLabel, phis, body, term = Ret val, ctx })
      = MkSimpleBlock { theLabel, phis, body, term = Ret val }
    
    toLLVM {outs = []} (MkBB { theLabel, phis, body, term = RetVoid, ctx })
      = MkSimpleBlock { theLabel, phis, body, term = RetVoid }
    
    toLLVM {outs = [l]} (MkBB { theLabel, phis, body, term = Branch l, ctx })
      = MkSimpleBlock { theLabel, phis, body, term = Branch l }
    
    toLLVM {outs = [t, e]} (MkBB { theLabel, phis, body, term = CondBranch c t e, ctx })
      = MkSimpleBlock { theLabel, phis, body, term = CondBranch c t e }
      
    toLLVM {outs = (l :: l' :: l'' :: ls)} (MkBB { theLabel, phis, body, term, ctx}) impossible  
  
    decompose : DList (f . g) ts -> DList f (map g ts)
    -- TODO is there a bettter way?
    decompose xs = believe_me xs
