module Compile.FunDef

import Control.Monad.State
import Control.Monad.Either

import Data.Attached
import Data.DList
import Data.The
import Data.Typed

import LLVM
import LNG.TypeChecked
import CFG
import Compile.Instr
import Compile.Data.CBlock
import Compile.Data.CompM
import Compile.Data.CompileResult
import Compile.Data.Context
import Compile.Data.Error
import Compile.Utils


compileBody : (labelIn : BlockLabel)
           -> (ctx : labelIn :~: VarCTX)
           -> (instr : Instr (Returning t))
           -> CompM (CFG CBlock Closed Closed)

compileBody labelIn ctx instr = do
  -- TODO get rid of this "" hack
  -- TODO consider using `compileInstrDD`
  CRUDC g <- compileInstrUD labelIn (MkBlockLabel "") ctx instr
  pure $ imap {ins = Just []} ([] |++>) g

export
compileFunDecl : FunDef retType paramTypes funId
              -> CompM $ FunDef (GetLLType retType) (map GetLLType paramTypes)
compileFunDecl func {paramTypes} = do
  
  varRegPairs <- dtraverse getReg func.params
  let entryLabel  = MkBlockLabel "entry"
      ctx         = attach entryLabel $ contextify varRegPairs
      regs        = dmap snd varRegPairs
      regs'       = decompose regs
      
  cfg <- compileBody entryLabel ctx func.body
  let cfg' = vmap' toLLVM cfg
  
  let MkFunId name = unThe func.theId
  pure $ LLVM.MkFunDef { name, theRetType = The.map GetLLType func.theRetType, params = regs', body = cfg' }

  where

    VRPair : LNGType -> Type
    VRPair t = (Variable t, Reg (GetLLType t))

    getReg : Variable t -> CompM (VRPair t)
    getReg {t} var = do
      reg <- freshRegister' (The.map GetLLType $ typeOf var)
      pure (var, reg)

    contextify : DList VRPair ts -> VarCTX
    contextify pairs = dfoldr insert' empty pairs where
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