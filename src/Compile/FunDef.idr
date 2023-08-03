module Compile.FunDef

import Control.Monad.State
import Control.Monad.Either

import Data.Attached
import Data.DList
import Data.The
import Data.Typed

import LLVM.Generalized as LLVM.G
import LNG.TypeChecked as LNG
import CFG
import Compile.Instr
import Compile.Data.CBlock
import Compile.Data.CompM
import Compile.Data.CompileResult
import Compile.Data.Error
import Compile.Data.LLVM
import Compile.Utils


compileBody : (labelIn : BlockLabel)
           -> (instr : Instr rt Returning)
           -> CompM (CFG (CBlock $ GetLLType rt) Closed Closed)

compileBody labelIn instr = do
  -- TODO get rid of this "" hack
  -- TODO consider using `compileInstrDD`
  CRC g <- compileInstrUD labelIn (MkBlockLabel "") instr
  pure $ imap {ins = Just []} ([] |++>) g

export
compileFunDecl : {retType : LNGType}
              -> {paramTypes : List LNGType}
              -> {funId : FunId retType paramTypes}
              -> FunDef retType paramTypes funId
              -> CompM $ FunDef (GetLLType retType) (map GetLLType paramTypes)
compileFunDecl func {paramTypes} = do
  
  let fparams = func.params
  varRegPairs <- dtraverse getReg fparams
  let entryLabel  = MkBlockLabel "entry"
      regs        = dmap snd varRegPairs
      regs'       = decompose regs
      
  cfg <- compileBody entryLabel func.body
  let cfg' = vmap' toLLVM cfg
  
  let MkFunId name = unThe func.theId
  let llname = MkConst (FunType (GetLLType retType) (map GetLLType paramTypes)) (MkConstId name)
  pure $ LLVM.G.MkFunDef { name = llname, theRetType = The.map GetLLType func.theRetType, params = regs', body = cfg' }

  where

    VRPair : LNGType -> Type
    VRPair t = (Variable t, Reg' (GetLLType t))

    getReg : Variable t -> CompM (VRPair t)
    getReg {t} var = do
      reg <- freshRegister' (The.map GetLLType $ typeOf var)
      pure (var, reg)

    toLLVM : {ins, outs : List BlockLabel}
          -> (CBlock rt) lbl (Just ins) (Just outs)
          -> BlockVertex rt lbl (Just ins) (Just outs)
    
    toLLVM {outs = []} (MkBB { theLabel, phis, body, term = Ret val })
      = MkSimpleBlock { theLabel, phis, body, term = Ret val }
    
    toLLVM {outs = []} (MkBB { theLabel, phis, body, term = RetVoid })
      = MkSimpleBlock { theLabel, phis, body, term = RetVoid }
    
    toLLVM {outs = [l]} (MkBB { theLabel, phis, body, term = Branch l })
      = MkSimpleBlock { theLabel, phis, body, term = Branch l }
    
    toLLVM {outs = [t, e]} (MkBB { theLabel, phis, body, term = CondBranch c t e })
      = MkSimpleBlock { theLabel, phis, body, term = CondBranch c t e }
      
    toLLVM {outs = (l :: l' :: l'' :: ls)} (MkBB { theLabel, phis, body, term }) impossible  
  
    decompose : DList (f . g) ts -> DList f (map g ts)
    -- TODO is there a bettter way?
    decompose xs = believe_me xs
