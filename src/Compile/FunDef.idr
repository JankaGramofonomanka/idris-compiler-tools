module Compile.FunDef

import Control.Monad.State
import Control.Monad.Either

import Data.Attached
import Data.DList
import Data.The
import Data.Typed

import LLVM
import LNG.TypeChecked as LNG
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
           -> (instr : Instr rt Returning)
           -> CompM (CFG (CBlock $ GetLLType rt) Closed Closed)

compileBody labelIn ctx instr = do
  -- TODO get rid of this "" hack
  -- TODO consider using `compileInstrDD`
  CRC g <- compileInstrUD labelIn (MkBlockLabel "") ctx instr
  pure $ imap {ins = Just []} ([] |++>) g

mkFunConst : Fun t ts -> Const $ FunType (GetLLType t) (map GetLLType ts)
mkFunConst (MkFun t ts (MkFunId name)) = MkConst (FunType (GetLLType t) (map GetLLType ts)) (MkConstId name)

export
compileFunDecl : LNG.FunDef
              -> CompM LLVM.FunDef
compileFunDecl func = do
  
  varRegPairs <- dtraverse getReg func.params
  let entryLabel  = MkBlockLabel "entry"
      ctx         = attach entryLabel $ contextify varRegPairs
      regs        = dmap snd varRegPairs
      regs'       = decompose regs
      
  cfg <- compileBody entryLabel ctx func.body
  let cfg' = vmap' toLLVM cfg
  
  pure $ LLVM.MkFunDef { retT = GetLLType func.retType
                       , name = mkFunConst func.funId
                       , params = regs'
                       , body = cfg'
                       }

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
          -> (CBlock rt) lbl (Just ins) (Just outs)
          -> BlockVertex rt lbl (Just ins) (Just outs)
    
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
