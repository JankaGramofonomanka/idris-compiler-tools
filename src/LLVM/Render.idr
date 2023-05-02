module LLVM.Render

import CFG
import Data.DList
import Data.Doc
import Data.List
import Data.The
import Data.Typed
import LLVM

prtArgs : List String -> String
prtArgs l = "(" ++ concat (intersperse ", " l) ++ ")"

mkSentence : List String -> String
mkSentence = concat . intersperse " "

prtFun : String -> String -> List String -> String
prtFun retTy fun args = mkSentence [retTy, fun ++ prtArgs args]

implementation {0 x : t} -> DocItem t => DocItem (The x) where
  prt (MkThe t) = prt t

implementation [typed] Typed f => (docT : DocItem (The t)) => DocItem (f t) => DocItem (f t) where
  prt val = prt (typeOf val) @{docT} ++ " " ++ prt val

-- LLType ---------------------------------------------------------------------
implementation DocItem LLType where
  prt (I n)           = "i" ++ show n
  prt Void            = "void"
  prt (Ptr t)         = prt t ++ "*"
  prt (Array t n)     = "[" ++ show n ++ " x " ++ prt t ++ "]"
  prt (FunType t ts)  = prt t ++ "(" ++ prtArgs (map prt ts) ++ ")"

-- Reg, RegId -----------------------------------------------------------------
implementation DocItem (RegId t) where
  prt (MkRegId s) = "%" ++ s

implementation DocItem (Reg t) where
  prt (MkReg t id) = prt id

-- Const, ConstId -------------------------------------------------------------
implementation DocItem (ConstId t) where
  prt (MkConstId s) = "@" ++ s

implementation DocItem (Const t) where
  prt (MkConst t id) = prt id

-- LLLiteral ------------------------------------------------------------------
implementation DocItem (LLLiteral t) where
  prt (ILit i) = show i

-- LLValue --------------------------------------------------------------------
prtValue : LLValue t -> String
prtValue (Var reg) = prt reg
prtValue (Lit lit) = prt lit
prtValue (ConstPtr cst) = prt cst
prtValue (Null t) = "null"

implementation DocItem (LLValue t) where
  prt = prtValue

-- BinOperator, CMPKind, BlockLabel, Inputs -----------------------------------
implementation DocItem (BinOperator t1 t2 t3) where
  -- TODO: verify that each of these is correct
  prt ADD   = "add"
  prt SUB   = "sub"
  prt MUL   = "mul"
  prt SDIV  = "sdiv"
  prt UDIV  = "udiv"
  prt SREM  = "srem"
  prt UREM  = "urem"

implementation DocItem CMPKind where
  -- TODO: verify that each of these is correct
  prt EQ  = "eq"
  prt NE  = "ne"
  prt SGT = "sgt"
  prt SGE = "sge"
  prt SLT = "slt"
  prt SLE = "sle"
  prt UGT = "ugt"
  prt UGE = "uge"
  prt ULT = "ult"
  prt ULE = "ule"

prtLabel : BlockLabel -> String
prtLabel (MkBlockLabel s) = "%" ++ s

implementation DocItem BlockLabel where
  prt = prtLabel

implementation [blockEntry] DocItem BlockLabel where
  prt (MkBlockLabel s) = s ++ ":"

implementation [branch] DocItem BlockLabel where
  prt lbl = "label " ++ prtLabel lbl

-- Expr -----------------------------------------------------------------------
implementation DocItem (LLExpr t) where
  
  prt (BinOperation op lhs rhs)
    = mkSentence [prt op, prt (resType op), prt lhs ++ ",", prt rhs]
  
  prt (Call funPtr params)
    = mkSentence ["define", prtFun (prt $ retTypeOf funPtr) (prt funPtr) (undmap (prt @{typed}) params)]
                          
  prt (ICMP cmp lhs rhs)
    = mkSentence ["icmp", prt cmp, prt @{typed} lhs ++ ",", prt rhs]
  
  prt (Load ptr)
    = let ptrT = typeOf ptr
      in mkSentence ["load", prt (unPtr ptrT) ++ ",", prt @{typed} ptr]
  
  prt (BitCast val t) = mkSentence ["bitcast", prt @{typed} val, "to", prt t]

implementation DocItem (PhiExpr ins t) where
  prt (Phi t l) = mkSentence $ ["phi", prt t] ++ map prtPair l where
    prtPair : (BlockLabel, LLValue t) -> String
    prtPair (lbl, val) = "[" ++ prt val ++ ", " ++ prt lbl ++ "]"

-- Isntr ----------------------------------------------------------------------
implementation DocItem STInstr where
  prt (Assign reg expr) = mkSentence [prt reg, "=", prt expr]
  prt (Exec expr) = prt expr
  prt (Store val ptr) = mkSentence ["store", prt val @{typed} ++ ",", prt ptr @{typed}]

implementation DocItem (CFInstr cfk) where
  prt (Branch lbl) = mkSentence ["br", prt @{branch} lbl]
  prt (CondBranch cond thn els) = mkSentence ["br", prt @{typed} cond ++ ",", prt @{branch} thn, prt @{branch} els]
  prt (Ret val) = mkSentence ["ret", prt @{typed} val]
  prt RetVoid = "ret void"

implementation DocItem (PhiInstr ins) where
  prt (AssignPhi reg phi) = mkSentence [prt reg, "=", prt phi]


-- SimpleBlock ----------------------------------------------------------------
implementation Document (SimpleBlock label inputs cfkind) where
  print (MkSimpleBlock { theLabel = MkThe label, phis, body, term })
    = MkDoc { lines = [ Right (simple $ prt label @{blockEntry})
                      , Left ( fromLines
                            -- TODO: Add comments to `SimpleBlock`
                             $ map (simple . prt) phis
                            ++ map (simple . prt) body
                            ++ map (simple . prt) [term]
                             )
                      ] 
            }

implementation Document (CFG BlockVertex (Defined ins) (Defined outs)) where

  print (SingleVertex {vins = Just ins, vouts = Just []} v) = print v
  print (SingleVertex {vins = Just ins, vouts = Just (out :: outs)} v) = print v
  print (Cycle node loop) = print node ++ print loop
  print (Series first second) = print first ++ print second
  
  print (LBranch  node branch) = print node ++ print branch
  print (RBranch  node branch) = print node ++ print branch
  print (LMerge   branch node) = print branch ++ print node
  print (RMerge   branch node) = print branch ++ print node

  print (Parallel left right) = print left ++ print right

  print (IFlip cfg) = print cfg
  print (OFlip cfg) = print cfg

-- FunDecl --------------------------------------------------------------------
implementation Document (FunDecl retT paramTs) where

  print (MkFunDecl { theRetType, name, params, body }) = let
      header = simple $ mkSentence ["define", prtFun (prt theRetType) name (undmap (prt @{typed}) params)]
    in MkDoc { lines = [Right header, Left (print body)] }

-- Program --------------------------------------------------------------------
implementation Document Program where
  print (MkProgram { funcs }) = foldl append Doc.empty funcs where

    append : Doc -> (t ** ts ** FunDecl t ts) -> Doc
    append doc (t ** ts ** fun) = doc ++ blankLines 1 ++ (print fun)
    

