module LLVM.Render

import Data.Vect

import CFG
import Data.DList
import Data.Doc
import Data.List
import Data.The
import Data.Typed
import LLVM
import Utils

prtItems : List String -> String
prtItems l = concat (intersperse ", " l)

prtArgs : List String -> String
prtArgs l = "(" ++ prtItems l ++ ")"

prtFun : String -> String -> List String -> String
prtFun retTy fun args = mkSentence [retTy, fun ++ prtArgs args]

export
implementation {0 x : t} -> DocItem t => DocItem (The x) where
  prt (MkThe t) = prt t

export
implementation [typed] Typed f => (docT : DocItem (The t)) => DocItem (f t) => DocItem (f t) where
  prt val = prt (typeOf val) @{docT} ++ " " ++ prt val

-- LLType ---------------------------------------------------------------------
export
implementation DocItem LLType where
  prt (I n)           = "i" ++ show n
  prt Void            = "void"
  prt (Ptr t)         = prt t ++ "*"
  prt (Array t n)     = "[" ++ show n ++ " x " ++ prt t ++ "]"
  prt (FunType t ts)  = prt t ++ "(" ++ prtArgs (map prt ts) ++ ")"

-- Reg, RegId -----------------------------------------------------------------
export
implementation DocItem (RegId t) where
  prt (MkRegId s) = "%" ++ s

export
implementation DocItem (Reg t) where
  prt (MkReg t id) = prt id

-- Const, ConstId -------------------------------------------------------------
export
implementation DocItem (ConstId t) where
  prt (MkConstId s) = "@" ++ s

export
implementation DocItem (Const t) where
  prt (MkConst t id) = prt id

-- LLLiteral ------------------------------------------------------------------
export
implementation DocItem (LLLiteral t) where
  prt (ILit i) = show i
  prt (CharArrLit chars) = "c\"" ++ concat (map encode chars) ++ "\\00\"" where
    encode : Char -> String
    
    -- based on this
    -- https://en.wikipedia.org/wiki/Escape_sequences_in_C
    encode '\a'   = "\\07"
    encode '\b'   = "\\08"
    encode '\ESC' = "\\1B"
    encode '\f'   = "\\0C"
    encode '\n'   = "\\0A"
    encode '\r'   = "\\0D"
    encode '\t'   = "\\09"
    encode '\v'   = "\\0B"
    encode '\\'   = "\\5C"
    encode '\''   = "\\27"
    encode '\"'   = "\\22"
    encode '\?'   = "\\3F"
    encode ch     = pack [ch]

-- LLValue --------------------------------------------------------------------
prtValue : LLValue t -> String
prtValue (Var reg) = prt reg
prtValue (Lit lit) = prt lit
prtValue (ConstPtr cst) = prt cst
prtValue (Null t) = "null"

export
implementation DocItem (LLValue t) where
  prt = prtValue

-- BinOperator, CMPKind, BlockLabel, Inputs -----------------------------------
export
implementation DocItem (BinOperator t1 t2 t3) where
  -- TODO: verify that each of these is correct
  prt ADD   = "add"
  prt SUB   = "sub"
  prt MUL   = "mul"
  prt SDIV  = "sdiv"
  prt UDIV  = "udiv"
  prt SREM  = "srem"
  prt UREM  = "urem"

export
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

export
implementation DocItem BlockLabel where
  prt = prtLabel

export
implementation [blockEntry] DocItem BlockLabel where
  prt (MkBlockLabel s) = s ++ ":"

export
implementation [branch] DocItem BlockLabel where
  prt lbl = "label " ++ prtLabel lbl

-- Expr -----------------------------------------------------------------------
export
implementation DocItem (LLExpr t) where
  
  prt (BinOperation op lhs rhs)
    = mkSentence [prt op, prt (resType op), prt lhs ++ ",", prt rhs]
  
  prt (Call funPtr params)
    = mkSentence ["call", prtFun (prt $ retTypeOf funPtr) (prt funPtr) (undmap (prt @{typed}) params)]

  prt (GetElementPtr {t, k} arr idx1 idx2)
    = mkSentence ["getelementptr", prtItems [prt (Array t k), prt @{typed} arr, prt @{typed}idx1, prt @{typed} idx2 ]]
                          
  prt (ICMP cmp lhs rhs)
    = mkSentence ["icmp", prt cmp, prt @{typed} lhs ++ ",", prt rhs]
  
  prt (Load ptr)
    = let ptrT = typeOf ptr
      in mkSentence ["load", prt (unPtr ptrT) ++ ",", prt @{typed} ptr]
  
  prt (BitCast val t) = mkSentence ["bitcast", prt @{typed} val, "to", prt t]

export
implementation DocItem (PhiExpr ins t) where
  prt (Phi t l) = mkSentence $ ["phi", prt t, prtItems (map prtPair l)] where
    prtPair : (BlockLabel, LLValue t) -> String
    prtPair (lbl, val) = "[" ++ prt val ++ ", " ++ prt lbl ++ "]"

-- Isntr ----------------------------------------------------------------------
export
implementation DocItem STInstr where
  prt (Assign reg expr) = mkSentence [prt reg, "=", prt expr]
  prt (Exec expr) = prt expr
  prt (Store val ptr) = mkSentence ["store", prt val @{typed} ++ ",", prt ptr @{typed}]
  prt Empty = ""

export
implementation DocItem (CFInstr cfk) where
  prt (Branch lbl) = mkSentence ["br", prt @{branch} lbl]
  prt (CondBranch cond thn els) = mkSentence ["br", prtItems [prt @{typed} cond, prt @{branch} thn, prt @{branch} els]]
  prt (Ret val) = mkSentence ["ret", prt @{typed} val]
  prt RetVoid = "ret void"

export
implementation DocItem (PhiInstr ins) where
  prt (AssignPhi reg phi) = mkSentence [prt reg, "=", prt phi]


-- SimpleBlock ----------------------------------------------------------------
export
implementation Document (SimpleBlock label inputs cfkind) where
  print (MkSimpleBlock { theLabel = MkThe label, phis, body, term })
    = MkDoc { lines = [ Right (simple $ prt label @{blockEntry})
                      , Left ( fromLines
                            -- TODO: Add comments to `SimpleBlock`
                             $ map (uncurry (MkLine . prt)) phis
                            ++ map (uncurry (MkLine . prt)) body
                            ++ map (simple . prt) [term]
                             )
                      ] 
            }

export
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

-- FunDef ---------------------------------------------------------------------
export
implementation Document (FunDef retT paramTs) where

  print (MkFunDef { theRetType, name, params, body }) = let
      header = simple $ mkSentence ["define", prtFun (prt theRetType) (prt name) (undmap (prt @{typed}) params), "{"]
    in MkDoc { lines = [Right header, Left (print body), Right (simple "}")] }

-- FunDecl --------------------------------------------------------------------
export
implementation DocItem (FunDecl retT paramTs) where
  prt (MkFunDecl { name, theRetType, theParamTypes }) = mkSentence ["declare", prtFun (prt theRetType) (prt name) (map prt $ unThe theParamTypes)]

-- ConstDef -------------------------------------------------------------------
export
implementation DocItem ConstDef where
  prt (DefineConst t cst val) = mkSentence [prt cst, "=", "internal", "constant", prt t, prt val]

-- Program --------------------------------------------------------------------
export
implementation Document Program where
  print (MkProgram { funDecls, constDefs, funcs })
     = foldl appendFunDecl Doc.empty funDecls
    ++ blankLines 4
    ++ foldl appendConstDef Doc.empty constDefs
    ++ blankLines 4
    ++ foldl appendFunDef Doc.empty funcs
    
    where
      appendFunDecl : Doc -> (t ** ts ** FunDecl t ts) -> Doc
      appendFunDecl doc (t ** ts ** decl) = doc ++ fromLines [simple (prt decl)]

      appendConstDef : Doc -> ConstDef -> Doc
      appendConstDef doc def = doc ++ fromLines [simple (prt def)]

      appendFunDef : Doc -> (t ** ts ** FunDef t ts) -> Doc
      appendFunDef doc (t ** ts ** fun) = doc ++ blankLines 1 ++ (print fun)
      

