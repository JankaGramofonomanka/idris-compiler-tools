||| A module that defines how to render the LLVM representation to text format
module LLVM.Render

import Data.Vect

import CFG
import Data.DList
import Data.Doc
import Data.List
import Data.Singleton
import Data.Typed
import LLVM
import Utils

||| Separate the elements of a list by commas
prtItems : List String -> String
prtItems l = concat (intersperse ", " l)

||| Separate the elements of a list by commas and put them in parentheses
prtArgs : List String -> String
prtArgs l = "(" ++ prtItems l ++ ")"

||| Print a function name with its arguments/parameters in parentheses
prtFun : String -> String -> List String -> String
prtFun retTy fun args = mkSentence [retTy, fun ++ prtArgs args]

export
implementation {0 x : t} -> DocItem t => DocItem (Singleton x) where
  prt (Val t) = prt t

export
implementation [typed] Typed f => (docT : DocItem (Singleton t)) => DocItem (f t) => DocItem (f t) where
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

-- BinOperator, CMPKind, Label ------------------------------------------------
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

prtLabel : Label -> String
prtLabel (MkLabel s) = "%" ++ s

export
implementation DocItem Label where
  prt = prtLabel

||| Print the block label as it appears at the block entry
export
implementation [blockEntry] DocItem Label where
  prt (MkLabel s) = s ++ ":"

||| Print the block label as it appears in the branch instructions
export
implementation [branch] DocItem Label where
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
    prtPair : (Label, LLValue t) -> String
    prtPair (lbl, val) = "[" ++ prt val ++ ", " ++ prt lbl ++ "]"

-- Isntr ----------------------------------------------------------------------
export
implementation DocItem STInstr where
  -- TODO: the assignments of `void` values should be prevented by the structure of `LLVM`
  prt (Assign reg expr) = case (typeOf {f = LLExpr} expr) of
    Val Void => prt expr
    Val t    => mkSentence [prt reg, "=", prt expr]
  prt (Exec expr) = prt expr
  prt (Store val ptr) = mkSentence ["store", prt val @{typed} ++ ",", prt ptr @{typed}]
  prt Empty = ""

export
implementation DocItem (CFInstr rt outs) where
  prt (Branch lbl) = mkSentence ["br", prt @{branch} lbl]
  prt (CondBranch cond thn els) = mkSentence ["br", prtItems [prt @{typed} cond, prt @{branch} thn, prt @{branch} els]]
  prt (Ret val) = mkSentence ["ret", prt @{typed} val]
  prt RetVoid = "ret void"

export
implementation DocItem (PhiInstr ins) where
  prt (AssignPhi reg phi) = mkSentence [prt reg, "=", prt phi]


-- BasicBlock -----------------------------------------------------------------
export
implementation Document (BasicBlock rt label inputs outputs) where
  print (MkBasicBlock { theLabel = Val label, phis, body, term })
    = MkDoc { lines = [ Right (simple $ prt label @{blockEntry})
                      , Left ( fromLines
                            -- TODO: Add comments to `BasicBlock`
                             $ map (uncurry (MkLine . prt)) phis
                            ++ map (uncurry (MkLine . prt)) body
                            ++ map (simple . prt) [term]
                             )
                      ]
            }

printCFG : CFG (BlockVertex rt) (Defined ins) (Defined outs) -> Doc
printCFG Empty = empty
printCFG (SingleVertex {vins = Just ins, vouts = Just outs} v) = print v
printCFG (Cycle node loop) = printCFG node ++ printCFG loop
printCFG (Series first second) = printCFG first ++ printCFG second

printCFG (Parallel left right) = printCFG left ++ printCFG right

printCFG (IFlip cfg) = printCFG cfg
printCFG (OFlip cfg) = printCFG cfg

implementation [cfg] Document (CFG (BlockVertex rt) (Defined ins) (Defined outs)) where
  print = printCFG

-- TODO for some reason idris can't find this implementation,
-- therefore I had to add the `cfg` implementation and the `printCFG` function
export
implementation Document (CFG (BlockVertex rt) (Defined ins) (Defined outs)) where

  print = print @{cfg}

-- FunDef ---------------------------------------------------------------------
export
implementation Document FunDef where

  print (MkFunDef { retT, name, params, body }) = let
      header = simple $ mkSentence ["define", prtFun (prt retT) (prt name) (undmap (prt @{typed}) params), "{"]
    in MkDoc { lines = [Right header, Left (print @{cfg} body), Right (simple "}")] }

-- FunDecl --------------------------------------------------------------------
export
implementation DocItem FunDecl where
  prt (MkFunDecl { retT, paramTs, name }) = mkSentence ["declare", prtFun (prt retT) (prt name) (map prt paramTs)]

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
      appendFunDecl : Doc -> FunDecl -> Doc
      appendFunDecl doc decl = doc ++ fromLines [simple (prt decl)]

      appendConstDef : Doc -> ConstDef -> Doc
      appendConstDef doc def = doc ++ fromLines [simple (prt def)]

      appendFunDef : Doc -> FunDef -> Doc
      appendFunDef doc fun = doc ++ blankLines 1 ++ (print fun)

||| Render an LLVM program
||| @ tablLength the length of a single indent
||| @ margin     the width after which comments will appear
||| @ doc        the docmuent to be rendered
|||
||| calls `Doc.render` with the LLVM comment delimiter
export
render : (tabLength : Nat) -> (margin : Nat) -> (doc : Doc) -> String
render = Doc.render ";"

