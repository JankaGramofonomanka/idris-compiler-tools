module Compile.Expr

import Data.List

import Control.Monad.State
import Control.Monad.Either

import Data.Some
import Data.DList
import Data.Attached
import Data.The
import Data.Typed

import LNG.BuiltIns
import LNG.TypeChecked
import LLVM.Generalized

import Compile.Data.CBlock
import Compile.Data.CompM
import Compile.Data.Error
import Compile.Data.LLVM
import Compile.Utils
import CFG

import Theory




data EQType = EQ' | NE'
cmpKind : EQType -> CMPKind
cmpKind EQ' = EQ
cmpKind NE' = NE


getValue : Variable t -> CompM (LLValue $ GetLLType t)
getValue var = pure (Var $ Placeholder var)



compileLiteral : (labelIn : BlockLabel)
              -> (literal : Literal t)
              -> CompM ((lbl ** CFG (CBlock rt) (Undefined labelIn) (Undefined lbl)), LLValue (GetLLType t))
compileLiteral labelIn (LitBool b) = pure $ ((labelIn ** emptyCFG), ILitV (if b then 1 else 0))
compileLiteral labelIn (LitInt i) = pure $ ((labelIn ** emptyCFG), ILitV i)
compileLiteral labelIn (LitString s) = do

  (k ** cst) <- getStringLiteral s
  reg <- freshRegister (Ptr I8)
  
  let expr = GetElementPtr {k} {n = 32} (ConstPtr cst) (ILitV 0) (ILitV 0)
  g <- pure $ omap {outs = Undefined} (<+ Assign reg expr) emptyCFG
  
  pure ((labelIn ** g), Var reg)


mutual

  {-
  Returns
    - a control flow graph that computes the expression `expr`
    - the label of the block that the graph ends in.
    - the value of the expression `expr`
  The graph starts in a block labeled `labelIn`.
  The context decribing values of variables stays the same through the entire
  computation and is stored in the state.
  -}
  export
  compileExpr : (labelIn : BlockLabel)
             -> (expr : Expr t)
             -> CompM ((lbl ** CFG (CBlock rt) (Undefined labelIn) (Undefined lbl)), LLValue (GetLLType t))



  compileExpr labelIn (Lit lit) = compileLiteral labelIn lit

  compileExpr labelIn (Var var) = do
    
    val <- getValue var

    pure ((labelIn ** emptyCFG), val)

  

  compileExpr labelIn (BinOperation op lhs rhs) = case op of
    Add => compileAritmOp labelIn ADD lhs rhs
    Sub => compileAritmOp labelIn SUB lhs rhs
    Mul => compileAritmOp labelIn MUL lhs rhs
    Div => compileAritmOp labelIn SDIV lhs rhs
    Mod => compileAritmOp labelIn SREM lhs rhs
    
    And => compileBoolExpr labelIn (BinOperation And lhs rhs)
    Or  => compileBoolExpr labelIn (BinOperation Or  lhs rhs)
    
    EQ {prf} => compileEqComparison {prf} labelIn EQ' lhs rhs
    NE {prf} => compileEqComparison {prf} labelIn NE' lhs rhs

    LE => compileIntComparison labelIn SLE lhs rhs
    LT => compileIntComparison labelIn SLT lhs rhs
    GE => compileIntComparison labelIn SGE lhs rhs
    GT => compileIntComparison labelIn SGT lhs rhs

    Concat => do
      ((lbl ** g), lhs', rhs') <- compileOperands labelIn lhs rhs

      reg <- freshRegister (Ptr I8)
      let g' = omap {outs = Undefined} (<+ Assign reg (Call (ConstPtr strconcat) [lhs', rhs'])) g

      pure ((lbl ** g'), Var reg)
  
  

  compileExpr labelIn (UnOperation op expr) = case op of
    
    Neg => do

      ((lbl ** g), val) <- compileExpr labelIn expr
      reg <- freshRegister I32

      -- TODO: Is this OK or is it a hack?
      let g' = omap {outs = Undefined} (<+ Assign reg (BinOperation SUB (ILitV 0) val)) g
      
      pure ((lbl ** g'), Var reg)

    Not => compileBoolExpr labelIn (UnOperation Not expr)

  
  compileExpr labelIn (Call fun args) = do
    funPtr <- getFunPtr fun

    ((lbl ** g), args') <- compileExprs labelIn args

    reg <- freshRegister' $ (unFun . unPtr) (typeOf funPtr)

    let instr = assignIfNonVoid (typeOf reg) reg (Call funPtr args')
    let g' = omap {outs = Undefined} (<+ instr) g

    pure ((lbl ** g'), Var reg)
  
    where
      -- TODO: this should be enforced by the structure of `LLVM`
      assignIfNonVoid : {0 t : LLType} -> The t -> Reg' t -> LLExpr t -> STInstr
      assignIfNonVoid (MkThe Void) reg expr = Exec expr
      assignIfNonVoid (MkThe t) reg expr = Assign reg expr



  -----------------------------------------------------------------------------
  compileExprs : (labelIn : BlockLabel)
              -> DList Expr ts
              -> CompM ( (lbl ** CFG (CBlock rt) (Undefined labelIn) (Undefined lbl))
                        , DList LLValue (map GetLLType ts)
                        )
  compileExprs labelIn [] = pure ((labelIn ** emptyCFG), [])
  compileExprs labelIn (expr :: exprs) = do
    ((lbl ** g), val) <- compileExpr labelIn expr
    ((lbl' ** g'), vals) <- compileExprs lbl exprs

    let g'' = connect g g'
    
    pure ((lbl' ** g''), val :: vals)
  



  -----------------------------------------------------------------------------
  compileOperands : (labelIn : BlockLabel)
                 -> Expr t
                 -> Expr t'
                 -> CompM ( (lbl ** CFG (CBlock rt) (Undefined labelIn) (Undefined lbl))
                           , LLValue (GetLLType t)
                           , LLValue (GetLLType t')
                           )

  compileOperands labelIn lhs rhs = do
    
    ((labelL ** gl), lhs') <- compileExpr labelIn lhs
    ((labelR ** gr), rhs') <- compileExpr labelL rhs
  
    let glr = connect gl gr
    pure ((labelR ** glr), lhs', rhs')
  



  -----------------------------------------------------------------------------
  compileAritmOp : (labelIn : BlockLabel)

                -> BinOperator I32 I32 I32
                -> Expr TInt
                -> Expr TInt
                -> CompM ((lbl ** CFG (CBlock rt) (Undefined labelIn) (Undefined lbl)), LLValue I32)
  compileAritmOp labelIn op lhs rhs = do
    ((lbl ** g), lhs', rhs') <- compileOperands labelIn lhs rhs
    
    reg <- freshRegister I32
    let g' = omap {outs = Undefined} (<+ Assign reg (BinOperation op lhs' rhs')) g

    pure ((lbl ** g'), Var reg)
  



  -----------------------------------------------------------------------------
  compileEqComparison : {0 prf : EqComparable t}
                     -> (labelIn : BlockLabel)
                     -> EQType
                     -> Expr t
                     -> Expr t
                     -> CompM ((lbl ** CFG (CBlock rt) (Undefined labelIn) (Undefined lbl)), LLValue I1)
  compileEqComparison labelIn eqType lhs rhs = case typeOf {f = Expr} lhs of
    
    MkThe TInt    => compileIntComparison labelIn (cmpKind eqType) lhs rhs
    
    MkThe TBool   => compileBoolComparison labelIn (cmpKind eqType) lhs rhs
    
    MkThe TString => do
      ((lbl ** g), lhs', rhs') <- compileOperands labelIn lhs rhs

      -- TODO here the `eqType` is discarded and the code acts as if it is `EQ'`
      reg <- freshRegister I1
      let g' = omap {outs = Undefined} (<+ Assign reg (Call (ConstPtr strcompare) [lhs', rhs'])) g

      pure ((lbl ** g'), Var reg)

    MkThe TVoid   => let
    
        0 impossiblePrf : (CompM ((lbl ** CFG (CBlock rt) (Undefined labelIn) (Undefined lbl)), LLValue I1) = ())
        impossiblePrf = exfalso (voidNotEqComparable prf)

      in rewrite impossiblePrf in ()

  -----------------------------------------------------------------------------
  compileIntComparison : (labelIn : BlockLabel)
                      -> CMPKind
                      -> Expr TInt
                      -> Expr TInt
                      -> CompM ((lbl ** CFG (CBlock rt) (Undefined labelIn) (Undefined lbl)), LLValue I1)
  compileIntComparison labelIn cmpKind lhs rhs = do
    ((lbl ** g), lhs', rhs') <- compileOperands labelIn lhs rhs

    (g', val) <- addICMP cmpKind g lhs' rhs'
    pure ((lbl ** g'), val)
  
  -----------------------------------------------------------------------------
  compileBoolComparison : (labelIn : BlockLabel)
                       -> CMPKind
                       -> Expr TBool
                       -> Expr TBool
                       -> CompM ((lbl ** CFG (CBlock rt) (Undefined labelIn) (Undefined lbl)), LLValue I1)
  compileBoolComparison labelIn cmpKind lhs rhs = do
    ((lbl ** g), lhs', rhs') <- compileOperands labelIn lhs rhs

    (g', val) <- addICMP cmpKind g lhs' rhs'
    pure ((lbl ** g'), val)
  
  
  
  
  -----------------------------------------------------------------------------
  addICMP : CMPKind
         -> CFG (CBlock rt) ins (Undefined labelOut)
         -> LLValue (I k)
         -> LLValue (I k)
         -> CompM (CFG (CBlock rt) ins (Undefined labelOut), LLValue I1)
  addICMP {k} cmpKind g lhs rhs = do
    reg <- freshRegister I1
    let g' = omap {outs = Undefined} (<+ Assign reg (ICMP cmpKind lhs rhs)) g
    
    pure (g', Var reg)
  


  -----------------------------------------------------------------------------
  
  {-
  Add branch instructions such that when the value of `expr` is `true`, then the
  execution of the program will end up in `lblT` and in `lblF` otherwise.
  -}
  export
  ifology : (labelIn : BlockLabel)
         -> (expr : Expr TBool)
         -> (lblT : BlockLabel)
         -> (lblF : BlockLabel)
         -> CompM  ( outsT ** outsF ** CFG (CBlock rt)
                                            (Undefined labelIn)
                                            (Defined $ outsT ~~> lblT ++ outsF ~~> lblF)
                    )

  
  ifology labelIn (BinOperation And lhs rhs) lblT lblF = do

    lblM <- freshLabel
    (outsM ** outsF   ** gl) <- ifology labelIn lhs lblM lblF
    (outsT ** outsF'  ** gr) <- ifology lblM    rhs lblT lblF

    let gr' = imap {ins = Just outsM} ([] |++>) gr
    
    let final : CFG (CBlock rt)
                    (Undefined labelIn)
                    (Defined $ outsT ~~> lblT ++ (outsF' ++ outsF) ~~> lblF)
        final = rewrite collect_concat lblF outsF' outsF
                in rewrite concat_assoc (outsT ~~> lblT) (outsF' ~~> lblF) (outsF ~~> lblF)
                in LBranch gl gr'
    
    pure (outsT ** outsF' ++ outsF ** final)
  

  ifology labelIn (BinOperation Or lhs rhs) lblT lblF = do

    lblM <- freshLabel
    (outsT  ** outsM ** gl) <- ifology labelIn  lhs lblT lblM
    (outsT' ** outsF ** gr) <- ifology lblM     rhs lblT lblF

    let gr' = imap {ins = Just outsM} ([] |++>) gr
    
    let final : CFG (CBlock rt)
                    (Undefined labelIn)
                    (Defined ((outsT ++ outsT') ~~> lblT ++ outsF ~~> lblF))
        final = rewrite collect_concat lblT outsT outsT'
                in rewrite revEq $ concat_assoc (outsT ~~> lblT) (outsT' ~~> lblT) (outsF ~~> lblF)
                in RBranch gl gr'
    
    pure (outsT ++ outsT' ** outsF ** final)
  

  ifology labelIn (UnOperation Not expr) lblT lblF = do
    (outsF ** outsT ** g) <- ifology labelIn expr lblF lblT
    pure (outsT ** outsF ** OFlip g)
  

  ifology labelIn expr lblT lblF = do
    ((lbl ** g), val) <- compileExpr labelIn expr
    let g' = omap {outs = Just [lblT, lblF]} (<+| CondBranch val lblT lblF) g
    
    pure ([lbl] ** [lbl] ** g')
    
  
  



  
  -----------------------------------------------------------------------------

  compileBoolExpr : (labelIn : BlockLabel)
                 -> Expr TBool
                 -> CompM ((lbl ** CFG (CBlock rt) (Undefined labelIn) (Undefined lbl)), LLValue I1)

  compileBoolExpr labelIn expr = do
    labelTrue <- freshLabel
    labelFalse <- freshLabel
    (outsT ** outsF ** ifologyG) <- ifology labelIn expr labelTrue labelFalse
    
    labelPost <- freshLabel
    
    
    trueBLK <- pure $ [] |++> emptyCBlock <+| Branch labelPost
    
    let trueG : CFG (CBlock rt) (Defined $ outsT ~~> labelTrue) (Defined [labelTrue ~> labelPost])
        trueG = SingleVertex {vins = Just outsT, vouts = Just [labelPost]} trueBLK
    
    
    falseBLK <- pure $ [] |++> emptyCBlock <+| Branch labelPost

    let falseG : CFG (CBlock rt) (Defined $ outsF ~~> labelFalse) (Defined [labelFalse ~> labelPost])
        falseG = SingleVertex {vins = Just outsF, vouts = Just [labelPost]} falseBLK
    
    
    reg <- freshRegister I1

    let phi : PhiExpr (MkInputs [labelTrue, labelFalse]) I1
        phi = Phi I1 [(labelTrue, ILitV 1), (labelFalse, ILitV 0)]
    
    let phiAssignment = AssignPhi reg phi
    
    let postIns = MkInputs [labelTrue, labelFalse]
    
    postBLK <- pure $ phiAssignment |+> emptyCBlock

    let postG : CFG (CBlock rt) (Defined [labelTrue ~> labelPost, labelFalse ~> labelPost]) (Undefined labelPost)
        postG = SingleVertex {vins = Just [labelTrue, labelFalse], vouts = Undefined} postBLK


    let confluence = Series (Parallel trueG falseG) postG
    let final = Series ifologyG confluence
    
    pure ((labelPost ** final), Var reg)

















