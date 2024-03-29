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
import LLVM

import Compile.Data.CBlock
import Compile.Data.CompM
import Compile.Data.Context
import Compile.Data.Error
import Compile.Utils
import CFG

import Theory




data EQType = EQ' | NE'
cmpKind : EQType -> CMPKind
cmpKind EQ' = EQ
cmpKind NE' = NE



public export
CompM' : Type -> Type
CompM' = StateT VarCTX CompM

getValue : Variable t -> CompM' (LLValue (GetLLType t))
getValue var = do
  Just val <- gets (lookup var) | Nothing => lift $ throwError (NoSuchVariable var)
  pure val



compileLiteral : (labelIn : Label)
              -> (literal : Literal t)
              -> CompM' ((lbl ** CFG (CBlock rt) (Undefined labelIn) (Undefined lbl)), LLValue (GetLLType t))
compileLiteral labelIn (LitBool b) = pure $ ((labelIn ** emptyCFG (attach labelIn !get)), ILitV (if b then 1 else 0))
compileLiteral labelIn (LitInt i) = pure $ ((labelIn ** emptyCFG (attach labelIn !get)), ILitV i)
compileLiteral labelIn (LitString s) = do

  (k ** cst) <- lift (getStringLiteral s)
  reg <- lift $ freshRegister (Ptr I8)
  
  let expr = GetElementPtr {k} {n = 32} (ConstPtr cst) (ILitV 0) (ILitV 0)
  g <- pure $ omap (<+ Assign reg expr) (emptyCFG $ attach labelIn !get)
  
  pure ((labelIn ** g), Var reg)


mutual

  ||| Returns
  |||   - a control flow graph that computes the expression `expr`
  |||   - the label of the block that the graph ends in.
  |||   - the value of the expression `expr`
  ||| The graph starts in a block labeled `labelIn`.
  ||| The context decribing values of variables stays the same through the entire
  ||| computation and is stored in the state.
  export
  compileExpr : (labelIn : Label)
             -> (expr : Expr t)
             -> CompM' ((lbl ** CFG (CBlock rt) (Undefined labelIn) (Undefined lbl)), LLValue (GetLLType t))



  compileExpr labelIn (Lit lit) = compileLiteral labelIn lit

  compileExpr labelIn (Var var) = do
    
    val <- getValue var

    pure ((labelIn ** emptyCFG (attach labelIn !get)), val)

  

  compileExpr labelIn (BinOperation op lhs rhs) = case op of
    Add => compileBinOp labelIn I32 (BinOperation ADD)  lhs rhs
    Sub => compileBinOp labelIn I32 (BinOperation SUB)  lhs rhs
    Mul => compileBinOp labelIn I32 (BinOperation MUL)  lhs rhs
    Div => compileBinOp labelIn I32 (BinOperation SDIV) lhs rhs
    Mod => compileBinOp labelIn I32 (BinOperation SREM) lhs rhs
    
    And => compileBoolExpr labelIn (BinOperation And lhs rhs)
    Or  => compileBoolExpr labelIn (BinOperation Or  lhs rhs)
    
    EQ {prf} => compileEqComparison {prf} labelIn EQ' lhs rhs
    NE {prf} => compileEqComparison {prf} labelIn NE' lhs rhs

    LE => compileBinOp labelIn I1 (ICMP SLE) lhs rhs
    LT => compileBinOp labelIn I1 (ICMP SLT) lhs rhs
    GE => compileBinOp labelIn I1 (ICMP SGE) lhs rhs
    GT => compileBinOp labelIn I1 (ICMP SGT) lhs rhs

    Concat => do
      ((lbl ** g), [lhs', rhs']) <- compileExprs labelIn [lhs, rhs]

      reg <- lift $ freshRegister (Ptr I8)
      let g' = omap (<+ Assign reg (Call (ConstPtr strconcat) [lhs', rhs'])) g

      pure ((lbl ** g'), Var reg)
  
  

  compileExpr labelIn (UnOperation op expr) = case op of
    
    Neg => do

      ((lbl ** g), val) <- compileExpr labelIn expr
      reg <- lift (freshRegister I32)

      -- TODO: Is this OK or is it a hack?
      let g' = omap (<+ Assign reg (BinOperation SUB (ILitV 0) val)) g
      
      pure ((lbl ** g'), Var reg)

    Not => compileBoolExpr labelIn (UnOperation Not expr)

  
  compileExpr labelIn (Call fun args) = do
    funPtr <- lift $ getFunPtr fun

    ((lbl ** g), args') <- compileExprs labelIn args

    reg <- lift (freshRegister' $ (unFun . unPtr) (typeOf funPtr))

    let g' = omap (<+ Assign reg (Call funPtr args')) g

    pure ((lbl ** g'), Var reg)
  


  -----------------------------------------------------------------------------
  compileExprs : (labelIn : Label)
              -> DList Expr ts
              -> CompM' ( (lbl ** CFG (CBlock rt) (Undefined labelIn) (Undefined lbl))
                        , DList LLValue (map GetLLType ts)
                        )
  compileExprs labelIn [] = pure ((labelIn ** emptyCFG (attach labelIn !get)), [])
  compileExprs labelIn (expr :: exprs) = do
    ((lbl ** g), val) <- compileExpr labelIn expr
    ((lbl' ** g'), vals) <- compileExprs lbl exprs

    let g'' = connect g g'
    
    pure ((lbl' ** g''), val :: vals)
  




  -----------------------------------------------------------------------------
  compileBinOp : (labelIn : Label)
              -> (t : LLType)
              -> (LLValue (GetLLType t') -> LLValue (GetLLType t'') -> LLExpr t)
              -> Expr t'
              -> Expr t''
              -> CompM' ((lbl ** CFG (CBlock rt) (Undefined labelIn) (Undefined lbl)), LLValue t)
  compileBinOp labelIn t mkExpr lhs rhs = do
  
    ((lbl ** g), [lhs', rhs']) <- compileExprs labelIn [lhs, rhs]
    
    reg <- lift (freshRegister t)
    let g' = omap (<+ Assign reg (mkExpr lhs' rhs')) g

    pure ((lbl ** g'), Var reg)



  -----------------------------------------------------------------------------
  compileEqComparison : {0 prf : EqComparable t}
                     -> (labelIn : Label)
                     -> EQType
                     -> Expr t
                     -> Expr t
                     -> CompM' ((lbl ** CFG (CBlock rt) (Undefined labelIn) (Undefined lbl)), LLValue I1)
  compileEqComparison labelIn eqType lhs rhs = case typeOf {f = Expr} lhs of
    
    MkThe TInt    => compileBinOp labelIn I1 (ICMP $ cmpKind eqType) lhs rhs
    
    MkThe TBool   => compileBinOp labelIn I1 (ICMP $ cmpKind eqType) lhs rhs
    
    MkThe TString => do
      ((lbl ** g), [lhs', rhs']) <- compileExprs labelIn [lhs, rhs]

      -- TODO here the `eqType` is discarded and the code acts as if it is `EQ'`
      reg <- lift $ freshRegister I1
      let g' = omap (<+ Assign reg (Call (ConstPtr strcompare) [lhs', rhs'])) g

      pure ((lbl ** g'), Var reg)

    MkThe TVoid   => let
    
        0 impossiblePrf : (CompM' ((lbl ** CFG (CBlock rt) (Undefined labelIn) (Undefined lbl)), LLValue I1) = ())
        impossiblePrf = exfalso (voidNotEqComparable prf)

      in rewrite impossiblePrf in ()

  
  
  
  
  -----------------------------------------------------------------------------
  
  {-
  Add branch instructions such that when the value of `expr` is `true`, then the
  execution of the program will end up in `lblT` and in `lblF` otherwise.
  -}
  export
  ifology : (labelIn : Label)
         -> (expr : Expr TBool)
         -> (lblT : Label)
         -> (lblF : Label)
         -> CompM'  ( outsT ** outsF ** CFG (CBlock rt)
                                            (Undefined labelIn)
                                            (Defined $ outsT ~~> lblT ++ outsF ~~> lblF)
                    )

  
  ifology labelIn (BinOperation And lhs rhs) lblT lblF = do

    lblM <- lift freshLabel
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

    lblM <- lift freshLabel
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
    let g' = omap (<+| CondBranch val lblT lblF) g
    
    pure ([lbl] ** [lbl] ** g')
    
  
  



  
  -----------------------------------------------------------------------------

  compileBoolExpr : (labelIn : Label)
                 -> Expr TBool
                 -> CompM' ((lbl ** CFG (CBlock rt) (Undefined labelIn) (Undefined lbl)), LLValue I1)

  compileBoolExpr labelIn expr = do
    labelTrue <- lift freshLabel
    labelFalse <- lift freshLabel
    (outsT ** outsF ** ifologyG) <- ifology labelIn expr labelTrue labelFalse
    
    labelPost <- lift freshLabel
    
    
    trueBLK <- pure $ [] |++> emptyCBlock (attach labelTrue !get) <+| Branch labelPost
    
    let trueG : CFG (CBlock rt) (Defined $ outsT ~~> labelTrue) (Defined [labelTrue ~> labelPost])
        trueG = SingleVertex {vins = Just outsT, vouts = Just [labelPost]} trueBLK
    
    
    falseBLK <- pure $ [] |++> emptyCBlock (attach labelFalse !get) <+| Branch labelPost

    let falseG : CFG (CBlock rt) (Defined $ outsF ~~> labelFalse) (Defined [labelFalse ~> labelPost])
        falseG = SingleVertex {vins = Just outsF, vouts = Just [labelPost]} falseBLK
    
    
    reg <- lift (freshRegister I1)

    let phi : PhiExpr [labelTrue, labelFalse] I1
        phi = Phi I1 [(labelTrue, ILitV 1), (labelFalse, ILitV 0)]
    
    let phiAssignment = AssignPhi reg phi
    
    let postIns = [labelTrue, labelFalse]
    
    postBLK <- pure $ phiAssignment |+> emptyCBlock (attach labelPost !get)

    let postG : CFG (CBlock rt) (Defined [labelTrue ~> labelPost, labelFalse ~> labelPost]) (Undefined labelPost)
        postG = SingleVertex {vins = Just [labelTrue, labelFalse], vouts = Undefined} postBLK


    let confluence = Series (Parallel trueG falseG) postG
    let final = Series ifologyG confluence
    
    pure ((labelPost ** final), Var reg)

















