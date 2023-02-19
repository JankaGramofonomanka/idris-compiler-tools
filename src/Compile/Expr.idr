module Compile.Expr

import Data.List

import Control.Monad.State
import Control.Monad.Either

import Data.Some
import Data.DMap
import Data.DList
import Data.Attached

import LNG
import LLVM

import Compile.Tools
import Compile.Tools.CBlock
import Compile.Tools.CompileResult
import Compile.Tools.CompM
import Compile.Tools.VariableCTX
import CFG

import Theory





fromLNGLit : Literal t -> LLValue (GetLLType t)
fromLNGLit (LitBool b) = ILit (if b then 1 else 0)
fromLNGLit (LitInt i) = ILit i


comparableInts : EqComparable t -> (n ** GetLLType t = I n)
comparableInts EqCMPInt = (32 ** Refl)
comparableInts EqCMPBool = (1 ** Refl)



-- Another case where dependent pairs with custom multiplicities would be useful
record DPairI (f : Nat -> Type) where
  constructor MkDPairI
  0 n : Nat
  val : f n

-- TODO: This is a hack that wouldn't work if there were more comparable types.
-- probably we should be able to determine the type of an expressiion
integerize : {auto 0 prf : EqComparable t}
          -> (LLValue (GetLLType t), LLValue (GetLLType t))
          -> DPairI (\n => (LLValue (I n), LLValue (I n)))
integerize {prf} (val, val') = let
  
  0 nsuch : (k ** I k = GetLLType t)
  nsuch = case prf of
    EqCMPBool => (1 ** Refl)
    EqCMPInt => (32 ** Refl)
  
  in MkDPairI nsuch.fst (rewrite nsuch.snd in val, rewrite nsuch.snd in val')









public export
CompM' : Type -> Type
CompM' = StateT VarCTX CompM

getValue : Variable t -> CompM' (LLValue (GetLLType t))
getValue var = do
  Just val <- gets (lookup var) | Nothing => lift $ throwError (NoSuchVariable var)
  pure val




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
             -> CompM' ((lbl ** CFG CBlock (Undefined labelIn) (Undefined lbl)), LLValue (GetLLType t))



  compileExpr labelIn (Lit lit) = pure ((labelIn ** initCFG), fromLNGLit lit)

  compileExpr labelIn (Var var) = do
    
    val <- getValue var

    pure ((labelIn ** initCFG), val)

  

  compileExpr labelIn (BinOperation op lhs rhs) = case op of
    Add => compileAritmOp labelIn ADD lhs rhs
    Sub => compileAritmOp labelIn SUB lhs rhs
    Mul => compileAritmOp labelIn MUL lhs rhs
    Div => compileAritmOp labelIn SDIV lhs rhs
    
    And => compileBoolExpr labelIn (BinOperation And lhs rhs)
    Or  => compileBoolExpr labelIn (BinOperation Or  lhs rhs)
    
    EQ => do
        ((lbl ** g), lhs', rhs') <- compileOperands labelIn lhs rhs
        let MkDPairI n (lhs'', rhs'') = integerize (lhs', rhs')

        (g', val) <- addICMP EQ g lhs'' rhs''
        pure ((lbl ** g'), val)

    LE => compileOrdComparison labelIn SLE lhs rhs
    LT => compileOrdComparison labelIn SLT lhs rhs
    GE => compileOrdComparison labelIn SGE lhs rhs
    GT => compileOrdComparison labelIn SGT lhs rhs
  
  

  compileExpr labelIn (UnOperation op expr) = case op of
    
    Neg => do

      ((lbl ** g), val) <- compileExpr labelIn expr
      reg <- lift freshRegister

      -- TODO: Is this OK or is it a hack?
      let g' = omap {outs = Undefined} (<+ Assign reg (BinOperation SUB (ILit 0) val)) g
      
      pure ((lbl ** g'), Var reg)

    Not => compileBoolExpr labelIn (UnOperation Not expr)

  
  compileExpr labelIn (Call fun args) = do
    funPtr <- lift $ getFunPtr fun

    ((lbl ** g), args') <- compileExprs labelIn args

    reg <- lift freshRegister
    let g' = omap {outs = Undefined} (<+ Assign reg (Call funPtr args')) g

    pure ((lbl ** g'), Var reg)
  



  -----------------------------------------------------------------------------
  compileExprs : (labelIn : BlockLabel)
              -> DList Expr ts
              -> CompM' ( (lbl ** CFG CBlock (Undefined labelIn) (Undefined lbl))
                        , DList LLValue (map GetLLType ts)
                        )
  compileExprs labelIn [] = pure ((labelIn ** initCFG), [])
  compileExprs labelIn (expr :: exprs) = do
    ((lbl ** g), val) <- compileExpr labelIn expr
    ((lbl' ** g'), vals) <- compileExprs lbl exprs

    let g'' = connect g g'
    
    pure ((lbl' ** g''), val :: vals)
  



  -----------------------------------------------------------------------------
  compileOperands : (labelIn : BlockLabel)
                 -> Expr t
                 -> Expr t'
                 -> CompM' ( (lbl ** CFG CBlock (Undefined labelIn) (Undefined lbl))
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
                -> CompM' ((lbl ** CFG CBlock (Undefined labelIn) (Undefined lbl)), LLValue I32)
  compileAritmOp labelIn op lhs rhs = do
    ((lbl ** g), lhs', rhs') <- compileOperands labelIn lhs rhs
    
    reg <- lift freshRegister
    let g' = omap {outs = Undefined} (<+ Assign reg (BinOperation op lhs' rhs')) g

    pure ((lbl ** g'), Var reg)
  


  -----------------------------------------------------------------------------
  compileOrdComparison : (labelIn : BlockLabel)
                      -> CMPKind
                      -> Expr TInt
                      -> Expr TInt
                      -> CompM' ((lbl ** CFG CBlock (Undefined labelIn) (Undefined lbl)), LLValue I1)
  compileOrdComparison labelIn cmpKind lhs rhs = do
    ((lbl ** g), lhs', rhs') <- compileOperands labelIn lhs rhs

    (g', val) <- addICMP cmpKind g lhs' rhs'
    pure ((lbl ** g'), val)
  
    
  

  -----------------------------------------------------------------------------
  addICMP : CMPKind
         -> CFG CBlock ins (Undefined labelOut)
         -> LLValue (I k)
         -> LLValue (I k)
         -> CompM' (CFG CBlock ins (Undefined labelOut), LLValue I1)
  addICMP cmpKind g lhs rhs = do
    reg <- lift freshRegister
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
         -> CompM'  ( outsT ** outsF ** ( CFG CBlock
                                              (Undefined labelIn)
                                              (Defined $ outsT ~~> lblT ++ outsF ~~> lblF)
                                        , NonEmpty outsT
                                        , NonEmpty outsF
                                        )
                    )

  
  ifology labelIn (BinOperation And lhs rhs) lblT lblF = do

    lblM <- lift freshLabel
    (outsM ** outsF   ** (gl, prfM, prfF))  <- ifology labelIn lhs lblM lblF
    (outsT ** outsF'  ** (gr, prfT, prfF')) <- ifology lblM    rhs lblT lblF

    let gr' = imap {ins = Just outsM} ([] |++>) gr
    
    let final : CFG CBlock
                    (Undefined labelIn)
                    (Defined $ outsT ~~> lblT ++ (outsF' ++ outsF) ~~> lblF)
        final = rewrite collect_concat lblF outsF' outsF
                in rewrite concat_assoc (outsT ~~> lblT) (outsF' ~~> lblF) (outsF ~~> lblF)
                in LBranch gl gr'
    
    pure (outsT ** outsF' ++ outsF ** (final, prfT, nonempty_plusplus prfF'))
  

  ifology labelIn (BinOperation Or lhs rhs) lblT lblF = do

    lblM <- lift freshLabel
    (outsT  ** outsM ** (gl, prfT,  prfM)) <- ifology labelIn  lhs lblT lblM
    (outsT' ** outsF ** (gr, prfT', prfF)) <- ifology lblM     rhs lblT lblF

    let gr' = imap {ins = Just outsM} ([] |++>) gr
    
    let final : CFG CBlock
                    (Undefined labelIn)
                    (Defined ((outsT ++ outsT') ~~> lblT ++ outsF ~~> lblF))
        final = rewrite collect_concat lblT outsT outsT'
                in rewrite revEq $ concat_assoc (outsT ~~> lblT) (outsT' ~~> lblT) (outsF ~~> lblF)
                in RBranch gl gr'
    
    pure (outsT ++ outsT' ** outsF ** (final, nonempty_plusplus prfT, prfF))
  

  ifology labelIn (UnOperation Not expr) lblT lblF = do
    (outsF ** outsT ** (g, prfF, prfT)) <- ifology labelIn expr lblF lblT
    pure (outsT ** outsF ** (OFlip g, prfT, prfF))
  

  ifology labelIn expr lblT lblF = do
    ((lbl ** g), val) <- compileExpr labelIn expr
    let g' = omap {outs = Just [lblT, lblF]} (<+| CondBranch val lblT lblF) g
    
    pure ([lbl] ** [lbl] ** (g', IsNonEmpty, IsNonEmpty))
    
  
  



  
  -----------------------------------------------------------------------------

  compileBoolExpr : (labelIn : BlockLabel)
                 -> Expr TBool
                 -> CompM' ((lbl ** CFG CBlock (Undefined labelIn) (Undefined lbl)), LLValue I1)

  compileBoolExpr labelIn expr = do
    labelTrue <- lift freshLabel
    labelFalse <- lift freshLabel
    (outsT ** outsF ** (ifologyG, prfT, prfF)) <- ifology labelIn expr labelTrue labelFalse
    
    labelPost <- lift freshLabel
    
    
    let trueBLK : CBlock labelTrue (Just outsT) (Just [labelPost])
        trueBLK = MkBB [] [] (Branch labelPost) DMap.empty
    
    let trueG : CFG CBlock (Defined $ outsT ~~> labelTrue) (Defined [labelTrue ~> labelPost])
        trueG = SingleVertex {vins = Just outsT, vouts = Just [labelPost]} trueBLK
    
    
    let falseBLK : CBlock labelFalse (Just outsF) (Just [labelPost])
        falseBLK = MkBB [] [] (Branch labelPost) DMap.empty

    let falseG : CFG CBlock (Defined $ outsF ~~> labelFalse) (Defined [labelFalse ~> labelPost])
        falseG = SingleVertex {vins = Just outsF, vouts = Just [labelPost]} falseBLK
    
    
    reg <- lift freshRegister

    let phi : PhiExpr (MkInputs [labelTrue, labelFalse]) I1
        phi = Phi [(labelTrue, ILit 1), (labelFalse, ILit 0)]
    
    let phiAssignment = AssignPhi reg phi
    
    let postIns = MkInputs [labelTrue, labelFalse]
    
    let postBLK : CBlock labelPost (Just [labelTrue, labelFalse]) Undefined
        postBLK = phiAssignment |+> initCBlock

    let postG : CFG CBlock (Defined [labelTrue ~> labelPost, labelFalse ~> labelPost]) (Undefined labelPost)
        postG = SingleVertex {vins = Just [labelTrue, labelFalse], vouts = Undefined} postBLK


    let confluence = Series (Parallel trueG falseG) postG
    let final = Series {prf = nonempty_cmap_cmap $ nonempty_plusplus prfT} ifologyG confluence
    
    pure ((labelPost ** final), Var reg)

















