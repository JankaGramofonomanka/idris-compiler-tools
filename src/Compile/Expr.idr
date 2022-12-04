module Compile.Expr

import Control.Monad.State

import Data.Some
import Data.DMap
import Data.DList
import Data.Attached

import LNG
import LLVM

import Compile.Tools





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
  
  0 nsuch : (n ** I n = GetLLType t)
  nsuch = case prf of
    EqCMPBool => (1 ** Refl)
    EqCMPInt => (32 ** Refl)
  
  in MkDPairI nsuch.fst (rewrite nsuch.snd in val, rewrite nsuch.snd in val')












mutual

  export
  compileExpr : (labelIn : Some BlockLabel)
             -> Expr t
             -> CompM (LabelResult Open, CompileResult Open, LLValue (GetLLType t))



  compileExpr labelIn (Lit lit) = pure (LastLabel labelIn, initCR, fromLNGLit lit)


  compileExpr labelIn (Var var) = do
    
    {-
    TODO where to get values of variables from?
    
    possible solution: pass contexts as arguments, but then there is a lot of
    parameters
    -}
    val <- getValue var

    pure (LastLabel labelIn, initCR, val)


  compileExpr labelIn (BinOperation op lhs rhs) = case op of
    Add => compileAritmOp labelIn ADD lhs rhs
    Sub => compileAritmOp labelIn SUB lhs rhs
    Mul => compileAritmOp labelIn MUL lhs rhs
    Div => compileAritmOp labelIn SDIV lhs rhs
    
    And => compileBoolExpr labelIn (BinOperation And lhs rhs)
    Or  => compileBoolExpr labelIn (BinOperation Or  lhs rhs)
    
    EQ => do
        (labelRes, res, lhs', rhs') <- compileOperands labelIn lhs rhs
        let MkDPairI n (lhs'', rhs'') = integerize (lhs', rhs')

        addICMP EQ labelRes res lhs'' rhs''

    LE => compileOrdComparison labelIn SLE lhs rhs
    LT => compileOrdComparison labelIn SLT lhs rhs
    GE => compileOrdComparison labelIn SGE lhs rhs
    GT => compileOrdComparison labelIn SGT lhs rhs
    

  compileExpr labelIn (UnOperation op expr) = case op of
    
    Neg => do

      (labelRes, res, val) <- compileExpr labelIn expr
      reg <- freshRegister

      -- TODO: Is this OK or is it a hack?
      let res' = mapOO (<+ Assign reg (BinOperation SUB (ILit 0) val)) res
      
      pure (labelRes, res', Var reg)

    Not => compileBoolExpr labelIn (UnOperation Not expr)


  compileExpr labelIn (Call fun args) = do
    funPtr <- getFunPtr fun

    (labelRes, res, args') <- compileExprs labelIn args

    reg <- freshRegister
    let res' = mapOO (<+ Assign reg (Call funPtr args')) res

    pure (labelRes, res', Var reg)




  -----------------------------------------------------------------------------
  compileExprs : (labelIn : Some BlockLabel)
              -> DList Expr ts
              -> CompM  ( LabelResult Open
                        , CompileResult Open
                        --, DList (LLValue . GetLLType) ts
                        , DList LLValue (map GetLLType ts)
                        )

  compileExprs labelIn [] = pure (LastLabel labelIn, initCR, [])
  compileExprs labelIn (expr :: exprs) = do
    (LastLabel lbl, res, val) <- compileExpr labelIn expr
    (LastLabel lbl', res', vals) <- compileExprs lbl exprs

    res'' <- combineCR res res'
    
    pure (LastLabel lbl', res', val :: vals)
  



  -----------------------------------------------------------------------------
  compileOperands : Some BlockLabel
                 -> Expr t
                 -> Expr t'
                 -> CompM ( LabelResult Open
                          , CompileResult Open
                          , LLValue (GetLLType t)
                          , LLValue (GetLLType t')
                          )

  compileOperands labelIn lhs rhs = do
    
    (LastLabel labelL, resL, lhs') <- compileExpr labelIn lhs
    (LastLabel labelR, resR, rhs') <- compileExpr labelL rhs
  
    resLR <- combineCR resL resR
    pure (LastLabel labelR, resLR, lhs', rhs')




  -----------------------------------------------------------------------------
  compileAritmOp : Some BlockLabel
                -> BinOperator I32 I32 I32
                -> Expr TInt
                -> Expr TInt
                -> CompM (LabelResult Open, CompileResult Open, LLValue I32)
  compileAritmOp labelIn op lhs rhs = do
    (labelRes, res, lhs', rhs') <- compileOperands labelIn lhs rhs
    
    reg <- freshRegister
    let res' = mapOO (<+ Assign reg (BinOperation op lhs' rhs')) res

    pure (labelRes, res', Var reg)
  


  -----------------------------------------------------------------------------
  compileOrdComparison : Some BlockLabel
                      -> CMPKind
                      -> Expr TInt
                      -> Expr TInt
                      -> CompM (LabelResult Open, CompileResult Open, LLValue I1)
  compileOrdComparison labelIn cmpKind lhs rhs = do
    (labelRes, res, lhs', rhs') <- compileOperands labelIn lhs rhs

    addICMP cmpKind labelRes res lhs' rhs'
    
  

  -----------------------------------------------------------------------------
  addICMP : CMPKind
         -> LabelResult Open
         -> CompileResult Open
         -> LLValue (I n)
         -> LLValue (I n)
         -> CompM (LabelResult Open, CompileResult Open, LLValue I1)
  addICMP cmpKind labelRes res lhs rhs = do
    reg <- freshRegister
    let res' = mapOO (<+ Assign reg (ICMP cmpKind lhs rhs)) res
    
    pure (labelRes, res', Var reg)



  -----------------------------------------------------------------------------
  {-
  Add branch instructions such that when the value of `expr` is `true`, then the
  execution of the program will end up in `labelThen` and in `labelElse`
  otherwise.
  -}
  export
  ifology : (labelIn : Some BlockLabel)
         -> (expr : Expr TBool)
         -> (labelThen : BlockLabel NonEntry)
         -> (labelElse : BlockLabel NonEntry)
         -> CompM ( Attached labelThen $ Inputs NonEntry
                  , Attached labelElse $ Inputs NonEntry
                  , CompileResult Closed
                  )

  ifology labelIn (BinOperation And lhs rhs) labelThen labelElse = do

    labelMid <- freshLabel
    (insMid,  insElse,  resL) <- ifology labelIn            lhs labelMid  labelElse
    (insThen, insElse', resR) <- ifology (MkSome labelMid)  rhs labelThen labelElse

    
    let SingleBLKC (cfk ** blk) = resR
    let IS : InStatus;  IS = InClosed NonEntry labelMid (detach insMid)
    let OS : OutStatus; OS = OutClosed cfk

    -- TODO: phis
    let blk': CBlock IS OS
        blk' = ?hphis_ifology_And |++> blk
    addBlock blk'

    pure (insThen, combine (++) insElse insElse', resL)
  
  ifology labelIn (BinOperation Or lhs rhs) labelThen labelElse = do
    
    labelMid <- freshLabel
    (insThen,   insMid,   resL) <- ifology labelIn            lhs labelThen labelMid
    (insThen',  insElse,  resR) <- ifology (MkSome labelMid)  rhs labelThen labelElse

    let SingleBLKC (cfk ** blk) = resR
    let IS : InStatus;  IS = InClosed NonEntry labelMid (detach insMid)
    let OS : OutStatus; OS = OutClosed cfk

    -- TODO: phis
    let blk' : CBlock IS OS
        blk' = ?hphis_ifology_Or |++> blk
    addBlock blk'

    pure (combine (++) insThen insThen', insElse, resL)

  ifology labelIn (UnOperation Not expr) labelThen labelElse = do
    (insElse, insThen, res) <- ifology labelIn expr labelElse labelThen
    pure (insThen, insElse, res)
  
  ifology labelIn expr labelThen labelElse = do
    (LastLabel lbl, res, val) <- compileExpr labelIn expr
    res' <- closeCR (CondBranch val labelThen labelElse) res
    
    let inputs = MkInputs [lbl]
    pure (Attach labelThen inputs, Attach labelElse inputs, res')
    



  
  -----------------------------------------------------------------------------

  -- TODO: this is ugly
  compileBoolExpr : (labelIn : Some BlockLabel)
                 -> Expr TBool
                 -> CompM (LabelResult Open, CompileResult Open, LLValue I1)
  compileBoolExpr labelIn expr = do
    labelTrue <- freshLabel
    labelFalse <- freshLabel
    (trueInputs, falseInputs, SingleBLKC blkIn) <- ifology labelIn expr labelTrue labelFalse
    
    labelPost <- freshLabel
    
    let TrueIS : InStatus;  TrueIS = InClosed NonEntry labelTrue (detach trueInputs)
    let TrueOS : OutStatus; TrueOS = OutClosed (Jump [labelPost])

    let FalseIS : InStatus;   FalseIS = InClosed NonEntry labelFalse (detach falseInputs)
    let FalseOS : OutStatus;  FalseOS = OutClosed (Jump [labelPost])

    let trueBLK : CBlock TrueIS TrueOS
        trueBLK = MkBB [] [] (Branch labelPost) DMap.empty
    
    let falseBLK : CBlock FalseIS FalseOS
        falseBLK = MkBB [] [] (Branch labelPost) DMap.empty
    
    addBlock trueBLK
    addBlock falseBLK



    reg <- freshRegister
    
    let inputs : Inputs NonEntry; inputs = MkInputs [MkSome labelTrue, MkSome labelFalse]
    
    let OutIS : InStatus; OutIS = InClosed NonEntry labelPost inputs
    
    let phi = Phi [(MkSome labelTrue, ILit 1), (MkSome labelFalse, ILit 0)]
    let phiAssignment = AssignPhi reg phi

    let blkOut : CBlock OutIS OutOpen
        blkOut = phiAssignment |+> initCBlock

    let res = DoubleBLK blkIn (NonEntry ** labelPost ** inputs ** blkOut)
    pure (LastLabel $ MkSome labelPost, res, Var reg)

















