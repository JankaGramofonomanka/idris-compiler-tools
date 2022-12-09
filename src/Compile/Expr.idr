module Compile.Expr

import Control.Monad.State

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
import CFG.Simple

import Utils





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
  compileExpr : (labelIn : BlockLabel)
             -> Expr t
             -> CompM ((lbl ** CompileResult labelIn (Just lbl)), LLValue (GetLLType t))



  compileExpr labelIn (Lit lit) = pure ((labelIn ** initCR), fromLNGLit lit)

  compileExpr labelIn (Var var) = do
    
    {-
    TODO where to get values of variables from?
    
    possible solution: pass contexts as arguments, but then there is a lot of
    parameters
    -}
    val <- getValue var

    pure ((labelIn ** initCR), val)

  

  compileExpr labelIn (BinOperation op lhs rhs) = case op of
    Add => compileAritmOp labelIn ADD lhs rhs
    Sub => compileAritmOp labelIn SUB lhs rhs
    Mul => compileAritmOp labelIn MUL lhs rhs
    Div => compileAritmOp labelIn SDIV lhs rhs
    
    And => compileBoolExpr labelIn (BinOperation And lhs rhs)
    Or  => compileBoolExpr labelIn (BinOperation Or  lhs rhs)
    
    EQ => do
        ((lbl ** res), lhs', rhs') <- compileOperands labelIn lhs rhs
        let MkDPairI n (lhs'', rhs'') = integerize (lhs', rhs')

        (res', val) <- addICMP EQ res lhs'' rhs''
        pure ((lbl ** res'), val)

    LE => compileOrdComparison labelIn SLE lhs rhs
    LT => compileOrdComparison labelIn SLT lhs rhs
    GE => compileOrdComparison labelIn SGE lhs rhs
    GT => compileOrdComparison labelIn SGT lhs rhs
  
  

  compileExpr labelIn (UnOperation op expr) = case op of
    
    Neg => do

      ((lbl ** res), val) <- compileExpr labelIn expr
      reg <- freshRegister

      -- TODO: Is this OK or is it a hack?
      let res' = mapOO (<+ Assign reg (BinOperation SUB (ILit 0) val)) res
      
      pure ((lbl ** res'), Var reg)

    Not => compileBoolExpr labelIn (UnOperation Not expr)

  
  compileExpr labelIn (Call fun args) = do
    funPtr <- getFunPtr fun

    ((lbl ** res), args') <- compileExprs labelIn args

    reg <- freshRegister
    let res' = mapOO (<+ Assign reg (Call funPtr args')) res

    pure ((lbl ** res'), Var reg)
  



  -----------------------------------------------------------------------------
  compileExprs : (labelIn : BlockLabel)
              -> DList Expr ts
              -> CompM  ( (lbl ** CompileResult labelIn (Just lbl))
                        , DList LLValue (map GetLLType ts)
                        )
  compileExprs labelIn [] = pure ((labelIn ** initCR), [])
  compileExprs labelIn (expr :: exprs) = do
    ((lbl ** res), val) <- compileExpr labelIn expr
    ((lbl' ** res'), vals) <- compileExprs lbl exprs

    let res'' = combineCR res res'
    
    pure ((lbl' ** res''), val :: vals)
  



  -----------------------------------------------------------------------------
  compileOperands : (labelIn : BlockLabel)
                 -> Expr t
                 -> Expr t'
                 -> CompM ( (lbl ** CompileResult labelIn (Just lbl))
                          , LLValue (GetLLType t)
                          , LLValue (GetLLType t')
                          )

  compileOperands labelIn lhs rhs = do
    
    ((labelL ** resL), lhs') <- compileExpr labelIn lhs
    ((labelR ** resR), rhs') <- compileExpr labelL rhs
  
    let resLR = combineCR resL resR
    pure ((labelR ** resLR), lhs', rhs')
  



  -----------------------------------------------------------------------------
  compileAritmOp : (labelIn : BlockLabel)

                -> BinOperator I32 I32 I32
                -> Expr TInt
                -> Expr TInt
                -> CompM ((lbl ** CompileResult labelIn (Just lbl)), LLValue I32)
  compileAritmOp labelIn op lhs rhs = do
    ((lbl ** res), lhs', rhs') <- compileOperands labelIn lhs rhs
    
    reg <- freshRegister
    let res' = mapOO (<+ Assign reg (BinOperation op lhs' rhs')) res

    pure ((lbl ** res'), Var reg)
  


  -----------------------------------------------------------------------------
  compileOrdComparison : (labelIn : BlockLabel)
                      -> CMPKind
                      -> Expr TInt
                      -> Expr TInt
                      -> CompM ((lbl ** CompileResult labelIn (Just lbl)), LLValue I1)
  compileOrdComparison labelIn cmpKind lhs rhs = do
    ((lbl ** res), lhs', rhs') <- compileOperands labelIn lhs rhs

    (res', val) <- addICMP cmpKind res lhs' rhs'
    pure ((lbl ** res'), val)
  
    
  

  -----------------------------------------------------------------------------
  addICMP : CMPKind
         -> CompileResult labelIn (Just labelOut)
         -> LLValue (I n)
         -> LLValue (I n)
         -> CompM (CompileResult labelIn (Just labelOut), LLValue I1)
  addICMP cmpKind res lhs rhs = do
    reg <- freshRegister
    let res' = mapOO (<+ Assign reg (ICMP cmpKind lhs rhs)) res
    
    pure (res', Var reg)
  


  -----------------------------------------------------------------------------
  
  {-
  Add branch instructions such that when the value of `expr` is `true`, then the
  execution of the program will end up in `labelThen` and in `labelElse`
  otherwise.
  -}
  export
  ifology : (labelIn : BlockLabel)
         -> (expr : Expr TBool)
         -> (labelThen : BlockLabel)
         -> (labelElse : BlockLabel)
         -> CompM ( outsThen ** outsElse ** 
                    ( Graph VBlock (Undefined labelIn) (Ends $ outsThen ++ outsElse)
                    , outsThen `AllLeadTo` labelThen
                    , outsElse `AllLeadTo` labelElse
                    )
                  )

  ifology labelIn (BinOperation And lhs rhs) labelThen labelElse = do

    labelMid <- freshLabel
    (outsMid  ** outsElse   ** (gl, prfM, prfE))  <- ifology labelIn  lhs labelMid  labelElse
    (outsThen ** outsElse'  ** (gr, prfT, prfE')) <- ifology labelMid rhs labelThen labelElse


    let gr' : Graph VBlock (Ends outsMid) (Ends $ outsThen ++ outsElse')
        gr' = rewrite alt_map prfM
              in mapIn {ins = Just (map Origin outsMid)} ([] |++>) gr
    
    let inter : Graph VBlock (Ends $ outsMid ++ outsElse) (Ends (outsThen ++ outsElse' ++ outsElse))
        inter = rewrite concat_assoc outsThen outsElse' outsElse
                in Parallel gr' Empty

    let final = Connect gl inter
    
    pure (outsThen ** outsElse' ++ outsElse ** (final, prfT, alt_concat prfE' prfE))
  
  ifology labelIn (BinOperation Or lhs rhs) labelThen labelElse = do

    labelMid <- freshLabel
    (outsThen   ** outsMid  ** (gl, prfT,   prfM)) <- ifology labelIn   lhs labelThen labelMid
    (outsThen'  ** outsElse ** (gr, prfT',  prfE)) <- ifology labelMid  rhs labelThen labelElse


    let gr' : Graph VBlock (Ends outsMid) (Ends $ outsThen' ++ outsElse)
        gr' = rewrite alt_map prfM
              in mapIn {ins = Just (map Origin outsMid)} ([] |++>) gr
    
    let inter : Graph VBlock (Ends $ outsThen ++ outsMid) (Ends ((outsThen ++ outsThen') ++ outsElse))
        inter = rewrite revEq $ concat_assoc outsThen outsThen' outsElse
                in Parallel Empty gr'

    let final = Connect gl inter
    
    pure (outsThen ++ outsThen' ** outsElse ** (final, alt_concat prfT prfT', prfE))
  
  ifology labelIn (UnOperation Not expr) labelThen labelElse = do
    (outsElse ** outsThen ** (g, prfE, prfT)) <- ifology labelIn expr labelElse labelThen
    pure (outsThen ** outsElse ** (FlipOut g, prfT, prfE))
  
  ifology labelIn expr labelThen labelElse = do
    ((lbl ** CROpen g), val) <- compileExpr labelIn expr
    let g' = mapOut {outs = Just [labelThen, labelElse]} (<+| CondBranch val labelThen labelElse) g
    
    let inputs = MkInputs [lbl]
    pure ([lbl ~> labelThen] ** [lbl ~> labelElse] ** (g', ALTCons ALTNil, ALTCons ALTNil))
  
  



  
  -----------------------------------------------------------------------------

  compileBoolExpr : (labelIn : BlockLabel)
                 -> Expr TBool
                 -> CompM ((lbl ** CompileResult labelIn (Just lbl)), LLValue I1)

  compileBoolExpr labelIn expr = do
    labelTrue <- freshLabel
    labelFalse <- freshLabel
    (outsT ** outsF ** (ifologyG, prfT, prfF)) <- ifology labelIn expr labelTrue labelFalse
    
    labelPost <- freshLabel
    
    
    let trueBLK : VBlock labelTrue (Just $ map Origin outsT) (Just [labelPost])
        trueBLK = MkBB [] [] (Branch labelPost) DMap.empty
    
    let trueG : Graph VBlock (Ends outsT) (Ends [labelTrue ~> labelPost])
        trueG = rewrite alt_map prfT
                in SingleVertex {vins = Just $ map Origin outsT, vouts = Just [labelPost]} trueBLK
    
    
    let falseBLK : VBlock labelFalse (Just $ map Origin outsF) (Just [labelPost])
        falseBLK = MkBB [] [] (Branch labelPost) DMap.empty

    let falseG : Graph VBlock (Ends outsF) (Ends [labelFalse ~> labelPost])
        falseG = rewrite alt_map prfF
                 in SingleVertex {vins = Just $ map Origin outsF, vouts = Just [labelPost]} falseBLK
    
    
    reg <- freshRegister

    let phi : PhiExpr (MkInputs [labelTrue, labelFalse]) I1
        phi = Phi [(labelTrue, ILit 1), (labelFalse, ILit 0)]
    
    let phiAssignment = AssignPhi reg phi
    
    let postIns = MkInputs [labelTrue, labelFalse]
    
    let postBLK : VBlock labelPost (Just [labelTrue, labelFalse]) Undefined
        postBLK = phiAssignment |+> initCBlock

    let postG : Graph VBlock (Ends [labelTrue ~> labelPost, labelFalse ~> labelPost]) (Undefined labelPost)
        postG = SingleVertex {vins = Just [labelTrue, labelFalse], vouts = Undefined} postBLK



    let confluence = Connect (Parallel trueG falseG) postG
    let final = Connect ifologyG confluence
    
    pure ((labelPost ** CROpen final), Var reg)

















