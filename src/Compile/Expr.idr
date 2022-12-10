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
import CFG

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
  
  0 nsuch : (k ** I k = GetLLType t)
  nsuch = case prf of
    EqCMPBool => (1 ** Refl)
    EqCMPInt => (32 ** Refl)
  
  in MkDPairI nsuch.fst (rewrite nsuch.snd in val, rewrite nsuch.snd in val')











mutual

  export
  compileExpr : (labelIn : BlockLabel)
             -> Expr t
             -> CompM ((lbl ** Graph VBlock (Undefined labelIn) (Undefined lbl)), LLValue (GetLLType t))



  compileExpr labelIn (Lit lit) = pure ((labelIn ** initG), fromLNGLit lit)

  compileExpr labelIn (Var var) = do
    
    {-
    TODO where to get values of variables from?
    
    possible solution: pass contexts as arguments, but then there is a lot of
    parameters
    -}
    val <- getValue var

    pure ((labelIn ** initG), val)

  

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
      reg <- freshRegister

      -- TODO: Is this OK or is it a hack?
      let g' = mapOut {outs = Undefined} (<+ Assign reg (BinOperation SUB (ILit 0) val)) g
      
      pure ((lbl ** g'), Var reg)

    Not => compileBoolExpr labelIn (UnOperation Not expr)

  
  compileExpr labelIn (Call fun args) = do
    funPtr <- getFunPtr fun

    ((lbl ** g), args') <- compileExprs labelIn args

    reg <- freshRegister
    let g' = mapOut {outs = Undefined} (<+ Assign reg (Call funPtr args')) g

    pure ((lbl ** g'), Var reg)
  



  -----------------------------------------------------------------------------
  compileExprs : (labelIn : BlockLabel)
              -> DList Expr ts
              -> CompM  ( (lbl ** Graph VBlock (Undefined labelIn) (Undefined lbl))
                        , DList LLValue (map GetLLType ts)
                        )
  compileExprs labelIn [] = pure ((labelIn ** initG), [])
  compileExprs labelIn (expr :: exprs) = do
    ((lbl ** g), val) <- compileExpr labelIn expr
    ((lbl' ** g'), vals) <- compileExprs lbl exprs

    let g'' = connect g g'
    
    pure ((lbl' ** g''), val :: vals)
  



  -----------------------------------------------------------------------------
  compileOperands : (labelIn : BlockLabel)
                 -> Expr t
                 -> Expr t'
                 -> CompM ( (lbl ** Graph VBlock (Undefined labelIn) (Undefined lbl))
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
                -> CompM ((lbl ** Graph VBlock (Undefined labelIn) (Undefined lbl)), LLValue I32)
  compileAritmOp labelIn op lhs rhs = do
    ((lbl ** g), lhs', rhs') <- compileOperands labelIn lhs rhs
    
    reg <- freshRegister
    let g' = mapOut {outs = Undefined} (<+ Assign reg (BinOperation op lhs' rhs')) g

    pure ((lbl ** g'), Var reg)
  


  -----------------------------------------------------------------------------
  compileOrdComparison : (labelIn : BlockLabel)
                      -> CMPKind
                      -> Expr TInt
                      -> Expr TInt
                      -> CompM ((lbl ** Graph VBlock (Undefined labelIn) (Undefined lbl)), LLValue I1)
  compileOrdComparison labelIn cmpKind lhs rhs = do
    ((lbl ** g), lhs', rhs') <- compileOperands labelIn lhs rhs

    (g', val) <- addICMP cmpKind g lhs' rhs'
    pure ((lbl ** g'), val)
  
    
  

  -----------------------------------------------------------------------------
  addICMP : CMPKind
         -> Graph VBlock ins (Undefined labelOut)
         -> LLValue (I k)
         -> LLValue (I k)
         -> CompM (Graph VBlock ins (Undefined labelOut), LLValue I1)
  addICMP cmpKind g lhs rhs = do
    reg <- freshRegister
    let g' = mapOut {outs = Undefined} (<+ Assign reg (ICMP cmpKind lhs rhs)) g
    
    pure (g', Var reg)
  


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
    ((lbl ** g), val) <- compileExpr labelIn expr
    let g' = mapOut {outs = Just [labelThen, labelElse]} (<+| CondBranch val labelThen labelElse) g
    
    let inputs = MkInputs [lbl]
    pure ([lbl ~> labelThen] ** [lbl ~> labelElse] ** (g', ALTCons ALTNil, ALTCons ALTNil))
  
  



  
  -----------------------------------------------------------------------------

  compileBoolExpr : (labelIn : BlockLabel)
                 -> Expr TBool
                 -> CompM ((lbl ** Graph VBlock (Undefined labelIn) (Undefined lbl)), LLValue I1)

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
    
    pure ((labelPost ** final), Var reg)

















