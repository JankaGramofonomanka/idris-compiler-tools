||| A module defining the compilation of LNG expressions
|||
||| Termonology used in this module:
||| * An *input label* is the label of the first block in a graph. This assumes
|||   the graph has only one entry point (input)
||| * By analogy, an *output label* is the label of the last block in a graph,
|||   assuming the graph has only one exit point (output)
module Compile.Expr

import Data.List

import Control.Monad.State
import Control.Monad.Either

import Data.Some
import Data.DList
import Data.Attached
import Data.Singleton
import Data.Typed

import LNG.BuiltIns
import LNG.TypeChecked
import LLVM

import Compile.Data.CompM
import Compile.Data.Context
import Compile.Data.Error
import Compile.Data.LLCBlock
import Compile.Utils
import ControlFlow.CFG

import Theory

||| Type of comparison - equality or inequality
data EQType = EQ' | NE'

||| Convert an `EQType` to a `CMPKind`
cmpKind : EQType -> CMPKind
cmpKind EQ' = EQ
cmpKind NE' = NE

-- TODO: consider having attached context in the state
||| A compiler monad with a variable context stored in addition to a `CompState`
public export
CompM' : Type -> Type
CompM' = StateT VarCTX CompM

||| Returns the value of a given variable
getValue : Variable t -> CompM' (LLValue (GetLLType t))
getValue var = do
  Just val <- gets (lookup var) | Nothing => lift $ throwError (NoSuchVariable var)
  pure val

||| "Compile" a literal.
||| Converts a literal into its LLVM representant.
||| Returns the LLVM value of the literal and a potentially empty graph needed
||| to be executed to produce that value.
||| @ lblIn  the input label of the returned graph
||| @ lit    the literal
||| @ rt     the return type of the function whose body the graph will be
|||          part of
||| @ lblOut the output label of the returned graph
compileLiteral
   : (lblIn : Label)
  -> (lit   : Literal t)
  -> CompM' ( ( lblOut
             ** CFG (LLCBlock rt) (Undefined lblIn) (Undefined lblOut)
              )
            , LLValue (GetLLType t)
            )
-- In case of the boolean ant integer literals, simply return a LLVM literal
-- and an empty graph.
compileLiteral lblIn (LitBool b)
  = pure $ ((lblIn ** emptyCFG), ILitV (if b then 1 else 0))
compileLiteral lblIn (LitInt i)
  = pure $ ((lblIn ** emptyCFG), ILitV i)

-- For string literals, return a pointer to the constant representing the
-- literal.
compileLiteral lblIn (LitString s) = do

  -- Retrieve the constant array representing the literal (`ctx`) and its
  -- length (`k`)
  (k ** cst) <- lift (getStringLiteral s)

  -- Generate a fresh reghister
  reg <- lift $ freshRegister (Ptr I8)

  -- Retrieve a pointer to the array and assign it
  let expr = GetElementPtr {k} {n = 32} (ConstPtr cst) (ILitV 0) (ILitV 0)

  -- Assign the pointer to the new registrer and put the assignment in a graph
  g <- pure $ omap (<+. Assign reg expr) emptyCFG

  -- Return the graph and the new register
  pure ((lblIn ** g), Var reg)

mutual

  ||| Compiles an expression.
  ||| Returns the value of the expression and a graph that computes it.
  ||| @ lblIn  the input label of the returned graph
  |||        / the label of the first block in the graph
  ||| @ expr   the compiled expression
  ||| @ rt     the return type of the function whose body the graph will be
  |||          part of
  ||| @ lblOut the output label of the returned graph
  |||        / the label of the last block in the graph
  export
  compileExpr
     : (lblIn : Label)
    -> (expr  : Expr t)
    -> CompM' ( ( lblOut
               ** CFG (LLCBlock rt) (Undefined lblIn) (Undefined lblOut)
                )
              , LLValue (GetLLType t)
              )

  -- A literal
  compileExpr lblIn (Lit lit) = compileLiteral lblIn lit

  -- A variable
  compileExpr lblIn (Var var) = do
    val <- getValue var
    pure ((lblIn ** emptyCFG), val)

  -- A binary operation
  compileExpr lblIn (BinOperation op lhs rhs) = case op of

    -- Compile operants and apply operator
    Add => compileBinOp lblIn I32 (BinOperation ADD)  lhs rhs
    Sub => compileBinOp lblIn I32 (BinOperation SUB)  lhs rhs
    Mul => compileBinOp lblIn I32 (BinOperation MUL)  lhs rhs
    Div => compileBinOp lblIn I32 (BinOperation SDIV) lhs rhs
    Mod => compileBinOp lblIn I32 (BinOperation SREM) lhs rhs

    -- Compile through jump statements
    And => compileBoolExpr lblIn (BinOperation And lhs rhs)
    Or  => compileBoolExpr lblIn (BinOperation Or  lhs rhs)

    -- Equality / inequality comparison
    EQ {prf} => compileEqComparison {prf} lblIn EQ' lhs rhs
    NE {prf} => compileEqComparison {prf} lblIn NE' lhs rhs

    -- Compile operants and apply "order-wise" comparison operator
    LE => compileBinOp lblIn I1 (ICMP SLE) lhs rhs
    LT => compileBinOp lblIn I1 (ICMP SLT) lhs rhs
    GE => compileBinOp lblIn I1 (ICMP SGE) lhs rhs
    GT => compileBinOp lblIn I1 (ICMP SGT) lhs rhs

    -- String concatenation
    Concat => do
      -- Compile the operands
      ((lblOut ** g), [lhs', rhs']) <- compileExprs lblIn [lhs, rhs]

      -- Generate a new register
      reg <- lift $ freshRegister (Ptr I8)

      -- Call the built in `.strconcat` function with the compiled operands as
      -- arguments and assign the result to the new register
      let g' = omap (<+. Assign reg (Call (ConstPtr strconcat) [lhs', rhs'])) g

      -- Return the graph and the new register
      pure ((lblOut ** g'), Var reg)

  -- An unary operation
  compileExpr lblIn (UnOperation op expr) = case op of

    -- Arithmetic negation
    Neg => do

      -- Compile the negated expression
      ((lblOut ** g), val) <- compileExpr lblIn expr

      -- Generate a new register
      reg <- lift (freshRegister I32)

      -- TODO: Is this OK or is it a hack?
      -- Assign the negation of the compiled expression to the new register
      let g' = omap (<+. Assign reg (BinOperation SUB (ILitV 0) val)) g

      pure ((lblOut ** g'), Var reg)

    -- Logical negation
    -- Compile through jump statements
    Not => compileBoolExpr lblIn (UnOperation Not expr)

  -- A function call
  compileExpr lblIn (Call fun args) = do

    -- Retrieve the fuction pointer representing the called function
    funPtr <- lift $ getFunPtr fun

    -- Compile the arguments
    ((lblOut ** g), args') <- compileExprs lblIn args

    -- Generate a fresh register
    reg <- lift (freshRegister' $ (unFun . unPtr) (typeOf funPtr))

    -- Call the function pointer with the compiled arguments and assign the
    -- result to the new register
    let g' = omap (<+. Assign reg (Call funPtr args')) g

    -- Return the graph and the new register
    pure ((lblOut ** g'), Var reg)

  -----------------------------------------------------------------------------
  ||| Compile multiple expressions into a graph with undefined edges at both
  ||| ends.
  ||| Returns a list of the values of the expressions and a graph that computes
  ||| these values.
  ||| @ lblIn  the input label of the returned graph
  ||| @ exprs  the expressions
  ||| @ rt     the return type of the function whose body the graph will be
  |||          part of
  ||| @ lblOut the output label of the returned graph
  compileExprs
     : (lblIn : Label)
    -> (exprs : DList Expr ts)
    -> CompM' ( ( lblOut
               ** CFG (LLCBlock rt) (Undefined lblIn) (Undefined lblOut)
                )
              , DList LLValue (map GetLLType ts)
              )
  compileExprs lblIn [] = pure ((lblIn ** emptyCFG), [])
  compileExprs lblIn (expr :: exprs) = do
    -- Compile the head and tail
    ((lbl    ** g),  val)  <- compileExpr  lblIn expr
    ((lblOut ** g'), vals) <- compileExprs lbl   exprs

    -- Connect the resulting graphs
    let g'' = g *~> g'

    -- Return the graph and the values
    pure ((lblOut ** g''), val :: vals)

  -----------------------------------------------------------------------------
  ||| Compile a binary operation by compiling the operands and adding a single
  ||| expression to complete the operation.
  ||| Returns the result of the operation and a graph that computes it.
  ||| @ lblIn  the input label of the returned graph
  ||| @ t      the (LLVM) type of the result of the operation
  ||| @ mkExpr the function producing an LLVM binary operation expression from
  |||          the values of the operands
  ||| @ lhs    the left operand
  ||| @ rhs    the right operand
  ||| @ rt     the return type of the function whose body the graph will be
  |||          part of
  ||| @ lblOut the output label of the returned graph
  compileBinOp
     : (lblIn  : Label)
    -> (t      : LLType)
    -> (mkExpr : LLValue (GetLLType t') -> LLValue (GetLLType t'') -> LLExpr t)
    -> (lhs    : Expr t')
    -> (rhs    : Expr t'')
    -> CompM' ( ( lblOut
               ** CFG (LLCBlock rt) (Undefined lblIn) (Undefined lblOut)
                )
              , LLValue t
              )
  compileBinOp lblIn t mkExpr lhs rhs = do

    -- Compile the operands
    ((lblOut ** g), [lhs', rhs']) <- compileExprs lblIn [lhs, rhs]

    -- Generate a new register
    reg <- lift (freshRegister t)

    -- Create an expression by applying `mkExpr` to the compiled operands and
    -- assign the result to the new register
    let g' = omap (<+. Assign reg (mkExpr lhs' rhs')) g

    pure ((lblOut ** g'), Var reg)

  -----------------------------------------------------------------------------
  ||| Compile a "equality-wise" comparison operation.
  ||| Returns the result of the comparison and a graph that computes it.
  ||| @ prf    a proof that the type of the operands is comparable
  |||          "equality-wise"
  ||| @ lblIn  the input label of the returned graph
  ||| @ eqType the type of comparioson - equality or inequality
  ||| @ lhs    the left operand
  ||| @ rhs    the right operand
  ||| @ rt     the return type of the function whose body the graph will be
  |||          part of
  ||| @ lblOut the output label of the returned graph
  compileEqComparison
     : {0 prf  : EqComparable t}
    -> (lblIn  : Label)
    -> (eqType : EQType)
    -> (lhs    : Expr t)
    -> (rhs    : Expr t)
    -> CompM' ( ( lblOut
               ** CFG (LLCBlock rt) (Undefined lblIn) (Undefined lblOut)
                )
              , LLValue I1
              )
  compileEqComparison lblIn eqType lhs rhs = case typeOf {f = Expr} lhs of

    -- Compile the operands and apply the comparison operator
    Val TInt    => compileBinOp lblIn I1 (ICMP $ cmpKind eqType) lhs rhs
    Val TBool   => compileBinOp lblIn I1 (ICMP $ cmpKind eqType) lhs rhs

    -- Compile the operands and call the built-in comparison function
    Val TString => do
      -- Compile the operands
      ((lblOut ** g), [lhs', rhs']) <- compileExprs lblIn [lhs, rhs]

      -- TODO here the `eqType` is discarded and the code acts as if it is `EQ'`
      -- Generate a new register
      reg <- lift $ freshRegister I1

      -- Call the built-in `.strcompare` function on the compiled operands and
      -- assign the result to the new register
      let g' = omap (<+. Assign reg (Call (ConstPtr strcompare) [lhs', rhs'])) g

      -- Return the graph and the new register
      pure ((lblOut ** g'), Var reg)

    -- Impossibnle: comapring voids
    Val TVoid   => let

        -- A proof that `void`s are not comparable
        0 impossiblePrf : (CompM' ((lblOut ** CFG (LLCBlock rt) (Undefined lblIn) (Undefined lblOut)), LLValue I1) = ())
        impossiblePrf = exfalso (voidNotEqComparable prf)

      in rewrite impossiblePrf in ()

  -----------------------------------------------------------------------------
  ||| Compiles a boolean expression through jump statements.
  ||| Given a boolean expression and labels of a "true" block and a "false"
  ||| block, produces a graph whose execution ends in the "true" block when the
  ||| expression is true and in the "false" block if it is false.
  |||
  ||| Returns the graph and the list of its "true" and "false" outputs.
  ||| The "false" and "true" outputs are the labels of blocks from which the
  ||| control flow jumps to the "false" and "rtrue" block respectively.
  |||
  ||| The binary boolean expressions are evalueated lazily. That means, if
  ||| evaluating the left operand gives a value such that the result is already
  ||| known, the right operand is not evalueted.
  |||
  ||| @ lblIn  the input label of the returned graph
  ||| @ expr   the compiled expression
  ||| @ lblT   the "true" block label
  ||| @ lblF   the "false" block label
  ||| @ outsT  the "true" outputs
  ||| @ outsF  the "false" outputs
  ||| @ rt     the return type of the function whose body the graph will be
  |||          part of
  ||| @ lblOut the output label of the returned graph
  export
  ifology
     : (lblIn : Label)
    -> (expr : Expr TBool)
    -> (lblT : Label)
    -> (lblF : Label)
    -> CompM' ( outsT
             ** outsF
             ** CFG (LLCBlock rt)
                    (Undefined lblIn)
                    (Defined $ outsT ~~> lblT ++ outsF ~~> lblF)
              )

  -- Logical and
  ifology lblIn (BinOperation And lhs rhs) lblT lblF = do

    -- Generate the "middle" label
    lblM <- lift freshLabel

    -- Compile the left operand
    --
    -- Pass the "false" label as the "false" label - if the left opperand is
    -- false, the result of the operation is also false
    --
    -- Pass the "middle" label as the "true" label - if the left opperand is
    -- true, we still have to evaluate the right operand
    --
    -- Pass the input label as the input label - this operand will be evaluated
    -- first, so its graph will be the "prefix" of the graph of the entire
    -- operation, and thus it will start in the same block.
    (outsM ** outsF ** gl) <- ifology lblIn lhs lblM lblF

    -- Compile the right operand
    --
    -- Note: if the control flow gets to evaluating `rhs`, this means `lhs` is
    -- true,
    -- that means the result of the logical and is the same as the value of
    -- `rhs`.
    --
    -- Given the note above, the "true" and "false" labels passed here are
    -- exactly the "true" and "false" labels of the entire operation.
    --
    -- Pass the "middle" label as the input label - the computation of `rhs`
    -- starts after `lhs` is evaluated to be true.
    (outsT ** outsF' ** gr) <- ifology lblM rhs lblT lblF

    -- Define the inputs of the graph of `rhs` as the "true" outputs of the
    -- graph of `lhs`.
    let gr' = imap {ins = Just outsM} ([] |++>) gr

    -- Construct the final graph by connecting the graph of `lhs` and `rhs`.
    -- Rearange their output parameters using proofs of simple theorems to fit
    -- them into the functions type signature
    let final : CFG (LLCBlock rt)
                    (Undefined lblIn)
                    (Defined $ outsT ~~> lblT ++ (outsF' ++ outsF) ~~> lblF)
        final = rewrite collect_concat lblF outsF' outsF
                in rewrite concat_assoc (outsT ~~> lblT) (outsF' ~~> lblF) (outsF ~~> lblF)
                in lbranch gl gr'

    -- Return the final graph and its "true" and "false" outputs
    pure (outsT ** outsF' ++ outsF ** final)

  -- Logical or (by analogy to logical and)
  ifology lblIn (BinOperation Or lhs rhs) lblT lblF = do

    -- Generate the "middle" label
    lblM <- lift freshLabel

    -- Compile the left operand
    --
    -- Pass the "true" label as the "true" label - if the left opperand is
    -- true, the result of the operation is also true
    --
    -- Pass the "middle" label as the "false" label - if the left opperand is
    -- false, we still have to evaluate the right operand
    --
    -- Pass the input label as the input label - this operand will be evaluated
    -- first, so its graph will be the "prefix" of the graph of the entire
    -- operation, and thus it will start in the same block.
    (outsT ** outsM ** gl) <- ifology lblIn lhs lblT lblM

    -- Compile the right operand
    --
    -- Note: if the control flow gets to evaluating `rhs`, this means `lhs` is
    -- false,
    -- that means the result of the logical or is the same as the value of
    -- `rhs`.
    --
    -- Given the note above, the "true" and "false" labels passed here are
    -- exactly the "true" and "false" labels of the entire operation.
    --
    -- Pass the "middle" label as the input label - the computation of `rhs`
    -- starts after `lhs` is evaluated to be false.
    (outsT' ** outsF ** gr) <- ifology lblM rhs lblT lblF

    -- Define the inputs of the graph of `rhs` as the "true" outputs of the
    -- graph of `lhs`.
    let gr' = imap {ins = Just outsM} ([] |++>) gr

    -- Construct the final graph by connecting the graph of `lhs` and `rhs`.
    -- Rearange their output parameters using proofs of simple theorems to fit
    -- them into the functions type signature
    let final : CFG (LLCBlock rt)
                    (Undefined lblIn)
                    (Defined ((outsT ++ outsT') ~~> lblT ++ outsF ~~> lblF))
        final = rewrite collect_concat lblT outsT outsT'
                in rewrite revEq $ concat_assoc (outsT ~~> lblT) (outsT' ~~> lblT) (outsF ~~> lblF)
                in rbranch gl gr'

    -- Return the final graph and its "true" and "false" outputs
    pure (outsT ++ outsT' ** outsF ** final)

  -- Logical negation
  ifology lblIn (UnOperation Not expr) lblT lblF = do

    -- Compile the negated expression
    (outsF ** outsT ** g) <- ifology lblIn expr lblF lblT

    -- Swap the "true" outputs with the "false" outputs
    pure (outsT ** outsF ** OFlip g)

  -- Default case
  ifology lblIn expr lblT lblF = do

    -- Compile the expression the "normal" way
    ((lbl ** g), val) <- compileExpr lblIn expr

    -- Branch to the "true" or "false" block based on the value of the
    -- compuiled expression.
    let g' = omap (<+| CondBranch val lblT lblF) g

    pure ([lbl] ** [lbl] ** g')

  -----------------------------------------------------------------------------
  ||| Compiles a boolean expression by adding a merging block to the graph
  ||| produced by `ifology`.
  ||| Returns the value of the expression and a graph that computes it.
  ||| @ lblIn  the input label of the returned graph
  ||| @ expr   the compiled expression
  ||| @ rt     the return type of the function whose body the graph will be
  |||          part of
  ||| @ lblOut the output label of the returned graph
  compileBoolExpr
     : (lblIn : Label)
    -> (expr  : Expr TBool)
    -> CompM' ( ( lblOut
               ** CFG (LLCBlock rt) (Undefined lblIn) (Undefined lblOut)
                )
              , LLValue I1
              )

  compileBoolExpr lblIn expr = do

    -- Note:
    -- Here, I compile the expression and add two empty blocks after the true
    -- and false outputs. Then, I add a merging block where the value of the
    -- expression is determined by the label of one of these blocks.
    -- This might seem superfluous: why not jump straight to the merging block?
    -- It is not as simple and the reason for that is that the expression might
    -- be coimputed in a single basic block that ends in a conditional jump.
    -- Then, the phi assignment in the merging block would contain the same
    -- block label twice, which is not a valid LLVM statement.

    -- Generate the "true" and "false" labels and compile the expression using
    -- jump statements
    lblTrue  <- lift freshLabel
    lblFalse <- lift freshLabel
    (outsT ** outsF ** ifologyG) <- ifology lblIn expr lblTrue lblFalse

    -- Generate a "post" label - the label of the merging block
    lblPost <- lift freshLabel

    -- Construct the "true" block and put it in a singleton graph
    trueBLK <- pure $ [] |++> emptyCBlock <+| Branch lblPost
    let trueG : CFG (LLCBlock rt) (Defined $ outsT ~~> lblTrue) (Defined [lblTrue ~> lblPost])
        trueG = SingleVertex {vins = Just outsT, vouts = Just [lblPost]} trueBLK

    -- Construct the "false" block and put it in a singleton graph
    falseBLK <- pure $ [] |++> emptyCBlock <+| Branch lblPost
    let falseG : CFG (LLCBlock rt) (Defined $ outsF ~~> lblFalse) (Defined [lblFalse ~> lblPost])
        falseG = SingleVertex {vins = Just outsF, vouts = Just [lblPost]} falseBLK

    -- Make a "phi" assignment.
    -- The value of the expression is `true` or `false` when coming from the
    -- "true" or "false" block respectively.
    let phi : PhiExpr [lblTrue, lblFalse] I1
        phi = Phi I1 [(lblTrue, ILitV 1), (lblFalse, ILitV 0)]

    -- Generate a new register and assign the phi expression to the new
    -- register.
    -- The new register now contains the value of the compiled expression (`expr`)
    reg <- lift (freshRegister I1)
    let phiAssignment = AssignPhi reg phi

    -- The inputs of the "post" block (the merging block)
    let postIns = [lblTrue, lblFalse]

    -- Construct the merging block and put it in a singleton graph
    postBLK <- pure $ phiAssignment |+.> emptyCBlock
    let postG : CFG (LLCBlock rt) (Defined [lblTrue ~> lblPost, lblFalse ~> lblPost]) (Undefined lblPost)
        postG = SingleVertex {vins = Just [lblTrue, lblFalse], vouts = Undefined} postBLK

    -- Construct the final graph
    let final = ifologyG *-> (trueG |-| falseG) *-> postG

    -- Retunr the final graph, its output label and the value of the expression
    pure ((lblPost ** final), Var reg)
