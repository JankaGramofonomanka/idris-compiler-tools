module ControlFlow.CFG.Conversion

import ControlFlow.CFG
import ControlFlow.CFG.Simple

public export
Simplify : CFG.Vertex a -> Simple.Vertex a
Simplify vertex v ins outs = vertex v (Just ins) (Just outs)

public export
Unsimplify : Simple.Vertex a -> CFG.Vertex a
Unsimplify vertex v _          Nothing     = Void
Unsimplify vertex v Nothing    _           = Void
Unsimplify vertex v (Just ins) (Just outs) = vertex v ins outs

||| Convert a control-flow graph (`CFG.CFG`) with defined inputs and outputs
||| into a simplified control-flow graph (`CFG.Simple.CFG`)
export
simplify : CFG vertex (Defined ins) (Defined outs) -> CFG (Simplify vertex) ins outs
simplify (SingleVertex {vins = Just ins, vouts = Just outs} v) = SingleVertex v
simplify Empty             = Empty
simplify (Cycle node loop) = Cycle (simplify node) (simplify loop)
simplify (Series g g')     = Series (simplify g) (simplify g')
simplify (Parallel g g')   = Parallel (simplify g) (simplify g')
simplify (IFlip g)         = IFlip (simplify g)
simplify (OFlip g)         = OFlip (simplify g)

simplify (SingleVertex {vins  = Nothing} v) impossible
simplify (SingleVertex {vouts = Nothing} v) impossible

||| Convert a simplified control-flow graph (`CFG.Simple.CFG`) into an
||| "unsimplified" control-flow graph (`CFG.CFG`) with defined inputs and
||| outputs
export
unsimplify : Simple.CFG vertex ins outs -> CFG (Unsimplify vertex) (Defined ins) (Defined outs)
unsimplify (SingleVertex {vins, vouts} v) = SingleVertex {vins = Just vins, vouts = Just vouts} v
unsimplify Empty             = Empty
unsimplify (Cycle node loop) = Cycle (unsimplify node) (unsimplify loop)
unsimplify (Series g g')     = Series (unsimplify g) (unsimplify g')
unsimplify (Parallel g g')   = Parallel (unsimplify g) (unsimplify g')
unsimplify (IFlip g)         = IFlip (unsimplify g)
unsimplify (OFlip g)         = OFlip (unsimplify g)
