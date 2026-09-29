module

/-
Kraken - x86_64 Assembly Interpreter

Root module. The baseline instruction semantics is `Operation.interp` in
Kraken/X64/Semantics.lean, in continuation-passing style over `Effects`.
Kraken/MachineWP.lean is the machine-founded weakest precondition on the deep
embedding. Kraken/SepWP.lean is the separation-logic weakest precondition over
the baseline's burst run, with the instruction specs of Kraken/SepSpecs.lean
and the frame inference of Kraken/SepFrameProc.lean. Both are discharged by the
`Std.WP` `vcgen` pipeline.
-/

public import Kraken.X64.Semantics
public import Kraken.X64.Parser
public import Kraken.X64.OmniSemantics
public import Kraken.X64.Sep
public import Kraken.Specs
public import Kraken.Tactics
public import Kraken.MachineWP
public import Kraken.SepWP
public import Kraken.SepSpecs
public import Kraken.SepFrameProc
import Kraken.X64.Examples.Examples
import Kraken.X64.Examples.SepAluMem
import Kraken.X64.Examples.SepDynamicStack
import Kraken.X64.Examples.SepMove2RegsToHeap
import Kraken.X64.Examples.SepPushPop
import Kraken.X64.Examples.SepSib
import Kraken.X64.Examples.SepSwap
