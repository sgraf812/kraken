module

/-
Kraken - x86_64 Assembly Interpreter

Root module. The baseline instruction semantics is `Operation.interp` in
Kraken/X64/Semantics.lean, in continuation-passing style over `Effects`.
Kraken/ProgramRun.lean is the run of a program fragment in the baseline's
burst. Kraken/StateWP.lean interprets a program by its run at predicates over
machine states, and Kraken/SepWP.lean at separation-logic assertions over the
memory, with the instruction specs of Kraken/SepSpecs.lean and the frame
inference of Kraken/SepFrameProc.lean. Kraken/MachineWP.lean is the
machine-founded weakest precondition over one instruction at a time. All of
them are discharged by the `Std.WP` `vcgen` pipeline.
-/

public import Kraken.X64.Semantics
public import Kraken.X64.Parser
public import Kraken.X64.OmniSemantics
public import Kraken.X64.Sep
public import Kraken.Specs
public import Kraken.Tactics
public import Kraken.X64.Registers
public import Kraken.MachineWP
public import Kraken.ProgramRun
public import Kraken.KVCGen
public import Kraken.StateWP
public import Kraken.MProp
public import Kraken.SepWP
public import Kraken.SepCancel
public import Kraken.SepSpecs
public import Kraken.SepFrameProc
import Kraken.X64.Examples.Examples
import Kraken.X64.Examples.SepWP.AluMem
import Kraken.X64.Examples.SepWP.DynamicStack
import Kraken.X64.Examples.SepWP.Move2RegsToHeap
import Kraken.X64.Examples.SepWP.PushPop
import Kraken.X64.Examples.SepWP.Sib
import Kraken.X64.Examples.SepWP.Swap
import Kraken.X64.Examples.StateWP.AluMem
