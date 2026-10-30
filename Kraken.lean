module

/-
Kraken - x86_64 Assembly Interpreter

Root module. The baseline instruction semantics is `Operation.interp` in
Kraken/X64/Semantics.lean, in continuation-passing style over `Effects`.
Kraken/X64/WP/Basic.lean is the run of a program fragment in the baseline's
burst. Kraken/X64/WP/Instance.lean interprets a program by its run at predicates over
machine states. Kraken/StateCfg.lean links the runs of basic blocks into the run
of a program with jumps. The wp is discharged by the `Std.WP` `vcgen` pipeline.
-/

public import Kraken.X64.Semantics
public import Kraken.X64.Parser
public import Kraken.X64.OmniSemantics
public import Kraken.X64.Sep
public import Kraken.Specs
public import Kraken.Tactics
public import Kraken.X64.Registers
public import Kraken.X64.WP
public import Kraken.KVCGen
public import Kraken.X64.WP.Instance
public import Kraken.StateCfg
import Kraken.X64.Examples.Examples
import Kraken.X64.Examples.WP.AluMem
import Kraken.X64.Examples.WP.Basic
import Kraken.X64.Examples.WP.P3
import Kraken.X64.Examples.WP.CallSwap
import Kraken.X64.Examples.WP.Memmove
import Kraken.X64.Examples.WP.Jumps
import Kraken.X64.Examples.WP.Surprises
import Kraken.X64.Examples.WP.EventuallySurprises
import Kraken.X64.Examples.WP.PushPopLoop
import Kraken.X64.Examples.WP.EvenOdd
import Kraken.X64.Examples.WP.LoadStore
import Kraken.X64.Examples.WP.FfScalarproductFloatFma3
import Kraken.X64.Examples.WP.ManyCalls
