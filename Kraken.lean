/-
Kraken - x86_64 Assembly Interpreter

Root module. The baseline instruction semantics is `Operation.interp` in
Kraken/X64/Semantics.lean, in continuation-passing style over `Effects`.
Kraken/X64M.lean re-encodes it as the straightline interpreter
`Operation.interpM` over `MachineM` (error-state on `MachineData`), and builds
the spec monad `X64M D` on top: a reader over the label/layout environment and
a state over `rip`, above the error-state machine over `Sys D` (the CPU state
plus a device state that a jump preserves). The per-constructor `Op.*` actions
and `@[spec]` triples (Kraken/X64M.lean, Kraken/Device.lean) are discharged by
the `Std.WP` weakest-precondition `vcgen` pipeline and the `easm` memory
tactic (Kraken/Easm.lean). Kraken/MachineWP.lean is the machine-founded
weakest precondition on the deep embedding.
-/

import Kraken.X64.Semantics
import Kraken.X64.Parser
import Kraken.X64.OmniSemantics
import Kraken.X64.Sep
import Kraken.Specs
import Kraken.X64M
import Kraken.Device
import Kraken.Tactics
import Kraken.Easm
import Kraken.MachineWP
import Kraken.SepWP
import Kraken.SepSpecs
