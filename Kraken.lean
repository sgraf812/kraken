/-
Kraken - x86_64 Assembly Interpreter

Root module. The baseline instruction semantics is a shallow monadic embedding
over `EStateM X64Exit MachineData` (`Operation.interp` in Kraken/Semantics.lean).
The spec layer runs on `X64MNew D`, a reader over the label/layout environment and
a state over `rip`, above the error-state machine over `Sys D` (the CPU state plus
a device state that a jump preserves); its per-constructor `Op.*` actions and
`@[spec]` triples (Kraken/X64MNew.lean, Kraken/DeviceNew.lean) are discharged by
the `Std.Internal.Do` weakest-precondition `vcgen` pipeline and the `easm` memory
tactic (Kraken/Tactics.lean).
-/

import Kraken.Semantics
import Kraken.Parser
import Kraken.OmniSemantics
import Kraken.Specs
import Kraken.X64MNew
import Kraken.DeviceNew
import Kraken.Tactics
