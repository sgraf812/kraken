/-
Kraken - x86_64 Assembly Interpreter

Root module. The baseline instruction semantics is `Operation.interp` in
Kraken/Semantics.lean, in continuation-passing style over `Effects`.
Kraken/X64M.lean re-encodes it as the straightline interpreter
`Operation.interpM` over `MachineM` (error-state on `MachineData`), and builds
the spec monad `X64M D` on top: a reader over the label/layout environment and
a state over `rip`, above the error-state machine over `Sys D` (the CPU state
plus a device state that a jump preserves). The per-constructor `Op.*` actions
and `@[spec]` triples (Kraken/X64M.lean, Kraken/Device.lean) are discharged by
the `Std.Internal.Do` weakest-precondition `vcgen` pipeline and the `easm`
memory tactic (Kraken/Tactics.lean).
-/

import Kraken.Semantics
import Kraken.Parser
import Kraken.OmniSemantics
import Kraken.Specs
import Kraken.X64M
import Kraken.Device
import Kraken.Tactics
