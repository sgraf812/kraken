/-
Kraken - x86_64 Assembly Interpreter

Root module. On the `estatem` experiment branch the instruction semantics is a
shallow monadic embedding over `EStateM X64Exit MachineData` (see
Kraken/Semantics.lean); the proof layer is the `Std.Internal.Do` weakest
precondition / `vcgen` pipeline (Kraken/OmniSemantics.lean, Kraken/AccessorSpecs.lean).
-/

import Kraken.Semantics
import Kraken.Parser
import Kraken.OmniSemantics
import Kraken.AccessorSpecs
import Kraken.Tactics
