/-
Flags of a carry chain on symbolic registers. Open this file to run the
benchmark; the `#eval` reports stepping, discharge and kernel time at each size.
-/
import Cases.CarryFlags
import Driver

set_option experimental.vcgen true
set_option grind.warning false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open Lean Order Parser Meta Elab Tactic Sym Std Std.WP
open scoped Program.WP

#eval runBenchUsingTactic ``CarryFlags.Goal [``CarryFlags.prog, ``AdcChain.chain]
  `(tactic| (intros; vcgen with kfinish)) `(tactic| fail)
  [8, 16, 32]
