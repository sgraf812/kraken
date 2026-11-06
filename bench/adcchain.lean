/-
Carry chain through the deep embedding. Open this file to run the benchmark;
the `#eval` reports stepping, discharge and kernel time at each size.
-/
import Cases.AdcChain
import Driver

set_option experimental.vcgen true
set_option grind.warning false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open Lean Order Parser Meta Elab Tactic Sym Std Std.WP
open scoped Program.WP

#eval runBenchUsingTactic ``AdcChain.Goal [``AdcChain.prog, ``AdcChain.chain]
  `(tactic| (intros; vcgen)) `(tactic| fail)
  [40, 160, 640]
