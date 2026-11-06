import Cases.ManyCalls
import Driver

set_option experimental.vcgen true
set_option grind.warning false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open Lean Order Parser Meta Elab Tactic Sym Std Std.WP
open scoped Program.WP

#eval runBenchUsingTactic ``ManyCalls.Goal [``ManyCalls.many, ``ManyCalls.calls]
  `(tactic| (
    intro _ _ _ _ _ _ _ _
    vcgen [ManyCalls.touch_spec]
      invariants
      · fun {s₀} l s' => match l with
          | "many" => s' = s₀
          | _ => False
      · fun _ _ => 0
      with kfinish))
  `(tactic| fail)
  [8, 16, 32]
