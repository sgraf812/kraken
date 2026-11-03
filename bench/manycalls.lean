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
    refine Program.Triple.cfg
      (fun s₀ => fun
        | "many", s' => s' = s₀
        | _, _ => False)
      (fun _ _ _ => 0) fun s₀ ⟨h₀, _⟩ => ?_
    cfg_cases
    all_goals vcgen [ManyCalls.touch_spec] with kfinish))
  `(tactic| fail)
  [8, 16, 32]
