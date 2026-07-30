/-
Acceptance test for a custom fold tactic: same goals, same stepping, only the
discharge differs.

`kraken_discharge` hands `simp only` all n state equations as rewrite rules, so
rule matching is linear in the chain length at every rewrite step. The custom
tactic should walk the chain once in dependency order instead, and the
discharge column should stop growing super-linearly.
-/
import Cases
import Driver
import KrakenTactics.Discharge

set_option mvcgen.warning false
set_option grind.warning false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

open Lean Order Parser Meta Elab Tactic Sym Std Internal.Do

macro "d_simp" : tactic => `(tactic| kraken_discharge)

#eval IO.println "-- baseline: kraken_discharge (simp only with n hypothesis rules)"
#eval runBenchUsingTactic ``AddChain.Goal [``AddChain.chain]
  `(tactic| (intro k; vcgen -internalize)) `(tactic| d_simp) [40, 160, 640]
#eval runBenchUsingTactic ``DecChain.Goal [``DecChain.chain]
  `(tactic| vcgen -internalize) `(tactic| d_simp) [40, 160, 640]
#eval runBenchUsingTactic ``AdcChain.Goal [``AdcChain.prog, ``AdcChain.chain]
  `(tactic| vcgen -internalize) `(tactic| d_simp) [40, 160, 640]
