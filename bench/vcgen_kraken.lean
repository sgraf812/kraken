/-
Kraken vcgen benchmarks: stepping, discharge and kernel time per family.

Sizes are capped so that no run exceeds ~20s. A configuration that blows that
budget is dropped from the larger sizes and marked SUPER-LINEAR here, to be
investigated rather than measured:

  * `simp_all` discharge: quadratic in the chain length, since it normalizes
    every hypothesis and each walk grows with chain depth (AdcChain(640) took
    185s). Kept only at small sizes as a reference point; `kraken_discharge`
    rewrites the goal only. Standalone reproducer:
    simp_all-superlinear-mwe.lean.
-/
import Cases
import Driver
import KrakenTactics.ClearDead
import KrakenTactics.Discharge

set_option mvcgen.warning false
set_option grind.warning false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

open Lean Order Parser Meta Elab Tactic Sym Std Internal.Do

macro "d_k" : tactic => `(tactic| kraken_discharge)
macro "d_kclear" : tactic => `(tactic| (clear_dead; kraken_discharge))
macro "d_simpall" : tactic => `(tactic| (simp_all <;> bv_decide))

#eval IO.println "-- AddChain (symbolic start)"
#eval runBenchUsingTactic ``AddChain.Goal [``AddChain.chain]
  `(tactic| (intro k; vcgen -internalize)) `(tactic| d_k) [40, 160, 640]
#eval IO.println "-- AddChain + clear_dead"
#eval runBenchUsingTactic ``AddChain.Goal [``AddChain.chain]
  `(tactic| (intro k; vcgen -internalize)) `(tactic| d_kclear) [40, 160, 640]
#eval IO.println "-- DecChain (ground)"
#eval runBenchUsingTactic ``DecChain.Goal [``DecChain.chain]
  `(tactic| vcgen -internalize) `(tactic| d_k) [40, 160, 640]
#eval IO.println "-- AdcChain (live carries)"
#eval runBenchUsingTactic ``AdcChain.Goal [``AdcChain.prog, ``AdcChain.chain]
  `(tactic| vcgen -internalize) `(tactic| d_k) [40, 160, 640]
#eval IO.println "-- AdcChain, simp_all reference (SUPER-LINEAR, small sizes only)"
#eval runBenchUsingTactic ``AdcChain.Goal [``AdcChain.prog, ``AdcChain.chain]
  `(tactic| vcgen -internalize) `(tactic| d_simpall) [40, 160]
#eval IO.println "-- MultiReg (15 queried registers)"
#eval runBenchUsingTactic ``MultiReg.Goal [``MultiReg.chain, ``MultiReg.round]
  `(tactic| vcgen -internalize) `(tactic| d_k) [4, 10, 40]
