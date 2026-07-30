/-
Kraken vcgen benchmarks: stepping, discharge and kernel time per family.

Sizes are capped so no run exceeds ~20s. A configuration that blows that budget
is dropped from the larger sizes and marked SUPER-LINEAR, to be investigated
rather than measured:

  * `simp_all` discharge: quadratic in the chain length, since it normalizes
    every hypothesis and each walk grows with chain depth (AdcChain(640) took
    185s). Standalone reproducer: simp_all-superlinear-mwe.lean.
-/
import Cases
import Driver
import KrakenTactics.Fold
import KrakenTactics.Discharge

set_option mvcgen.warning false
set_option grind.warning false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

open Lean Order Parser Meta Elab Tactic Sym Std Internal.Do

macro "d_fold" : tactic => `(tactic| kfold_discharge)
macro "d_simp" : tactic => `(tactic| kraken_discharge)

#eval IO.println "== kfold_discharge"
#eval runBenchUsingTactic ``AddChain.Goal [``AddChain.chain]
  `(tactic| (intro k; vcgen -internalize)) `(tactic| d_fold) [40, 160, 640]
#eval runBenchUsingTactic ``DecChain.Goal [``DecChain.chain]
  `(tactic| vcgen -internalize) `(tactic| d_fold) [40, 160, 640]
#eval runBenchUsingTactic ``AdcChain.Goal [``AdcChain.prog, ``AdcChain.chain]
  `(tactic| vcgen -internalize) `(tactic| d_fold) [40, 160, 640]
#eval runBenchUsingTactic ``MultiReg.Goal [``MultiReg.chain, ``MultiReg.round]
  `(tactic| vcgen -internalize) `(tactic| d_fold) [4, 10, 40]

#eval IO.println "== kraken_discharge (simp only reference)"
#eval runBenchUsingTactic ``AddChain.Goal [``AddChain.chain]
  `(tactic| (intro k; vcgen -internalize)) `(tactic| d_simp) [40, 160, 640]
#eval runBenchUsingTactic ``DecChain.Goal [``DecChain.chain]
  `(tactic| vcgen -internalize) `(tactic| d_simp) [40, 160, 640]
#eval runBenchUsingTactic ``AdcChain.Goal [``AdcChain.prog, ``AdcChain.chain]
  `(tactic| vcgen -internalize) `(tactic| d_simp) [40, 160, 640]
#eval runBenchUsingTactic ``MultiReg.Goal [``MultiReg.chain, ``MultiReg.round]
  `(tactic| vcgen -internalize) `(tactic| d_simp) [4, 10, 40]
