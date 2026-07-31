/-
Kraken vcgen benchmarks: stepping, discharge and kernel time per family.

One pipeline for every workload: the let-form `@[spec]` triples of
`Kraken/Specs.lean`, `vcgen -internalize simplifying_assumptions` to step the
program and normalize each state literal as it is produced, and `bv_decide` on
whatever verification condition is left.

The carry chain and the multi-register chain leave no verification condition at
all: their programs are ground, so the state-simplification pass reaches the
postcondition's value and closes the goal. The add and decrement chains carry a
symbolic start, so one bitvector identity survives to the discharge.
-/
import Cases
import Driver
import KrakenTactics.Fold

set_option mvcgen.warning false
set_option grind.warning false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open Lean Order Parser Meta Elab Tactic Sym Std Internal.Do

#eval runBenchUsingTactic ``AddChain.Goal [``AddChain.chain]
  `(tactic| (intro k; vcgen -internalize simplifying_assumptions)) `(tactic| bv_decide) [40, 160, 640]
#eval runBenchUsingTactic ``DecChain.Goal [``DecChain.chain]
  `(tactic| vcgen -internalize simplifying_assumptions) `(tactic| bv_decide) [40, 160, 640]
#eval runBenchUsingTactic ``AdcChain.Goal [``AdcChain.prog, ``AdcChain.chain]
  `(tactic| vcgen -internalize simplifying_assumptions) `(tactic| bv_decide) [40, 160, 640]
#eval runBenchUsingTactic ``MultiReg.Goal [``MultiReg.chain, ``MultiReg.round]
  `(tactic| vcgen -internalize simplifying_assumptions) `(tactic| bv_decide) [4, 10, 40]
