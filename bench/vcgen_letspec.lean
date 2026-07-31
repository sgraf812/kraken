/-
Let-form vs accessor-form specs on the same add chain: stepping, discharge and
kernel time per size.

`sorry` discharge isolates the kernel cost of the stepping certificate alone;
the fold discharge adds the cost of a checked proof.
-/
import Cases
import Driver
import KrakenTactics.Fold
import KrakenTactics.FoldLet
import KrakenTactics.Discharge

set_option mvcgen.warning false
set_option grind.warning false
set_option maxRecDepth 400000
set_option maxHeartbeats 10000000

open Lean Order Parser Meta Elab Tactic Sym Std Internal.Do

#eval do IO.println "== accessor + sorry"; (← IO.getStdout).flush
#eval runBenchUsingTactic ``AddChain.Goal [``AddChain.chain]
  `(tactic| (intro k; vcgen -internalize)) `(tactic| sorry) [40, 80, 160, 320, 640]

#eval do IO.println "== let-form + sorry"; (← IO.getStdout).flush
#eval runBenchUsingTactic ``AddChainLet.Goal [``AddChainLet.chain]
  `(tactic| (intro k; vcgen -internalize)) `(tactic| sorry) [40, 80, 160, 320, 640]

#eval do IO.println "== accessor + kfold_discharge"; (← IO.getStdout).flush
#eval runBenchUsingTactic ``AddChain.Goal [``AddChain.chain]
  `(tactic| (intro k; vcgen -internalize)) `(tactic| kfold_discharge) [40, 80, 160, 320, 640]

#eval do IO.println "== let-form + kfold_let_discharge"; (← IO.getStdout).flush
#eval runBenchUsingTactic ``AddChainLet.Goal [``AddChainLet.chain]
  `(tactic| (intro k; vcgen -internalize)) `(tactic| kfold_let_discharge) [40, 80, 160, 320, 640]
