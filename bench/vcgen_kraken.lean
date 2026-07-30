/-
Kraken vcgen benchmarks: stepping, discharge and kernel time per family.
-/
import Cases
import Driver
import KrakenTactics.ClearDead

set_option mvcgen.warning false
set_option grind.warning false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

open Lean Order Parser Meta Elab Tactic Sym Std Internal.Do

/-- Fold the goal along the state chain, then decide the bitvector identity. -/
macro "fold_decide" : tactic =>
  `(tactic| (simp only [Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.setWidth_eq,
      Reg64s.get64_set64, ↓reduceIte, ← BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, *] at ⊢ <;>
    bv_decide))

macro "d_plain" : tactic => `(tactic| fold_decide)
macro "d_clear" : tactic => `(tactic| (clear_dead; fold_decide))
macro "d_simpall" : tactic => `(tactic| (simp_all <;> bv_decide))

#eval IO.println "-- AddChain (symbolic start), discharge: fold_decide"
#eval runBenchUsingTactic ``AddChain.Goal [``AddChain.chain]
  `(tactic| (intro k; vcgen -internalize)) `(tactic| d_plain) [40, 160, 640]
#eval IO.println "-- AddChain, discharge: clear_dead + fold_decide"
#eval runBenchUsingTactic ``AddChain.Goal [``AddChain.chain]
  `(tactic| (intro k; vcgen -internalize)) `(tactic| d_clear) [40, 160, 640]

#eval IO.println "-- DecChain (ground), discharge: fold_decide"
#eval runBenchUsingTactic ``DecChain.Goal [``DecChain.chain]
  `(tactic| vcgen -internalize) `(tactic| d_plain) [40, 160, 640]

#eval IO.println "-- AdcChain (live carries), discharge: simp_all"
#eval runBenchUsingTactic ``AdcChain.Goal [``AdcChain.prog, ``AdcChain.chain]
  `(tactic| vcgen -internalize) `(tactic| d_simpall) [40, 160, 640]

#eval IO.println "-- MultiReg (15 queried registers), discharge: simp_all"
#eval runBenchUsingTactic ``MultiReg.Goal [``MultiReg.chain, ``MultiReg.round]
  `(tactic| vcgen -internalize) `(tactic| d_simpall) [4, 10, 40]
