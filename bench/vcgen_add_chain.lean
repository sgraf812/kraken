import Cases.AddChain
import Driver
import KrakenTactics.ClearDead

set_option mvcgen.warning false
set_option grind.warning false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open Lean Order Parser Meta Elab Tactic Sym Std Internal.Do
open AddChain

/-- Fold the goal along the state chain, then decide the bitvector identity. -/
macro "fold_decide" : tactic =>
  `(tactic| (simp only [Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.setWidth_eq,
      Reg64s.get64_set64, ↓reduceIte, ← BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, *] at ⊢ <;>
    bv_decide))

macro "discharge_plain" : tactic => `(tactic| fold_decide)
macro "discharge_clear" : tactic => `(tactic| (clear_dead; fold_decide))

#eval runBenchUsingTactic ``Goal [``AddChain.chain] `(tactic| (intro k; vcgen -internalize))
  `(tactic| discharge_plain) [40, 160, 640]
#eval runBenchUsingTactic ``Goal [``AddChain.chain] `(tactic| (intro k; vcgen -internalize))
  `(tactic| discharge_clear) [40, 160, 640]
