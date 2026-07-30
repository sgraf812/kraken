/-
The discharge simp set for kraken verification conditions.

`kraken_simp` folds a verification condition emitted by accessor-style
stepping: it rewrites the goal by the state-component equations and reduces
what an instruction leaves behind. It rewrites the goal only; `simp_all`
normalizes every hypothesis against every other, which is quadratic in the
chain length (see simp_all-superlinear-mwe.lean).

The set covers four jobs:

* literal normalization, so an instruction's immediate reaches the form the
  arithmetic simprocs recognize;
* register read-over-write, resolving a read against the writes before it;
* flag reduction, collapsing a carry whose operands agree;
* the arithmetic reduce simprocs, which `simp only` does not run unless they
  are named, and without which constants never collapse and the chain stays
  as deep as the program is long.
-/
import Kraken.AccessorSpecs
import Std.Tactic.BVDecide

/-- Fold a verification condition along the state chain. -/
macro "kraken_simp" : tactic =>
  `(tactic| simp only [Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.setWidth_eq,
      Reg64s.get64_set64, ↓reduceIte,
      BitVec.add_zero, reduceCtorEq, BitVec.unsigned_eq, BitVec.toNat_ofNat,
      Nat.reducePow, Nat.zero_mod, Int.cast_ofNat_Int, Int.add_zero,
      bne_self_eq_false, Bool.toNat_false,
      BitVec.reduceAdd, Nat.reduceMod, Int.reduceAdd, Nat.reduceMul, *] at ⊢)

/-- Fold a verification condition and decide the residual bitvector goal. -/
macro "kraken_discharge" : tactic => `(tactic| (kraken_simp <;> bv_decide))
