module

/-
The squaring loop `p3` in the state wp: starting from `rdx = 2`, each
iteration squares `rdx` by `mulx` and counts `rbx` down to zero, so the loop
computes `rdx = 2 ^ 2 ^ rbx`. The proposition is the baseline's
`p3_correct` with two more hypotheses: `rax` starts at zero, which the
statement needs when the loop does not run, and the layout is valid, which
places the loop's labels. `p3_table` gives the assertion at each label,
`rbx` is the variant, and `StateWP.cfg` leaves one `kvcgen64` obligation per
block.
-/
public import Kraken.StateCfg
import Kraken.X64.Examples.Examples

open Std.WP
open Lean.Order
open scoped StateWP

set_option experimental.vcgen true

namespace State

/-- Squaring steps the exponent tower once. -/
@[grind =] private theorem sq_pow (r b : Nat) (hb : b ≠ 0) (hle : b ≤ r) :
    2 ^ 2 ^ (r - b) * 2 ^ 2 ^ (r - b) = 2 ^ 2 ^ (r - (b - 1)) := by
  rw [← Nat.pow_add, ← Nat.mul_two, ← Nat.pow_succ]
  show 2 ^ 2 ^ (r - b + 1) = _
  rw [show r - b + 1 = r - (b - 1) from by omega]

/-- The squared invariant stays below the word size. -/
@[grind .] private theorem sq_lt (r b : Nat) (hbound : 2 ^ 2 ^ r < 2 ^ 64)
    (hb : b ≠ 0) (hle : b ≤ r) :
    2 ^ 2 ^ (r - b) * 2 ^ 2 ^ (r - b) < 2 ^ 64 := by
  rw [sq_pow r b hb hle]
  calc 2 ^ 2 ^ (r - (b - 1))
      ≤ 2 ^ 2 ^ r :=
        Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
    _ < 2 ^ 64 := hbound

/-- The forward edge of the loop: `_end` sits later in the text than `start`. -/
@[grind .] private theorem idx_start_lt_end :
    Program.blockIdx p3 "start" < Program.blockIdx p3 "_end" := by
  decide

/-- The jump targets of `p3` are mapped. -/
@[grind .] private theorem p3_start_isSome : (Program.blockAt p3 "start").isSome := by decide
@[grind .] private theorem p3_end_isSome : (Program.blockAt p3 "_end").isSome := by decide

/-- The machine at each label of `p3`, for a run that started on `d`. At
`start` it is the loop invariant. -/
private abbrev p3_table (d : MachineData) : Label → MachineData → Prop
  | "init", s => s = d
  | "start", s =>
      s.regs.rdx.toNat = 2 ^ 2 ^ (d.regs.rbx.toNat - s.regs.rbx.toNat)
      ∧ s.regs.rbx.toNat ≤ d.regs.rbx.toNat ∧ s.regs.rax = 0
  | "_end", s => s.regs.rdx.toNat = 2 ^ 2 ^ d.regs.rbx.toNat ∧ s.regs.rax = 0
  | _, _ => False

/-- The baseline's `p3_correct`, for a start state with `rax = 0` and a valid
layout. -/
theorem p3_correct [layout : Layout] [Kraken.Executable.ValidExecutable (layout p3)]
    (d : MachineData) (h_bounds : p3_spec d < 2 ^ 64) (h_rax : d.regs.rax = 0) :
    Eventually (straightlineStep (layout p3))
      (fun s => s.1.regs.rdx.toNat = p3_spec d ∧ s.1.regs.rax = 0) (d, layout.start) := by
  simp only [p3_spec] at h_bounds ⊢
  apply eventually_straightlineStep_of_wp
  intro _
  refine StateWP.cfg_wp (p3_table d) (fun _ s => s.regs.rbx.toNat) _ ⊥ ?_ d rfl
  cfg_cases [p3]
  all_goals kvcgen64 with finish

end State
