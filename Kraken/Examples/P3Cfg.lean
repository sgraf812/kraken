/-
`p3`, verified through the control-flow rule. One spec table gives the
assertion at each label, `rbx` is the variant, and `Program.cfg` produces one
obligation per basic block. Each obligation is one `vcgen` call. The old
`Kraken/Examples/P3.lean` proves the same statements through the while and
resolve rules and stays as is.
-/
import Kraken.Examples.P3

open Kraken.Parser
open Std.Internal.Do
open Lean.Order

set_option mvcgen.warning false

namespace P3Cfg

/-- One squaring step of the exponent tower. -/
private theorem pow_sq (e : Nat) : 2 ^ 2 ^ e * 2 ^ 2 ^ e = 2 ^ 2 ^ (e + 1) := by
  rw [← Nat.pow_add, Nat.pow_succ, Nat.mul_two]

/-- `p3`, cut at its first cell. -/
private theorem p3_head :
    p3 = Directive.label "init" :: ((p3.entry.tail ++ p3.loop) ++ p3.exit) := rfl

/-- The spec table: the machine at each label of `p3`, for a run that started
on `d`. At `start` it is the loop invariant. -/
private abbrev p3_table (d : MachineData) (l : Label) (s : MachineData) : Prop :=
  if l = "init" then s = d
  else if l = "start" then
    s.regs.rdx.toNat = 2 ^ 2 ^ (d.regs.rbx.toNat - s.regs.rbx.toNat)
    ∧ s.regs.rbx.toNat ≤ d.regs.rbx.toNat ∧ s.regs.rax = 0
  else if l = "_end" then
    s.regs.rdx.toNat = 2 ^ 2 ^ d.regs.rbx.toNat ∧ s.regs.rax = 0
  else False

theorem p3_correct (d : MachineData) (h_bounds : p3_spec d < 2 ^ 64)
    (h_rax : d.regs.rax = 0) :
    ⦃ fun s => s = d ⦄
      p3
    ⦃ fun _ s => s.regs.rdx.toNat = p3_spec d ∧ s.regs.rax = 0;
      fun _ _ => False ⦄ := by
  simp only [p3_spec] at h_bounds ⊢
  refine Program.cfg "init" p3_head (p3_table d) (fun _ s => s.regs.rbx.toNat)
    (by decide) ?_ ?_
  · -- the table lives on the text
    intro l s hT
    by_cases h1 : l = "init"
    · subst h1; decide
    · by_cases h2 : l = "start"
      · subst h2; decide
      · by_cases h3 : l = "_end"
        · subst h3; decide
        · rw [p3_table, if_neg h1, if_neg h2, if_neg h3] at hT
          exact hT.elim
  · -- one obligation per block
    intro lbn hmem n
    simp only [p3, p3.entry, p3.loop, p3.body, p3.exit,
      List.cons_append, List.nil_append,
      Program.blocks, Program.blockBody, Program.nextLabel,
      List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl <;> dsimp only
    · -- init: establish the invariant
      vcgen simplifying_assumptions with finish
    · -- start: the loop body
      have hsq : ∀ m : Nat, m = 2 ^ 2 ^ (d.regs.rbx.toNat - n) → n ≤ d.regs.rbx.toNat →
          n ≠ 0 → m * m < 2 ^ 64 ∧ m * m = 2 ^ 2 ^ (d.regs.rbx.toNat - (n - 1)) := by
        intro m hm hle hb
        subst hm
        rw [pow_sq, show d.regs.rbx.toNat - (n - 1) = d.regs.rbx.toNat - n + 1 from by omega]
        refine ⟨?_, rfl⟩
        calc 2 ^ 2 ^ (d.regs.rbx.toNat - n + 1)
            ≤ 2 ^ 2 ^ d.regs.rbx.toNat :=
              Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
          _ < 2 ^ 64 := h_bounds
      have hlen : (Program.fromLabel p3 "_end").length
          < (Program.fromLabel p3 "start").length := by decide
      vcgen simplifying_assumptions with finish
    · -- _end: carry the answer off the text
      vcgen simplifying_assumptions with finish

variable [layout : Layout] [hv : Executable.ValidLayout (layout p3)]

/-- `p3_correct`, read at the machine as the baseline judgment. -/
theorem p3_correct_run (d : MachineData) (h_bounds : p3_spec d < 2 ^ 64)
    (h_rax : d.regs.rax = 0) :
    Eventually (straightlineStep (layout p3))
      (fun s => s.1.regs.rdx.toNat = p3_spec d ∧ s.1.regs.rax = 0)
      (d, layout.start) := by
  have h := (p3_correct d h_bounds h_rax).le_wp d rfl
  refine (Program.sound p3_entry_segment p3_hlab h).mono (fun _ _ h => h) ?_
  rintro mid (hq | ⟨l, -, hf⟩)
  · exact hq
  · exact hf.elim

end P3Cfg
