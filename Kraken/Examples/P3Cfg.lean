/-
`p3`, verified through the control-flow rule. One spec table gives the
assertion at each label, `rbx` is the variant, and `Program.cfg` produces one
obligation per basic block. Each obligation is one `vcgen` call; the loop
arithmetic lives in two `grind` lemmas keyed on the square of the invariant's
power. The old `Kraken/Examples/P3.lean` proves the same statements through
the while and resolve rules and stays as is.
-/
import Kraken.Examples.P3

open Kraken.Parser
open Std.Internal.Do
open Lean.Order

set_option mvcgen.warning false

namespace P3Cfg

/-- Squaring steps the exponent tower once. The right side is a single power,
so the rewrite cannot feed itself. -/
@[grind =] private theorem sq_pow (r b : Nat) (hb : b ≠ 0) (hle : b ≤ r) :
    2 ^ 2 ^ (r - b) * 2 ^ 2 ^ (r - b) = 2 ^ 2 ^ (r - (b - 1)) := by
  rw [← Nat.pow_add, ← Nat.mul_two, ← Nat.pow_succ]
  show 2 ^ 2 ^ (r - b + 1) = _
  rw [show r - b + 1 = r - (b - 1) from by omega]

/-- The squared invariant stays below the word size. -/
@[grind] private theorem sq_lt (r b : Nat) (hbound : 2 ^ 2 ^ r < 2 ^ 64)
    (hb : b ≠ 0) (hle : b ≤ r) :
    2 ^ 2 ^ (r - b) * 2 ^ 2 ^ (r - b) < 2 ^ 64 := by
  rw [sq_pow r b hb hle]
  calc 2 ^ 2 ^ (r - (b - 1))
      ≤ 2 ^ 2 ^ r :=
        Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
    _ < 2 ^ 64 := hbound

/-- The forward edge of the loop: `_end` sits later in the text than `start`. -/
@[grind] private theorem len_end_lt_start :
    (Program.fromLabel p3 "_end").length < (Program.fromLabel p3 "start").length := by
  decide

/-- `p3`, cut at its first cell. -/
private theorem p3_head :
    p3 = Directive.label "init" :: ((p3.entry.tail ++ p3.loop) ++ p3.exit) := rfl

/-- The spec table: the machine at each label of `p3`, for a run that started
on `d`. At `start` it is the loop invariant. -/
private abbrev p3_table (d : MachineData) : Label → MachineData → Prop
  | "init", s => s = d
  | "start", s =>
      s.regs.rdx.toNat = 2 ^ 2 ^ (d.regs.rbx.toNat - s.regs.rbx.toNat)
      ∧ s.regs.rbx.toNat ≤ d.regs.rbx.toNat ∧ s.regs.rax = 0
  | "_end", s => s.regs.rdx.toNat = 2 ^ 2 ^ d.regs.rbx.toNat ∧ s.regs.rax = 0
  | _, _ => False

/-- The three blocks of `p3`, in terms of its fragments. -/
private theorem p3_blocks_eq :
    Program.blocks p3 =
      [⟨"init", p3.entry.tail, some "start"⟩,
       ⟨"start", p3.body, some "_end"⟩,
       ⟨"_end", p3.exit.tail, none⟩] := by
  decide

private theorem mem_p3_blocks {blk : Program.Block} :
    blk ∈ Program.blocks p3 ↔
      blk = ⟨"init", p3.entry.tail, some "start"⟩
      ∨ blk = ⟨"start", p3.body, some "_end"⟩
      ∨ blk = ⟨"_end", p3.exit.tail, none⟩ := by
  simp [p3_blocks_eq]

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
        · rw [p3_table.eq_def] at hT
          split at hT <;> simp_all
  · -- one obligation per block
    intro blk hmem n
    rw [mem_p3_blocks] at hmem
    rcases hmem with rfl | rfl | rfl <;> simp only [List.tail_cons]
    · vcgen simplifying_assumptions with finish
    · vcgen simplifying_assumptions with finish
    · vcgen simplifying_assumptions with finish

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
