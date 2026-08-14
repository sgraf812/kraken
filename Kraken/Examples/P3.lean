/-
The squaring loop `p3`: starting from `rdx = 2`, each iteration squares `rdx`
by `mulx` and counts `rbx` down to zero, so the loop computes
`rdx = 2 ^ 2 ^ rbx`. `p3_correct` is one `Triple` of the run wp on `Program`,
proved through the control-flow rule: `p3_table` gives the assertion at each
label, `rbx` is the variant, and `Program.cfg` with `cfg_cases` produces one
`vcgen` obligation per basic block. The loop arithmetic lives in two `grind`
lemmas keyed on the square of the invariant's power. `Program.sound` reads the
triple back as the baseline judgment (`p3_correct_run`).
-/
import Kraken.Parser
import Kraken.SegmentExtract
import Kraken.SegmentWP
import Kraken.SegmentWPSound

open Kraken.Parser
open Std.Internal.Do
open Lean.Order

set_option mvcgen.warning false

/-- The prologue: it sets the base `rdx` holds on entry to the loop. -/
abbrev p3.entry : Program := parse("
init:
  mov $2, %rdx
")

/-- The loop body: it squares `rdx` and counts `rbx` down, jumping to `_end`
at zero and back to `start` otherwise. -/
abbrev p3.body : Program := parse("
  sub $0, %rbx
  jz _end
  mulx %rdx, %rdx, %rax
  sub $1, %rbx
  jmp start
")

/-- The loop: its header label, then the body. -/
abbrev p3.loop : Program := Directive.label "start" :: p3.body

/-- The tail the loop exits to. -/
abbrev p3.exit : Program := parse("
_end:
  nop
")

/-- The program a run of `p3` executes: the prologue, the loop, the tail. -/
def p3 : Program := p3.entry ++ p3.loop ++ p3.exit

/-- `p3`, opened for the walk. -/
@[spec] private theorem p3_def_spec {Q : Unit → MachineData → Prop}
    {E : Label → MachineData → Prop} :
    ⦃ fun s => wp (p3.entry ++ p3.loop ++ p3.exit) Q E s ⦄ p3 ⦃ Q; E ⦄ :=
  Triple.intro fun _ h => h

/-- What a run of `p3` computes from the machine it starts on. -/
def p3_spec (d : MachineData) : Nat := 2 ^ 2 ^ d.regs.rbx.toNat

/-! ## The proof -/

/-- Squaring steps the exponent tower once. The right side is a single power,
so the rewrite cannot feed itself. -/
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
@[grind .] private theorem len_end_lt_start :
    (Program.fromLabel p3 "_end").length < (Program.fromLabel p3 "start").length := by
  decide

/-- The jump targets of `p3` are mapped. -/
@[grind .] private theorem p3_start_isSome : (Program.blockAt p3 "start").isSome := by decide
@[grind .] private theorem p3_end_isSome : (Program.blockAt p3 "_end").isSome := by decide

/-- The spec table: the machine at each label of `p3`, for a run that started
on `d`. At `start` it is the loop invariant. -/
private abbrev p3_table (d : MachineData) : Label → MachineData → Prop
  | "init", s => s = d
  | "start", s =>
      s.regs.rdx.toNat = 2 ^ 2 ^ (d.regs.rbx.toNat - s.regs.rbx.toNat)
      ∧ s.regs.rbx.toNat ≤ d.regs.rbx.toNat ∧ s.regs.rax = 0
  | "_end", s => s.regs.rdx.toNat = 2 ^ 2 ^ d.regs.rbx.toNat ∧ s.regs.rax = 0
  | _, _ => False

theorem p3_correct (d : MachineData) (h_bounds : p3_spec d < 2 ^ 64)
    (h_rax : d.regs.rax = 0) :
    ⦃ fun s => s = d ⦄
      p3
    ⦃ fun _ s => s.regs.rdx.toNat = p3_spec d ∧ s.regs.rax = 0 ⦄ := by
  simp only [p3_spec] at h_bounds ⊢
  apply Program.cfg (p3_table d) (fun _ s => s.regs.rbx.toNat)
  cfg_cases [p3, p3.entry, p3.loop, p3.body, p3.exit]
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
  refine (Program.sound h).mono (fun _ _ h => h) ?_
  rintro mid (hq | ⟨l, -, hf⟩)
  · exact hq
  · exact Program.bot_elim hf

