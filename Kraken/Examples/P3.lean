/-
The squaring loop `p3`: starting from `rdx = 2`, each iteration squares `rdx`
by `mulx` and counts `rbx` down to zero, so the loop computes
`rdx = 2 ^ 2 ^ rbx`. `p3_correct` is one `Triple` of the run wp on `Program`:
the fall-through postcondition holds when the run falls off the end of the
text, and the label context is `False` because the run never pauses.

The walk is one `vcgen` call (`p3_full_spec`): the prologue establishes the
invariant, and `Program.while_spec` steps the loop at its header with the
invariant `rdx = 2 ^ 2 ^ (rbx₀ - rbx)` and the variant `rbx`. The loop body is
one traversal (`p3_body_spec`), whose forward exit pauses at `_end`;
`Program.resolve` discharges that pause against the tail (`p3_exit_spec`).
`Program.sound` reads the triple back as the baseline judgment
(`p3_correct_run`), fed by the extraction facts `p3_hlab`.
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

/-- The split at the loop header. -/
private theorem p3_eq_entry_append : p3 = p3.entry ++ (p3.loop ++ p3.exit) := by simp [p3]

/-- The split at the exit label. -/
private theorem p3_eq_loop_append : p3 = (p3.entry ++ p3.loop) ++ p3.exit := by simp [p3]

/-- What a run of `p3` computes from the machine it starts on. -/
def p3_spec (d : MachineData) : Nat := 2 ^ 2 ^ d.regs.rbx.toNat

/-- One squaring step of the exponent tower. -/
private theorem pow_sq (e : Nat) : 2 ^ 2 ^ e * 2 ^ 2 ^ e = 2 ^ 2 ^ (e + 1) := by
  rw [← Nat.pow_add, Nat.pow_succ, Nat.mul_two]

/-! ## Segment extraction

One fact per label: the segment at the label's address is the label's scope
suffix, laid out at its position. `Program.sound` consumes these through
`p3_hlab`. -/

section Extraction

attribute [local simp] p3 Layout.apply_fst Layout.apply_snd

variable [layout : Layout]

/-- From the start of the text the run traverses the whole program. -/
theorem p3_entry_segment :
    (layout p3).directivesFromAddress layout.start = Layout.frag 0 p3 := by
  have h := Executable.directivesFromAddress_addrOf (layout p3) 0 (Nat.zero_le _)
    (fun k hk => absurd hk (Nat.not_lt_zero k))
  rw [← Layout.apply_snd]
  simpa using h

variable [hv : Executable.ValidLayout (layout p3)]

theorem p3_init_addr :
    (layout p3).labels.label "init" = (layout p3).addrOf 0 := by
  have h0 : (layout p3).2[0]? = some (.label "init", layout.size 0) := by
    simp
  with_reducible apply Executable.label_addrOf
  · rw [h0, hv.label_size _ "init" _ h0]
  · simp

theorem p3_start_addr :
    (layout p3).labels.label "start" = (layout p3).addrOf p3.entry.length := by
  have h2 : (layout p3).2[p3.entry.length]? = some (.label "start", layout.size p3.entry.length) := by
    simp
  with_reducible apply Executable.label_addrOf
  · rw [h2, hv.label_size _ "start" _ h2]
  · simp

theorem p3_start_segment :
    (layout p3).directivesFromAddress ((layout p3).labels.label "start")
      = Layout.frag p3.entry.length (p3.loop ++ p3.exit) := by
  rw [p3_start_addr, Executable.directivesFromAddress_addrOf]
  · rw [p3_eq_entry_append]
    with_reducible exact Layout.apply_drop p3.entry (p3.loop ++ p3.exit)
  · simp
  · intro k hk
    with_reducible apply Executable.addrOf_ne_of_valid (layout p3) hk <;>
      simp

theorem p3_end_addr :
    (layout p3).labels.label "_end" = (layout p3).addrOf (p3.entry ++ p3.loop).length := by
  have h8 : (layout p3).2[(p3.entry ++ p3.loop).length]?
      = some (.label "_end", layout.size (p3.entry ++ p3.loop).length) := by
    simp
  with_reducible apply Executable.label_addrOf
  · rw [h8, hv.label_size _ "_end" _ h8]
  · simp

theorem p3_end_segment :
    (layout p3).directivesFromAddress ((layout p3).labels.label "_end")
      = Layout.frag (p3.entry ++ p3.loop).length p3.exit := by
  rw [p3_end_addr, Executable.directivesFromAddress_addrOf]
  · rw [p3_eq_loop_append]
    with_reducible exact Layout.apply_drop (p3.entry ++ p3.loop) p3.exit
  · simp
  · intro k hk
    with_reducible apply Executable.addrOf_ne_of_valid (layout p3) hk <;>
      simp

/-- The extraction facts, keyed the way `Program.sound` consumes them: every
label with a scope suffix sits in the text, and the segment at its address is
that suffix, laid out at its position. -/
theorem p3_hlab : ∀ l, Program.fromLabel p3 l ≠ [] →
    (layout p3).directivesFromAddress ((layout p3).labels.label l)
      = Layout.frag (p3.length - (Program.fromLabel p3 l).length) (Program.fromLabel p3 l) := by
  intro l hl
  have hmem := Program.fromLabel_mem hl
  simp only [p3, p3.entry, p3.loop, p3.exit, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, Directive.label.injEq, reduceCtorEq] at hmem
  rcases hmem with (h | h) | h <;> subst h
  · rw [show Program.fromLabel p3 "init" = p3 by decide,
      show p3.length - p3.length = 0 from Nat.sub_self _,
      p3_init_addr, Executable.addrOf_zero, Layout.apply_fst]
    exact p3_entry_segment
  · rw [show Program.fromLabel p3 "start" = p3.loop ++ p3.exit by decide,
      show p3.length - (p3.loop ++ p3.exit).length = p3.entry.length by decide]
    exact p3_start_segment
  · rw [show Program.fromLabel p3 "_end" = p3.exit by decide,
      show p3.length - p3.exit.length = (p3.entry ++ p3.loop).length by decide]
    exact p3_end_segment

end Extraction

/-! ## The proof -/

section Proof

/-- The loop invariant at the header: `rdx` holds the `rbx₀ - rbx`-fold
squaring, and `rbx` is the variant. -/
private abbrev p3_inv (rbx0 : Nat) (s : MachineData) : Prop :=
  s.regs.rdx.toNat = 2 ^ 2 ^ (rbx0 - s.regs.rbx.toNat)
  ∧ s.regs.rbx.toNat ≤ rbx0 ∧ s.regs.rax = 0

/-- The loop body, traversed once with `rbx = n`: the countdown either reaches
zero and exits at `_end` with the answer, or one squaring runs and the back
jump exits at `start` with the invariant kept and the variant decreased. -/
private theorem p3_body_spec (rbx0 : Nat) (hbound : 2 ^ 2 ^ rbx0 < 2 ^ 64) (n : Nat) :
    ⦃ fun s => p3_inv rbx0 s ∧ s.regs.rbx.toNat = n ⦄
      (p3.body ++ p3.exit)
    ⦃ fun _ s => s.regs.rdx.toNat = 2 ^ 2 ^ rbx0 ∧ s.regs.rax = 0;
      fun l s => if l = "start" then p3_inv rbx0 s ∧ s.regs.rbx.toNat < n
                 else l = "_end" ∧ s.regs.rdx.toNat = 2 ^ 2 ^ rbx0 ∧ s.regs.rax = 0 ⦄ := by
  have hsq : ∀ m : Nat, m = 2 ^ 2 ^ (rbx0 - n) → n ≤ rbx0 → n ≠ 0 →
      m * m < 2 ^ 64 ∧ m * m = 2 ^ 2 ^ (rbx0 - (n - 1)) := by
    intro m hm hle hb
    subst hm
    rw [pow_sq, show rbx0 - (n - 1) = rbx0 - n + 1 from by omega]
    refine ⟨?_, rfl⟩
    calc 2 ^ 2 ^ (rbx0 - n + 1)
        ≤ 2 ^ 2 ^ rbx0 :=
          Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
      _ < 2 ^ 64 := hbound
  vcgen simplifying_assumptions with finish

/-- The tail: the label and the `nop` leave the machine unchanged, and the run
falls off the end of the text. -/
private theorem p3_exit_spec (rbx0 : Nat) :
    ⦃ fun s => s.regs.rdx.toNat = 2 ^ 2 ^ rbx0 ∧ s.regs.rax = 0 ⦄
      p3.exit
    ⦃ fun _ s => s.regs.rdx.toNat = 2 ^ 2 ^ rbx0 ∧ s.regs.rax = 0;
      fun _ _ => False ⦄ := by
  vcgen simplifying_assumptions with finish

/-- A run of `p3` from a machine whose `rax` is clear falls off the end of the
text with `rdx = 2 ^ 2 ^ rbx` and `rax` clear again: walk the text once, with
the while rule at `start`, then resolve the pause at `_end` against the tail. -/
theorem p3_correct (d : MachineData) (h_bounds : p3_spec d < 2 ^ 64)
    (h_rax : d.regs.rax = 0) :
    ⦃ fun s => s = d ⦄
      p3
    ⦃ fun _ s => s.regs.rdx.toNat = p3_spec d ∧ s.regs.rax = 0;
      fun _ _ => False ⦄ := by
  simp only [p3_spec] at h_bounds ⊢
  have hwhile := Program.while_spec "start" (p3_inv d.regs.rbx.toNat)
    (fun s => s.regs.rbx.toNat) (by decide) (p3_body_spec d.regs.rbx.toNat h_bounds)
  refine Program.triple_conseq
    (Program.resolve (J := fun l s =>
        l = "_end" ∧ s.regs.rdx.toNat = 2 ^ 2 ^ d.regs.rbx.toNat ∧ s.regs.rax = 0)
      ?_ ?_)
    (fun _ h => h) (fun l s h => absurd (h.2.1 ▸ h.1) (by decide))
  · vcgen [hwhile] simplifying_assumptions with finish
  · intro l hmem
    by_cases h2 : l = "_end"
    · subst h2
      rw [show Program.fromLabel p3 "_end" = p3.exit by decide]
      exact Program.triple_conseq (p3_exit_spec d.regs.rbx.toNat)
        (fun s hJ => hJ.2) (fun _ _ h => False.elim h)
    · exact Program.triple_conseq Program.triple_false
        (fun s hJ => (h2 hJ.1).elim) (fun _ _ h => False.elim h)

variable [layout : Layout] [hv : Executable.ValidLayout (layout p3)]

/-- `p3_correct`, read at the machine: the omni-semantics judgment of
`Kraken.OmniSemantics` that a run of the laid-out program from
`(d, layout.start)` reaches a state with `rdx = 2 ^ 2 ^ rbx` and `rax` clear.
The exit disjunct drops out because the triple's label context is `False`. -/
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

end Proof
