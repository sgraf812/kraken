/-
The squaring loop `p3`: starting from `rdx = 2`, each iteration squares `rdx`
by `mulx` and counts `rbx` down to zero, so the loop computes
`rdx = 2 ^ 2 ^ rbx`. `p3_correct` proves it as one `Triple` of the run wp on
`Program`: the fall-through postcondition holds when the run falls off the end
of the text, and the exceptional postcondition is `False` because the run
never leaves the text.

`vcgen` walks the program through the `Program` specs. The label cells `init`
and `_end` are skipped; the label cell `start` is stepped with
`Program.label_loop_spec` and the measure-indexed invariant
`rbx = k ∧ rdx = 2 ^ 2 ^ (rbx₀ - k)`, whose body obligation is
`p3_body_spec`, the one traversal of the loop. `Program.sound` reads the
triple back as the baseline judgment (`p3_correct_run`), fed by the
extraction lemmas of the three labels.
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

/-- The loop: it squares `rdx` and counts `rbx` down, jumping to `_end` at zero. -/
abbrev p3.loop : Program := parse("
start:
  sub $0, %rbx
  jz _end
  mulx %rdx, %rdx, %rax
  sub $1, %rbx
  jmp start
")

/-- The tail the loop exits to. -/
abbrev p3.exit : Program := parse("
_end:
  nop
")

/-- The program a run of `p3` executes: the prologue, the loop, the tail. -/
def p3 : Program := p3.entry ++ p3.loop ++ p3.exit

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

/-- The loop invariant at the header, indexed by the remaining iteration
count `k`: `rbx` holds `k` and `rdx` holds the `rbx₀ - k`-fold squaring. -/
private abbrev p3_inv (rbx0 k : Nat) (s : MachineData) : Prop :=
  s.regs.rbx.toNat = k ∧ k ≤ rbx0 ∧ s.regs.rdx.toNat = 2 ^ 2 ^ (rbx0 - k) ∧ s.regs.rax = 0

/-- The cells of the loop body and the tail, named so the dispatch specs and
the walked text unify at reducible transparency. -/
private abbrev c_sub0 : Directive :=
  .instr (.regular .W64 .W64 (.sub (.reg (.low .rbx .W64)) (.imm (.int64 0))))
private abbrev c_jz : Directive := .instr (.regular .W64 .W64 (.jcc .z "_end"))
private abbrev c_mulx : Directive :=
  .instr (.regular .W64 .W64 (.mulx (.low .rax .W64) (.low .rdx .W64) (.reg (.low .rdx .W64))))
private abbrev c_sub1 : Directive :=
  .instr (.regular .W64 .W64 (.sub (.reg (.low .rbx .W64)) (.imm (.int64 1))))
private abbrev c_jmp : Directive :=
  .instr (.regular .W64 .W64 (.jmp (.rel (.sub (.label "start") .after_current_instruction))))
private abbrev c_end : Directive := .label "_end"
private abbrev c_nop : Directive := .instr (.regular .W64 .W64 (.nop 1))

/-- The loop body: everything the run traverses from past the `start` cell. -/
private abbrev p3_body : Program := [c_sub0, c_jz, c_mulx, c_sub1, c_jmp, c_end, c_nop]

/-- The conditional exit of the loop, with its dispatch computed: `_end` is in
scope, and the taken branch continues at the tail fragment. -/
private theorem p3_jz_spec (Q : Unit → MachineData → Prop) (E : Label → MachineData → Prop) :
    ⦃ fun s =>
        (CondCode.z.interp s.status = true → wp ([c_end, c_nop] : Program) Q E s)
          ⊓ (CondCode.z.interp s.status = false →
              wp ([c_mulx, c_sub1, c_jmp, c_end, c_nop] : Program) Q E s) ⦄
      (c_jz :: [c_mulx, c_sub1, c_jmp, c_end, c_nop])
    ⦃ Q; E ⦄ := by
  have h := Program.jcc_spec (p := [c_mulx, c_sub1, c_jmp, c_end, c_nop])
    (Q := Q) (E := E) .W64 .W64 .z "_end"
  rw [show Program.fromLabel [c_mulx, c_sub1, c_jmp, c_end, c_nop] "_end"
      = [c_end, c_nop] by decide] at h
  simp only [show (([c_end, c_nop] : Program) = []) = False by simp, if_false] at h
  exact h

/-- The back jump of the loop, with its dispatch computed: `start` is not a
label of what follows, so the exit surfaces at `start`. -/
private theorem p3_jmp_spec (Q : Unit → MachineData → Prop) (E : Label → MachineData → Prop) :
    ⦃ fun s => E "start" s ⦄
      (c_jmp :: [c_end, c_nop])
    ⦃ Q; E ⦄ := by
  have h := Program.jmp_label_spec (p := [c_end, c_nop]) (Q := Q) (E := E) .W64 .W64 "start"
  rw [show Program.fromLabel [c_end, c_nop] "start" = [] by decide] at h
  simp only [reduceIte] at h
  exact h

/-- The loop body, traversed once: the countdown either reaches zero and the
run continues through `_end` off the end of the text with the answer, or one
squaring runs and the back jump exits at `start` with the invariant one step
down. -/
private theorem p3_body_spec (rbx0 : Nat) (hbound : 2 ^ 2 ^ rbx0 < 2 ^ 64)
    (E : Label → MachineData → Prop) (k : Nat) :
    ⦃ p3_inv rbx0 k ⦄
      p3_body
    ⦃ fun _ s => s.regs.rdx.toNat = 2 ^ 2 ^ rbx0 ∧ s.regs.rax = 0;
      fun l s => if l = "start" then k ≠ 0 ∧ p3_inv rbx0 (k - 1) s else E l s ⦄ := by
  with_reducible refine Triple.intro fun s ⟨hrbx, hle, hrdx, hrax⟩ => ?_
  have hlt : k ≠ 0 → s.regs.rdx.toNat * s.regs.rdx.toNat < 2 ^ 64 := by
    intro _
    rw [hrdx, pow_sq]
    calc 2 ^ 2 ^ (rbx0 - k + 1)
        ≤ 2 ^ 2 ^ rbx0 :=
          Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
      _ < 2 ^ 64 := hbound
  have hsq : k ≠ 0 → s.regs.rdx.toNat * s.regs.rdx.toNat = 2 ^ 2 ^ (rbx0 - (k - 1)) := by
    intro hk
    rw [hrdx, pow_sq, show rbx0 - (k - 1) = rbx0 - k + 1 from by omega]
  vcgen [p3_jz_spec, p3_jmp_spec] simplifying_assumptions with finish

/-- A run of `p3` from a machine whose `rax` is clear falls off the end of the
text with `rdx = 2 ^ 2 ^ rbx` and `rax` clear again. The exceptional
postcondition is `False`: the run never leaves the text. -/
theorem p3_correct (d : MachineData) (h_bounds : p3_spec d < 2 ^ 64)
    (h_rax : d.regs.rax = 0) :
    ⦃ fun s => s = d ⦄
      p3
    ⦃ fun _ s => s.regs.rdx.toNat = p3_spec d ∧ s.regs.rax = 0;
      fun _ _ => False ⦄ := by
  with_reducible refine Triple.intro fun s hs => ?_
  rw [hs]
  simp only [p3_spec] at h_bounds ⊢
  simp only [p3, p3.entry, p3.loop, p3.exit, List.cons_append, List.nil_append]
  have hbody : ∀ k, ⦃ p3_inv d.regs.rbx.toNat k ⦄ p3_body
      ⦃ fun _ s => s.regs.rdx.toNat = 2 ^ 2 ^ d.regs.rbx.toNat ∧ s.regs.rax = 0;
        fun l s => if l = "start" then ∃ j, j < k ∧ p3_inv d.regs.rbx.toNat j s
                   else (fun _ (_ : MachineData) => False) l s ⦄ := by
    intro k
    refine Program.triple_mono
      (p3_body_spec d.regs.rbx.toNat h_bounds (fun _ _ => False) k) ?_
    intro l s' h
    by_cases hl : l = "start"
    · rw [if_pos hl] at h ⊢
      obtain ⟨hk, hinv⟩ := h
      exact ⟨k - 1, by omega, hinv⟩
    · rw [if_neg hl] at h
      exact h.elim
  have hloop := Program.label_loop_spec "start" (p3_inv d.regs.rbx.toNat) (by decide) hbody
  vcgen [hloop] simplifying_assumptions with finish

variable [layout : Layout] [hv : Executable.ValidLayout (layout p3)]

/-- `p3_correct`, read at the machine: the omni-semantics judgment of
`Kraken.OmniSemantics` that a run of the laid-out program from
`(d, layout.start)` reaches a state with `rdx = 2 ^ 2 ^ rbx` and `rax` clear.
The exit disjunct drops out because the triple's exceptional postcondition is
`False`. -/
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
