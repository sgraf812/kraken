/-
The squaring loop `p3`: starting from `rdx = 2`, each iteration squares `rdx`
by `mulx` and counts `rbx` down to zero, so the loop computes
`rdx = 2 ^ 2 ^ rbx`. `p3_correct` proves it against the omni-semantics
judgments.

The program is three fragments, `p3.entry ++ p3.loop ++ p3.exit`, cut at the
labels a run jumps to. Each cut point gets an address (`p3_start_addr`,
`p3_end_addr`) and the directives reached from it (`p3_start_segment`,
`p3_end_segment`); `vcgen` steps through those directives against the segment
weakest-precondition specs. The segments chain by `Eventually.step`, and the
loop closes by `Eventually.loop` with the invariant
`rbx = k ∧ rdx = 2 ^ 2 ^ (rbx₀ - k)` at the header.
-/
import Kraken.Parser
import Kraken.SegmentExtract
import Kraken.SegmentWP
import Kraken.SegmentWPSound

open Kraken.Parser
open Std.Internal.Do

set_option mvcgen.warning false

/-- Expand a fragment expression into the directive list `vcgen` steps through. -/
local macro "materialize" "[" fs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [$fs,*, List.cons_append, List.nil_append,
      List.mapIdx_cons, List.mapIdx_nil])

/-- The prologue: it sets the base `rdx` holds on entry to the loop. -/
def p3.entry : Program := parse("
init:
  mov $2, %rdx
")

/-- The loop: it squares `rdx` and counts `rbx` down, jumping to `_end` at zero. -/
def p3.loop : Program := parse("
start:
  sub $0, %rbx
  jz _end
  mulx %rdx, %rdx, %rax
  sub $1, %rbx
  jmp start
")

/-- The tail the loop exits to. -/
def p3.exit : Program := parse("
_end:
  nop
")

/-- The program a run of `p3` executes: the prologue, the loop, the tail. -/
def p3 : Program := p3.entry ++ p3.loop ++ p3.exit

/-- The directives a run reaches from the loop header: the loop and the tail it
falls into, laid out past the prologue. -/
def p3.body [layout : Layout] : List (Directive × Nat) :=
  (p3.loop ++ p3.exit).mapIdx (fun i d => (d, layout.size (p3.entry.length + i)))

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

The three cut points a run of `p3` visits: the entry, the loop head `start`,
and the exit label `_end`. Each cut point falls on a fragment boundary, so the
text a segment traverses is the suffix of `p3.entry ++ p3.loop ++ p3.exit` that
starts there, laid out with the sizes past the fragments before it. -/

section Extraction

attribute [local simp] p3 p3.entry p3.loop p3.exit Layout.apply_fst Layout.apply_snd

variable [layout : Layout]

theorem p3_entry_segment :
    (layout p3).directivesFromAddress layout.start
      = (p3.entry ++ p3.loop ++ p3.exit).mapIdx (fun i d => (d, layout.size i)) := by
  have h := Executable.directivesFromAddress_addrOf (layout p3) 0 (Nat.zero_le _)
    (fun k hk => absurd hk (Nat.not_lt_zero k))
  simpa using h

variable [hv : Executable.ValidLayout (layout p3)]

theorem p3_start_addr :
    (layout p3).labels.label "start" = (layout p3).addrOf p3.entry.length := by
  have h2 : (layout p3).2[p3.entry.length]? = some (.label "start", layout.size p3.entry.length) := by
    simp
  with_reducible apply Executable.label_addrOf
  · rw [h2, hv.label_size _ "start" _ h2]
  · simp

/-- From the loop header the run traverses the loop fragment and the tail it
falls into. -/
theorem p3_start_segment :
    (layout p3).directivesFromAddress ((layout p3).labels.label "start")
      = p3.body := by
  rw [p3_start_addr, Executable.directivesFromAddress_addrOf]
  · rw [p3_eq_entry_append]
    unfold p3.body
    with_reducible exact Layout.apply_drop p3.entry (p3.loop ++ p3.exit)
  · simp
  · intro k hk
    with_reducible apply Executable.addrOf_ne_of_valid (layout p3) hk <;>
      simp

omit hv in
/-- Where the exit label sits in the directive list. -/
private theorem p3_idx_end :
    (layout p3).2[(p3.entry ++ p3.loop).length]?
      = some (.label "_end", layout.size (p3.entry ++ p3.loop).length) := by
  simp

theorem p3_end_addr :
    (layout p3).labels.label "_end" = (layout p3).addrOf (p3.entry ++ p3.loop).length := by
  with_reducible apply Executable.label_addrOf
  · rw [p3_idx_end, hv.label_size _ "_end" _ p3_idx_end]
  · simp

/-- From `_end` the run traverses the tail fragment alone. -/
theorem p3_end_segment :
    (layout p3).directivesFromAddress ((layout p3).labels.label "_end")
      = p3.exit.mapIdx (fun i d => (d, layout.size ((p3.entry ++ p3.loop).length + i))) := by
  rw [p3_end_addr, Executable.directivesFromAddress_addrOf]
  · rw [p3_eq_loop_append]
    with_reducible exact Layout.apply_drop (p3.entry ++ p3.loop) p3.exit
  · simp
  · intro k hk
    with_reducible apply Executable.addrOf_ne_of_valid (layout p3) hk <;>
      simp

/-- Traversing the tail fragment ends just past the program text. -/
private theorem p3_end_pc :
    (layout p3).labels.label "_end"
        + .ofNat (layout.size (p3.entry ++ p3.loop).length)
        + .ofNat (layout.size ((p3.entry ++ p3.loop).length + 1))
      = (layout p3).addrOf p3.length := by
  have h9 : (layout p3).2[(p3.entry ++ p3.loop).length + 1]?
      = some (.instr (.regular .W64 .W64 (.nop 1)),
          layout.size ((p3.entry ++ p3.loop).length + 1)) := by
    simp
  rw [p3_end_addr, ← Executable.addrOf_succ (layout p3) p3_idx_end,
    ← Executable.addrOf_succ (layout p3) h9]
  simp

end Extraction

/-! ## The proof -/

section Proof

variable [layout : Layout] [hv : Executable.ValidLayout (layout p3)]

/-- The loop invariant at the header, indexed by the remaining iteration
count `k`: `rbx` holds `k` and `rdx` holds the `rbx₀ - k`-fold squaring. -/
private abbrev p3_inv (rbx0 k : Nat) (s : MachineData) : Prop :=
  s.regs.rbx.toNat = k ∧ k ≤ rbx0 ∧ s.regs.rdx.toNat = 2 ^ 2 ^ (rbx0 - k) ∧ s.regs.rax = 0

/-- Running the exit segment: the label and the `nop` leave the machine
unchanged, and the run stops just past the program text. -/
private theorem p3_end_run (s : MachineData) (post : @Post MachineState)
    (h : post (s, (layout p3).addrOf p3.length)) :
    Eventually (straightlineStep (layout p3)) post (s, (layout p3).labels.label "_end") := by
  with_reducible apply step_cps
  with_reducible apply straightlineStep_of_wp
  rw [p3_end_segment]
  materialize [p3.exit]
  vcgen simplifying_assumptions
  simp only [Nat.add_zero]
  rw [p3_end_pc]
  with_reducible exact Eventually.done _ h

omit hv in
/-- The entry segment: `rdx` is set to `2`, and the loop test either exits to
`_end` at once or runs the first iteration and arrives at `start` with the
invariant established at `rbx₀ - 1`. -/
private theorem p3_enter (d : MachineData) :
    straightlineStep (layout p3) (d, layout.start) (fun mid =>
      (d.regs.rbx.toNat = 0 ∧ mid.2 = (layout p3).labels.label "_end"
        ∧ mid.1.regs.rdx.toNat = 2 ∧ mid.1.regs.rax = d.regs.rax)
      ∨ (d.regs.rbx.toNat ≠ 0 ∧ mid.2 = (layout p3).labels.label "start"
          ∧ p3_inv d.regs.rbx.toNat (d.regs.rbx.toNat - 1) mid.1)) := by
  with_reducible apply straightlineStep_of_wp
  rw [p3_entry_segment]
  materialize [p3.entry, p3.loop, p3.exit]
  vcgen simplifying_assumptions with finish

omit hv in
/-- The loop body: entered at the header with `k ≠ 0` iterations left, the
traversal never falls off the program text and every jump exit lands back on
the header with the invariant at `k - 1`. -/
private theorem p3_body (rbx0 : Nat) (hbound : 2 ^ 2 ^ rbx0 < 2 ^ 64) (k : Nat) (hk : k ≠ 0) :
    ⦃ fun labels st => labels = (layout p3).labels
        ∧ st.2 = (layout p3).labels.label "start" ∧ p3_inv rbx0 k st.1 ⦄
      p3.body
    ⦃ fun _ _ _ => False;
      fun st => st.2 = (layout p3).labels.label "start" ∧ p3_inv rbx0 (k - 1) st.1 ⦄ := by
  with_reducible refine Triple.intro fun labels st ⟨hlab, hpc, hrbx, hle, hrdx, hrax⟩ => ?_
  subst hlab
  have hlt : st.1.regs.rdx.toNat * st.1.regs.rdx.toNat < 2 ^ 64 := by
    rw [hrdx, pow_sq]
    calc 2 ^ 2 ^ (rbx0 - k + 1)
        ≤ 2 ^ 2 ^ rbx0 :=
          Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
      _ < 2 ^ 64 := hbound
  have hsq : st.1.regs.rdx.toNat * st.1.regs.rdx.toNat = 2 ^ 2 ^ (rbx0 - (k - 1)) := by
    rw [hrdx, pow_sq, show rbx0 - (k - 1) = rbx0 - k + 1 from by omega]
  materialize [p3.body, p3.loop, p3.exit]
  vcgen simplifying_assumptions with finish

/-- The loop exit: entered at the header with the countdown at zero, the test
takes the jump to `_end` and the run reaches the postcondition. -/
private theorem p3_exit (rbx0 : Nat) (s : MachineData) (h : p3_inv rbx0 0 s) :
    Eventually (straightlineStep (layout p3))
      (fun st => st.1.regs.rdx.toNat = 2 ^ 2 ^ rbx0 ∧ st.1.regs.rax = 0)
      (s, (layout p3).labels.label "start") := by
  obtain ⟨hrbx, hle, hrdx, hrax⟩ := h
  with_reducible refine Eventually.step _ (fun st => st.2 = (layout p3).labels.label "_end"
    ∧ st.1.regs.rdx = s.regs.rdx ∧ st.1.regs.rax = s.regs.rax) ?_ ?_
  · with_reducible apply straightlineStep_of_wp
    rw [p3_start_segment]
    materialize [p3.body, p3.loop, p3.exit]
    vcgen simplifying_assumptions with finish
  · rintro ⟨m, pc⟩ ⟨hpc, hrdx', hrax'⟩
    subst hpc
    with_reducible apply p3_end_run
    with_reducible exact ⟨by rw [hrdx', hrdx]; simp, by rw [hrax', hrax]⟩

theorem p3_correct (d : MachineData) (h_bounds : p3_spec d < 2 ^ 64)
    (h_rax : d.regs.rax = 0) :
    Eventually (straightlineStep (layout p3))
      (fun s => s.1.regs.rdx.toNat = p3_spec d ∧ s.1.regs.rax = 0)
      (d, layout.start) := by
  simp only [p3_spec] at h_bounds ⊢
  with_reducible apply Eventually.step _ _ (p3_enter d)
  rintro ⟨m, pc⟩ (⟨h0, hpc, hrdx2, hraxd⟩ | ⟨hne, hpc, hinv⟩)
  · subst hpc
    with_reducible apply p3_end_run
    with_reducible exact ⟨by simp [h0, hrdx2], by rw [hraxd, h_rax]⟩
  · subst hpc
    with_reducible
      exact Eventually.loop p3_start_segment
        (fun k hk => p3_body d.regs.rbx.toNat h_bounds k hk)
        (fun s hs => p3_exit d.regs.rbx.toNat s hs) _ m hinv

end Proof
