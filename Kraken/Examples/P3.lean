/-
The squaring loop `p3`: starting from `rdx = 2`, each iteration squares `rdx`
by `mulx` and counts `rbx` down to zero, so the loop computes
`rdx = 2 ^ 2 ^ rbx`. `p3_correct` proves it against the omni-semantics
judgments: each straightline segment is discharged by `vcgen` through the
segment weakest-precondition specs, the segments chain by `Eventually.step`,
and the loop closes by `Eventually.loop` with the invariant
`rbx = k ∧ rdx = 2 ^ 2 ^ (rbx₀ - k)` at the header.
-/
import Kraken.Parser
import Kraken.SegmentExtract
import Kraken.SegmentWP
import Kraken.SegmentWPSound

open Kraken.Parser
open Std.Internal.Do

set_option mvcgen.warning false

def p3.entry : Program := parse("
init:
  mov $2, %rdx
")

def p3.loop : Program := parse("
start:
  sub $0, %rbx
  jz _end
  mulx %rdx, %rdx, %rax
  sub $1, %rbx
  jmp start
")

def p3.exit : Program := parse("
_end:
  nop
")

/-- The program a run of `p3` executes: the prologue, the loop, the tail. -/
def p3 : Program := p3.entry ++ p3.loop ++ p3.exit

def p3_spec (d : MachineData) : Nat := 2 ^ 2 ^ d.regs.rbx.toNat

private theorem pow_sq (e : Nat) : 2 ^ 2 ^ e * 2 ^ 2 ^ e = 2 ^ 2 ^ (e + 1) := by
  rw [← Nat.pow_add, Nat.pow_succ, Nat.mul_two]

/-! ## Segment extraction

The three cut points a run of `p3` visits: the entry, the loop head `start`,
and the exit label `_end`. Each cut point falls on a fragment boundary, so the
text a segment traverses is the suffix of `p3.entry ++ p3.loop ++ p3.exit` that
starts there, laid out with the sizes past the fragments before it. -/

section Extraction

variable [layout : Layout]

theorem p3_entry_segment :
    (layout p3).directivesFromAddress layout.start
      = (p3.entry ++ p3.loop ++ p3.exit).mapIdx (fun i d => (d, layout.size i)) := by
  have h := Executable.directivesFromAddress_addrOf (layout p3) 0 (Nat.zero_le _)
    (fun k hk => absurd hk (Nat.not_lt_zero k))
  simpa [p3, Layout.apply] using h

variable [hv : Executable.ValidLayout (layout p3)]

theorem p3_start_addr :
    (layout p3).labels.label "start" = (layout p3).addrOf p3.entry.length := by
  have h2 : (layout p3).2[p3.entry.length]? = some (.label "start", layout.size p3.entry.length) := by
    simp [p3, p3.entry, p3.loop, p3.exit, Layout.apply]
  apply Executable.label_addrOf
  · rw [h2, hv.label_size _ "start" _ h2]
  · simp [p3, p3.entry, p3.loop, p3.exit, Layout.apply]

/-- From the loop header the run traverses the loop fragment and the tail it
falls into. -/
theorem p3_start_segment :
    (layout p3).directivesFromAddress ((layout p3).labels.label "start")
      = (p3.loop ++ p3.exit).mapIdx (fun i d => (d, layout.size (p3.entry.length + i))) := by
  rw [p3_start_addr, Executable.directivesFromAddress_addrOf]
  · exact Layout.apply_drop p3.entry (p3.loop ++ p3.exit)
  · simp [p3, p3.entry, p3.loop, p3.exit, Layout.apply]
  · intro k hk
    apply Executable.addrOf_ne_of_valid (layout p3) hk <;>
      simp [p3, p3.entry, p3.loop, p3.exit, Layout.apply]

theorem p3_end_addr :
    (layout p3).labels.label "_end" = (layout p3).addrOf (p3.entry ++ p3.loop).length := by
  have h8 : (layout p3).2[(p3.entry ++ p3.loop).length]?
      = some (.label "_end", layout.size (p3.entry ++ p3.loop).length) := by
    simp [p3, p3.entry, p3.loop, p3.exit, Layout.apply]
  apply Executable.label_addrOf
  · rw [h8, hv.label_size _ "_end" _ h8]
  · simp [p3, p3.entry, p3.loop, p3.exit, Layout.apply]

/-- From `_end` the run traverses the tail fragment alone. -/
theorem p3_end_segment :
    (layout p3).directivesFromAddress ((layout p3).labels.label "_end")
      = p3.exit.mapIdx (fun i d => (d, layout.size ((p3.entry ++ p3.loop).length + i))) := by
  rw [p3_end_addr, Executable.directivesFromAddress_addrOf]
  · exact Layout.apply_drop (p3.entry ++ p3.loop) p3.exit
  · simp [p3, p3.entry, p3.loop, p3.exit, Layout.apply]
  · intro k hk
    apply Executable.addrOf_ne_of_valid (layout p3) hk <;>
      simp [p3, p3.entry, p3.loop, p3.exit, Layout.apply]

end Extraction

/-! ## The proof -/

section Proof

variable [layout : Layout] [hv : Executable.ValidLayout (layout p3)]

/-- The loop invariant at the header, indexed by the remaining iteration
count `k`: `rbx` holds `k` and `rdx` holds the `rbx₀ - k`-fold squaring. -/
private abbrev p3_inv (rbx0 k : Nat) (s : MachineData) : Prop :=
  s.regs.rbx.toNat = k ∧ k ≤ rbx0 ∧ s.regs.rdx.toNat = 2 ^ 2 ^ (rbx0 - k) ∧ s.regs.rax = 0

/-- Running the exit segment: the label and the `nop` leave the machine
unchanged, and the run falls off the end of the program text. -/
private theorem p3_end_run (s : MachineData) (post : @Post MachineState)
    (h : ∀ pc, post (s, pc)) :
    Eventually (straightlineStep (layout p3)) post (s, (layout p3).labels.label "_end") := by
  apply step_cps
  apply straightlineStep_of_wp
  rw [p3_end_segment]
  simp only [p3.exit, List.mapIdx_cons, List.mapIdx_nil]
  vcgen
  exact Eventually.done _ (h _)

/-- The entry segment: `rdx` is set to `2`, and the loop test either exits to
`_end` at once or runs the first iteration and arrives at `start` with the
invariant established at `rbx₀ - 1`. -/
private theorem p3_enter (d : MachineData) :
    straightlineStep (layout p3) (d, layout.start) (fun mid =>
      (d.regs.rbx.toNat = 0 ∧ mid.2 = (layout p3).labels.label "_end"
        ∧ mid.1.regs.rdx.toNat = 2 ∧ mid.1.regs.rax = d.regs.rax)
      ∨ (d.regs.rbx.toNat ≠ 0 ∧ mid.2 = (layout p3).labels.label "start"
          ∧ p3_inv d.regs.rbx.toNat (d.regs.rbx.toNat - 1) mid.1)) := by
  apply straightlineStep_of_wp
  rw [p3_entry_segment]
  simp only [p3.entry, p3.loop, p3.exit, List.cons_append, List.nil_append,
    List.mapIdx_cons, List.mapIdx_nil]
  have hstart : (layout p3).labels.label "start" = (layout p3).addrOf p3.entry.length :=
    p3_start_addr (layout := layout)
  have hexp : d.regs.rbx.toNat ≠ 0 →
      2 ^ 2 ^ (d.regs.rbx.toNat - (d.regs.rbx.toNat - 1)) = 4 := by
    intro h0
    rw [show d.regs.rbx.toNat - (d.regs.rbx.toNat - 1) = 1 from by omega]
  vcgen simplifying_assumptions with finish

omit hv in
/-- The loop body: entered at the header with `k ≠ 0` iterations left, the
traversal never falls off the program text and every jump exit lands back on
the header with the invariant at `k - 1`. -/
private theorem p3_body (rbx0 : Nat) (hbound : 2 ^ 2 ^ rbx0 < 2 ^ 64) (k : Nat) (hk : k ≠ 0) :
    ⦃ fun labels st => labels = (layout p3).labels
        ∧ st.2 = (layout p3).labels.label "start" ∧ p3_inv rbx0 k st.1 ⦄
      ((p3.loop ++ p3.exit).mapIdx (fun i d => (d, layout.size (p3.entry.length + i))))
    ⦃ fun _ _ _ => False;
      fun st => st.2 = (layout p3).labels.label "start" ∧ p3_inv rbx0 (k - 1) st.1 ⦄ := by
  refine Triple.intro fun labels st ⟨hlab, hpc, hrbx, hle, hrdx, hrax⟩ => ?_
  subst hlab
  have hlt : st.1.regs.rdx.toNat * st.1.regs.rdx.toNat < 2 ^ 64 := by
    rw [hrdx, pow_sq]
    calc 2 ^ 2 ^ (rbx0 - k + 1)
        ≤ 2 ^ 2 ^ rbx0 :=
          Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
      _ < 2 ^ 64 := hbound
  have hsq : st.1.regs.rdx.toNat * st.1.regs.rdx.toNat = 2 ^ 2 ^ (rbx0 - (k - 1)) := by
    rw [hrdx, pow_sq, show rbx0 - (k - 1) = rbx0 - k + 1 from by omega]
  simp only [p3.loop, p3.exit, List.cons_append, List.nil_append,
    List.mapIdx_cons, List.mapIdx_nil]
  vcgen simplifying_assumptions with finish

/-- The loop exit: entered at the header with the countdown at zero, the test
takes the jump to `_end` and the run reaches the postcondition. -/
private theorem p3_exit (rbx0 : Nat) (s : MachineData) (h : p3_inv rbx0 0 s) :
    Eventually (straightlineStep (layout p3))
      (fun st => st.1.regs.rdx.toNat = 2 ^ 2 ^ rbx0 ∧ st.1.regs.rax = 0)
      (s, (layout p3).labels.label "start") := by
  obtain ⟨hrbx, hle, hrdx, hrax⟩ := h
  refine Eventually.step _ (fun st => st.2 = (layout p3).labels.label "_end"
    ∧ st.1.regs.rdx = s.regs.rdx ∧ st.1.regs.rax = s.regs.rax) ?_ ?_
  · apply straightlineStep_of_wp
    rw [p3_start_segment]
    simp only [p3.loop, p3.exit, List.cons_append, List.nil_append,
      List.mapIdx_cons, List.mapIdx_nil]
    vcgen simplifying_assumptions with finish
  · rintro ⟨m, pc⟩ ⟨hpc, hrdx', hrax'⟩
    simp only at hpc hrdx' hrax'
    subst hpc
    apply p3_end_run
    intro pc'
    exact ⟨by rw [hrdx', hrdx]; simp, by rw [hrax', hrax]⟩

set_option maxHeartbeats 1000000 in
theorem p3_correct (d : MachineData) (h_bounds : p3_spec d < 2 ^ 64)
    (h_rax : d.regs.rax = 0) :
    Eventually (straightlineStep (layout p3))
      (fun s => s.1.regs.rdx.toNat = p3_spec d ∧ s.1.regs.rax = 0)
      (d, layout.start) := by
  have hbound : 2 ^ 2 ^ d.regs.rbx.toNat < 2 ^ 64 := by simpa [p3_spec] using h_bounds
  apply Eventually.step _ _ (p3_enter d)
  rintro ⟨m, pc⟩ (⟨h0, hpc, hrdx2, hraxd⟩ | ⟨hne, hpc, hinv⟩)
  · simp only at hpc
    subst hpc
    apply p3_end_run
    intro pc'
    exact ⟨by simp [p3_spec, h0, hrdx2], by rw [hraxd, h_rax]⟩
  · simp only at hpc hinv
    subst hpc
    exact Eventually.loop (l := "start") p3_start_segment
      (fun k hk => p3_body d.regs.rbx.toNat hbound k hk)
      (fun s hs => p3_exit d.regs.rbx.toNat s hs) _ m hinv

end Proof
