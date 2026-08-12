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

def p3 : Program := parse("
init:
  mov $2, %rdx
start:
  sub $0, %rbx
  jz _end
  mulx %rdx, %rdx, %rax
  sub $1, %rbx
  jmp start
_end:
  nop
")

def p3_spec (d : MachineData) : Nat := 2 ^ 2 ^ d.regs.rbx.toNat

private theorem pow_sq (e : Nat) : 2 ^ 2 ^ e * 2 ^ 2 ^ e = 2 ^ 2 ^ (e + 1) := by
  rw [← Nat.pow_add, Nat.pow_succ, Nat.mul_two]

/-! ## Segment extraction

The three cut points a run of `p3` visits: the entry, the loop head `start`,
and the exit label `_end`. -/

section Extraction

theorem p3_entry_segment [layout : Layout] :
    (layout p3).directivesFromAddress layout.start = (layout p3).2 := by
  have h := Executable.directivesFromAddress_addrOf (layout p3) 0 (Nat.zero_le _)
    (fun k hk => absurd hk (Nat.not_lt_zero k))
  simpa [Layout.apply] using h

/-- The laid-out directive list of `p3`. -/
private theorem p3_dirs [layout : Layout] :
    (layout p3).2 =
      [(Directive.label "init", layout.size 0),
       (Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low .rdx .W64)) (.imm (.int64 2)))), layout.size 1),
       (Directive.label "start", layout.size 2),
       (Directive.instr (.regular .W64 .W64
          (.sub (.reg (.low .rbx .W64)) (.imm (.int64 0)))), layout.size 3),
       (Directive.instr (.regular .W64 .W64 (.jcc .z "_end")), layout.size 4),
       (Directive.instr (.regular .W64 .W64
          (.mulx (.low .rax .W64) (.low .rdx .W64) (.reg (.low .rdx .W64)))), layout.size 5),
       (Directive.instr (.regular .W64 .W64
          (.sub (.reg (.low .rbx .W64)) (.imm (.int64 1)))), layout.size 6),
       (Directive.instr (.regular .W64 .W64
          (.jmp (.rel (.sub (.label "start") .after_current_instruction)))), layout.size 7),
       (Directive.label "_end", layout.size 8),
       (Directive.instr (.regular .W64 .W64 (.nop 1)), layout.size 9)] := by
  simp [p3, Layout.apply, List.mapIdx_cons, List.mapIdx_nil]

variable [layout : Layout] [hv : Executable.ValidLayout (layout p3)]

theorem p3_start_addr :
    (layout p3).labels.label "start" = (layout p3).addrOf 2 := by
  have h2 : (layout p3).2[2]? = some (.label "start", layout.size 2) := by
    simp [p3, Layout.apply]
  apply Executable.label_addrOf
  · rw [h2, hv.label_size 2 "start" _ h2]
  · intro k hk
    match k, hk with
    | 0, _ => simp [p3, Layout.apply]
    | 1, _ => simp [p3, Layout.apply]

theorem p3_loop_segment :
    (layout p3).directivesFromAddress ((layout p3).addrOf 2) = (layout p3).2.drop 2 := by
  apply Executable.directivesFromAddress_addrOf
  · simp [p3, Layout.apply]
  · intro k hk
    apply Executable.addrOf_ne_of_valid (layout p3) hk
      (d := .instr (.regular .W64 .W64 (.mov (.reg (.low .rdx .W64)) (.imm (.int64 2)))))
      (z := layout.size 1)
    · simp [p3, Layout.apply]
    · intro l; simp

theorem p3_start_segment :
    (layout p3).directivesFromAddress ((layout p3).labels.label "start")
      = (layout p3).2.drop 2 := by
  rw [p3_start_addr]
  exact p3_loop_segment

theorem p3_end_addr :
    (layout p3).labels.label "_end" = (layout p3).addrOf 8 := by
  have h8 : (layout p3).2[8]? = some (.label "_end", layout.size 8) := by
    simp [p3, Layout.apply]
  apply Executable.label_addrOf
  · rw [h8, hv.label_size 8 "_end" _ h8]
  · intro k hk
    match k, hk with
    | 0, _ => simp [p3, Layout.apply]
    | 1, _ => simp [p3, Layout.apply]
    | 2, _ => simp [p3, Layout.apply]
    | 3, _ => simp [p3, Layout.apply]
    | 4, _ => simp [p3, Layout.apply]
    | 5, _ => simp [p3, Layout.apply]
    | 6, _ => simp [p3, Layout.apply]
    | 7, _ => simp [p3, Layout.apply]

theorem p3_end_segment :
    (layout p3).directivesFromAddress ((layout p3).labels.label "_end")
      = (layout p3).2.drop 8 := by
  rw [p3_end_addr]
  apply Executable.directivesFromAddress_addrOf
  · simp [p3, Layout.apply]
  · intro k hk
    apply Executable.addrOf_ne_of_valid (layout p3) hk
      (d := .instr (.regular .W64 .W64
        (.jmp (.rel (.sub (.label "start") .after_current_instruction)))))
      (z := layout.size 7)
    · simp [p3, Layout.apply]
    · intro l; simp

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
  rw [p3_end_segment, p3_dirs]
  simp only [List.drop_succ_cons, List.drop_zero]
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
  rw [p3_entry_segment, p3_dirs]
  have hstart : (layout p3).labels.label "start" = (layout p3).addrOf 2 :=
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
      ((layout p3).2.drop 2)
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
  rw [p3_dirs]
  simp only [List.drop_succ_cons, List.drop_zero]
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
    rw [p3_start_segment, p3_dirs]
    simp only [List.drop_succ_cons, List.drop_zero]
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
