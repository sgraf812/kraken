/-
The squaring loop `p3`: starting from `rdx = 2`, each iteration squares `rdx`
by `mulx` and counts `rbx` down to zero, so the loop computes
`rdx = 2 ^ 2 ^ rbx`. `p3_correct` proves it against the omni-semantics
judgments: each straightline segment is discharged by `vcgen` through the
segment weakest-precondition specs, the segments chain by `step_cps`, and the
loop closes by `reg_dec_loop` with the invariant `rdx = 2 ^ 2 ^ (rbx₀ - i)`
at the loop head.
-/
import Kraken.Parser
import Kraken.SegmentExtract
import Kraken.SegmentWP

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

private theorem ofInt_mul_lo (a b : BitVec 64) (h : a.toNat * b.toNat < 2 ^ 64) :
    (BitVec.ofInt 64 ((a.toNat : Int) * (b.toNat : Int))).toNat = a.toNat * b.toNat := by
  rw [← Int.natCast_mul, BitVec.ofInt_natCast]
  simp [Nat.mod_eq_of_lt h]

private theorem ofInt_mul_hi (a b : BitVec 64) (h : a.toNat * b.toNat < 2 ^ 64) :
    BitVec.ofInt 64 (((a.toNat : Int) * (b.toNat : Int)) >>> 64) = 0#64 := by
  rw [← Int.natCast_mul, ← Int.natCast_shiftRight, Nat.shiftRight_eq_div_pow,
    Nat.div_eq_of_lt h]
  simp

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

/-- Running the exit segment: the label and the `nop` leave the machine
unchanged, and the run falls off the end of the program text. -/
private theorem p3_end_run (s : MachineData) (post : @Post MachineState)
    (h : ∀ pc, post (s, pc)) :
    Eventually (straightlineStep (layout p3)) post (s, (layout p3).labels.label "_end") := by
  apply step_cps
  apply straightlineStep_of_wp (n := 0) (E := fun _ _ => True)
  rw [p3_end_segment, p3_dirs]
  simp only [List.drop_succ_cons, List.drop_zero]
  vcgen
  exact Eventually.done _ (h _)

/-- The loop invariant at the loop head, indexed by the remaining iteration
count `i`: `rbx` holds `i` and `rdx` holds the `rbx₀ - i`-fold squaring. -/
private def p3_inv (rbx0 : Nat) (i : Nat) : @Post MachineState := fun s =>
  s.2 = (layout p3).addrOf 2
    ∧ (s.1.regs.get64 .rbx).toNat = i
    ∧ i ≤ rbx0
    ∧ (s.1.regs.get64 .rdx).toNat = 2 ^ 2 ^ (rbx0 - i)
    ∧ s.1.regs.get64 .rax = 0#64

set_option maxHeartbeats 1000000 in
theorem p3_correct (d : MachineData) (h_bounds : p3_spec d < 2 ^ 64)
    (h_rax : d.regs.rax = 0) :
    Eventually (straightlineStep (layout p3))
      (fun s => s.1.regs.rdx.toNat = p3_spec d ∧ s.1.regs.rax = 0)
      (d, layout.start) := by
  apply step_cps
  apply straightlineStep_of_wp (n := 0) (E := fun _ _ => True)
  rw [p3_entry_segment, p3_dirs]
  vcgen
  case vc1 h =>
    simp [CondCode.interp, StatusFlags.from_result] at h
    apply p3_end_run
    intro pc
    have h0 : d.regs.rbx.toNat = 0 := by
      have := congrArg BitVec.toNat h
      simpa [Reg64s.get64] using this
    constructor
    · simp [p3_spec, h0]
      rfl
    · simp [h_rax]
  case vc2 h =>
    simp [CondCode.interp, StatusFlags.from_result] at h
    have hn0 : d.regs.rbx.toNat ≠ 0 := by
      intro h0
      apply h
      simp only [Reg64s.get64, BitVec.toNat_eq]
      simpa using h0
    have hbound : 2 ^ 2 ^ d.regs.rbx.toNat < 2 ^ 64 := by simpa [p3_spec] using h_bounds
    apply reg_dec_loop _ _ _ (p3_inv d.regs.rbx.toNat) (d.regs.rbx.toNat - 1)
    refine ⟨?init, ?zero, ?step⟩
    case init =>
      have hb := d.regs.rbx.toNat_lt
      refine ⟨p3_start_addr, ?_, by omega, ?_, ?_⟩
      · simp [Reg64s.get64, BitVec.toNat_sub]
        omega
      · have h1 : d.regs.rbx.toNat - (d.regs.rbx.toNat - 1) = 1 := by omega
        simp [Reg64s.get64, h1]
      · simp
        decide
    case zero =>
      rintro ⟨s, pc⟩ ⟨hpc, hrbx, hle, hrdx, hrax⟩
      simp only at hpc
      subst hpc
      apply step_cps
      apply straightlineStep_of_wp (n := 0) (E := fun _ _ => True)
      rw [p3_loop_segment, p3_dirs]
      simp only [List.drop_succ_cons, List.drop_zero]
      vcgen
      case vc1 h' =>
        apply p3_end_run
        intro pc'
        have hrdx' : s.regs.rdx.toNat = p3_spec d := by
          have h1 := hrdx
          simp only [Reg64s.get64, UInt64.toNat_toBitVec, Nat.sub_zero] at h1
          simpa [p3_spec] using h1
        have hrax' : s.regs.rax = 0 := by
          have := congrArg UInt64.ofBitVec hrax
          simpa [Reg64s.get64] using this
        constructor
        · simp [hrdx']
        · simp [hrax']
      case vc2 h' =>
        exfalso
        simp [CondCode.interp, StatusFlags.from_result] at h'
        apply h'
        have h0 : (s.regs.get64 Reg64.rbx) = 0#64 := by
          rw [BitVec.toNat_eq]
          simp [hrbx]
        simp [h0]
    case step =>
      rintro ⟨s, pc⟩ k hk ⟨hpc, hrbx, hle, hrdx, hrax⟩
      simp only at hpc hrbx hle hrdx hrax
      subst hpc
      apply step_cps
      apply straightlineStep_of_wp (n := 0) (E := fun _ _ => True)
      rw [p3_loop_segment, p3_dirs]
      simp only [List.drop_succ_cons, List.drop_zero]
      vcgen
      case vc1 h' =>
        exfalso
        simp [CondCode.interp, StatusFlags.from_result] at h'
        rw [h'] at hrbx
        simp at hrbx
        omega
      case vc2 h' =>
        apply Eventually.done
        have hlt : (s.regs.get64 Reg64.rdx).toNat * (s.regs.get64 Reg64.rdx).toNat < 2 ^ 64 := by
          rw [hrdx, pow_sq]
          calc 2 ^ 2 ^ (d.regs.rbx.toNat - k + 1)
              ≤ 2 ^ 2 ^ d.regs.rbx.toNat :=
                Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
            _ < 2 ^ 64 := hbound
        refine ⟨p3_start_addr, ?_, by omega, ?_, ?_⟩ <;>
          simp [BitVec.toNat_sub, ofInt_mul_lo _ _ hlt, ofInt_mul_hi _ _ hlt]
        · omega
        · rw [hrdx, pow_sq,
            show d.regs.rbx.toNat - (k - 1) = d.regs.rbx.toNat - k + 1 from by omega]

end Proof
