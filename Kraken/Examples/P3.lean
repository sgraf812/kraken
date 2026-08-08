/-
The squaring loop `p3`: starting from `rdx = 2`, each iteration squares `rdx`
by `mulx` and counts `rbx` down to zero, so the loop computes
`rdx = 2 ^ 2 ^ rbx`. The statement targets the omni-semantics judgments
(`straightlineStep` segments chained by `Eventually`); completing the proof is
the acceptance test for the weakest-precondition instance on the deep
embedding.
-/
import Kraken.OmniSemantics
import Kraken.Parser
import Kraken.SegmentExtract

open Kraken.Parser

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

/-! ## Segment extraction

The three cut points a run of `p3` visits: the entry, the loop head `start`,
and the exit label `_end`. -/

section Extraction

theorem p3_entry_segment [layout : Layout] :
    (layout p3).directivesFromAddress layout.start = (layout p3).2 := by
  have h := Executable.directivesFromAddress_addrOf (layout p3) 0 (Nat.zero_le _)
    (fun k hk => absurd hk (Nat.not_lt_zero k))
  simpa [Layout.apply] using h

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

theorem p3_start_segment :
    (layout p3).directivesFromAddress ((layout p3).labels.label "start")
      = (layout p3).2.drop 2 := by
  rw [p3_start_addr]
  apply Executable.directivesFromAddress_addrOf
  · simp [p3, Layout.apply]
  · intro k hk
    apply Executable.addrOf_ne_of_valid (layout p3) hk
      (d := .instr (.regular .W64 .W64 (.mov (.reg (.low .rdx .W64)) (.imm (.int64 2)))))
      (z := layout.size 1)
    · simp [p3, Layout.apply]
    · intro l; simp

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

theorem p3_correct [layout : Layout] [Executable.ValidLayout (layout p3)]
    (d : MachineData) (h_bounds : p3_spec d < 2 ^ 64) :
    Eventually (straightlineStep (layout p3))
      (fun s => s.1.regs.rdx.toNat = p3_spec d ∧ s.1.regs.rax = 0)
      (d, layout.start) := by
  sorry
