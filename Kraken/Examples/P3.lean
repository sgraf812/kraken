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

theorem p3_correct [layout : Layout] (d : MachineData)
    (h_bounds : p3_spec d < 2 ^ 64) :
    Eventually (straightlineStep (layout p3))
      (fun s => s.1.regs.rdx.toNat = p3_spec d ∧ s.1.regs.rax = 0)
      (d, layout.start) := by
  sorry
