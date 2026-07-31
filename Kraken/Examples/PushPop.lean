/-
Push a register, overwrite it, then pop it back: the stack slot roundtrips the
original value. `vcgen simplifying_assumptions` folds the pop's load into a
read-over-write over the push's store at the same stack address, `easm` reads the
mapped-ness and the stored value off the memory hypotheses, and the register
identity `BitVec.ofInt_toInt` (the value stored as an integer and reloaded) closes
the postcondition.
-/
import Kraken.Tactics
import Kraken.StateSimp
import Std.Tactic.BVDecide

open Std.Internal.Do
open Kraken

set_option mvcgen.warning false
set_option grind.warning false
set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

-- pushq %rbx; movq $0, %rbx; popq %rbx
def pushPopProg : X64M Unit := do
  Op.pushR .rbx
  Op.movRI .rbx 0
  Op.popR .rbx

theorem pushpop_roundtrip (s : MachineData)
    (h_mapped : Mem.loadInt s.dmem ((s.regs.get64 .rsp).toBitVec - 8#64) 8
      = some ((s.regs.get64 .rbx).toBitVec.toInt))
    (h_back : Mem.loadInt
        (Mem.storeInt s.dmem ((s.regs.get64 .rsp).toBitVec - 8#64) 8
          ((s.regs.get64 .rbx).toBitVec.toInt))
        ((s.regs.get64 .rsp).toBitVec - 8#64) 8
      = some ((s.regs.get64 .rbx).toBitVec.toInt)) :
    ⦃fun s0 => s0 = s⦄ pushPopProg
      ⦃fun _ s' => s'.regs.get64 .rbx = s.regs.get64 .rbx⦄ := by
  vcgen [pushPopProg] simplifying_assumptions with (first (easm) (skip))
  all_goals (simp only [BitVec.ofInt_toInt] <;> bv_decide)
