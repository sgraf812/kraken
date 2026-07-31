/-
Store through a scaled-index (SIB) address and read the same cell back. The store
and load use the same `Addr` with a base register, a scaled index register and a
displacement, so the reload sees the just-written value.
-/
import Kraken.Tactics
open Std.Internal.Do
open Kraken

set_option mvcgen.warning false
set_option grind.warning false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

-- movq $42, (%rdi,%r15,8); movq (%rdi,%r15,8), %rax
def sibProg : X64M Unit := do
  Op.movMI (Addr.mk .rdi (some (.r15, 8)) 0) 42
  Op.movRM .rax (Addr.mk .rdi (some (.r15, 8)) 0)

theorem sib_correct (s₀ : MachineData) (v : Int)
    (h_mapped : Mem.loadInt s₀.dmem ((Addr.mk .rdi (some (.r15, 8)) 0).eval s₀.regs) 8 = some v)
    (h_back : Mem.loadInt
        (Mem.storeInt s₀.dmem ((Addr.mk .rdi (some (.r15, 8)) 0).eval s₀.regs) 8
          (BitVec.setWidth 64 ((42 : Int64)).toBitVec).toInt)
        ((Addr.mk .rdi (some (.r15, 8)) 0).eval s₀.regs) 8 = some 42) :
    ⦃fun sd => sd = s₀⦄ sibProg
      ⦃fun _ s => s.regs.rax = BitVec.ofInt 64 42⦄ := by
  have h42 : (BitVec.setWidth 64 ((42 : Int64)).toBitVec).toInt = 42 := by decide
  sym =>
    vcgen [sibProg]
    all_goals (first (easm) (skip))
    all_goals finish (splits := 40)
