/-
An ALU instruction with a memory source operand: store a value to a displacement
address, then `add` that slot into a register. The `add`'s memory read sees the
just-stored value; the addend register holds its initial value.
-/
import Kraken.Tactics
open Std.Internal.Do
open Kraken

set_option mvcgen.warning false
set_option grind.warning false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

-- movq $42, 136(%rdx); addq 136(%rdx), %rcx   (with %rcx = 100 on entry)
def aluMemProg : X64M Unit := do
  Op.movMI (Addr.mk .rdx none 136) 42
  Op.addRM .rcx (Addr.mk .rdx none 136)

theorem alu_mem_correct (s₀ : MachineData) (v : Int)
    (h_rcx : (s₀.regs.get64 .rcx).toBitVec = 100#64)
    (h_mapped : Mem.loadInt s₀.dmem ((Addr.mk .rdx none 136).eval s₀.regs) 8 = some v)
    (h_back : Mem.loadInt
        (Mem.storeInt s₀.dmem ((Addr.mk .rdx none 136).eval s₀.regs) 8
          (BitVec.setWidth 64 ((42 : Int64)).toBitVec).toInt)
        ((Addr.mk .rdx none 136).eval s₀.regs) 8 = some 42) :
    ⦃fun sd => sd = s₀⦄ aluMemProg
      ⦃fun _ s => s.regs.rcx = BitVec.ofInt 64 142⦄ := by
  have h42 : (BitVec.setWidth 64 ((42 : Int64)).toBitVec).toInt = 42 := by decide
  sym =>
    vcgen [aluMemProg]
    all_goals (first (easm) (skip))
    all_goals finish (splits := 40)
