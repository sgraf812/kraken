/-
Two adjacent heap slots: store `rax` at `(rdi)` and `rcx` at `8(rdi)`, then read
them back into `r12` and `r13`. The base register `rdi` is never written, so the
second slot's address is the same whether evaluated before or after `r12` is
loaded; that address equality is supplied as `ha8'`. The reads see the stored
register bits, with the read of the first slot passing the disjoint second store.
-/
import Kraken.Tactics
open Std.Internal.Do
open Kraken

set_option mvcgen.warning false
set_option grind.warning false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

def move2Prog : X64M Unit := do
  Op.movMR (Addr.mk .rdi none 0) .rax
  Op.movMR (Addr.mk .rdi none 8) .rcx
  Op.movRM .r12 (Addr.mk .rdi none 0)
  Op.movRM .r13 (Addr.mk .rdi none 8)

theorem move2_correct (s₀ : MachineData)
    (a0 a8 : BitVec 64)
    (ha0 : (Addr.mk .rdi none 0).eval s₀.regs = a0)
    (ha8 : (Addr.mk .rdi none 8).eval s₀.regs = a8)
    (ha8' : (Addr.mk .rdi none 8).eval
        (s₀.regs.set64 .r12 (.ofBitVec (BitVec.ofInt 64 (s₀.regs.get64 .rax).toBitVec.toInt))) = a8)
    (v0 v8 : Int)
    (h_map0 : Mem.loadInt s₀.dmem a0 8 = some v0)
    (h_map8 : Mem.loadInt (Mem.storeInt s₀.dmem a0 8 (s₀.regs.get64 .rax).toBitVec.toInt) a8 8 = some v8)
    (h_load0 : Mem.loadInt
        (Mem.storeInt (Mem.storeInt s₀.dmem a0 8 (s₀.regs.get64 .rax).toBitVec.toInt) a8 8
          (s₀.regs.get64 .rcx).toBitVec.toInt) a0 8 = some (s₀.regs.get64 .rax).toBitVec.toInt)
    (h_load8 : Mem.loadInt
        (Mem.storeInt (Mem.storeInt s₀.dmem a0 8 (s₀.regs.get64 .rax).toBitVec.toInt) a8 8
          (s₀.regs.get64 .rcx).toBitVec.toInt) a8 8 = some (s₀.regs.get64 .rcx).toBitVec.toInt) :
    ⦃fun sd => sd = s₀⦄ move2Prog
      ⦃fun _ s => (s.regs.get64 .r12).toBitVec = (s₀.regs.get64 .rax).toBitVec ∧
        (s.regs.get64 .r13).toBitVec = (s₀.regs.get64 .rcx).toBitVec ∧
        s.regs.rdi = s₀.regs.rdi⦄ := by
  sym =>
    vcgen [move2Prog]
    all_goals (first (easm) (skip))
    all_goals finish (splits := 40)
