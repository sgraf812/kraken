import Kraken.X64MNew
import Kraken.Tactics

open Std.Internal.Do
open Kraken

set_option mvcgen.warning false
set_option grind.warning false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

def ae0 : AddrExpr := { base := some (.reg .rdi), idx := none, disp := .int64 0 }
def ae8 : AddrExpr := { base := some (.reg .rdi), idx := none, disp := .int64 8 }

def move2Prog : X64MNew Unit Unit := do
  Op.mov (.mem ae0) (.regOrMem (.reg (.low .rax .W64)))
  Op.mov (.mem ae8) (.regOrMem (.reg (.low .rcx .W64)))
  Op.mov (.reg (.low .r12 .W64)) (.regOrMem (.mem ae0))
  Op.mov (.reg (.low .r13 .W64)) (.regOrMem (.mem ae8))

theorem move2_correct (env₀ : Env) (s₀ : MachineData) (a0 a8 : BitVec 64)
    (ha0 : AddrExpr.interp env₀.labels (.mk .W64) ae0 s₀.regs (.mk 0 0) = a0)
    (ha8 : AddrExpr.interp env₀.labels (.mk .W64) ae8 s₀.regs (.mk 0 0) = a8)
    (ha8' : AddrExpr.interp env₀.labels (.mk .W64) ae8
        (s₀.regs.set64 .r12 (.ofBitVec (BitVec.ofInt 64 (s₀.regs.get64 .rax).toBitVec.toInt))) (.mk 0 0) = a8)
    (v0 v8 : Int)
    (h_map0 : Mem.loadInt s₀.dmem a0 8 = some v0)
    (h_map8 : Mem.loadInt (Mem.storeInt s₀.dmem a0 8 (s₀.regs.get64 .rax).toBitVec.toInt) a8 8 = some v8)
    (h_load0 : Mem.loadInt
        (Mem.storeInt (Mem.storeInt s₀.dmem a0 8 (s₀.regs.get64 .rax).toBitVec.toInt) a8 8
          (s₀.regs.get64 .rcx).toBitVec.toInt) a0 8 = some (s₀.regs.get64 .rax).toBitVec.toInt)
    (h_load8 : Mem.loadInt
        (Mem.storeInt (Mem.storeInt s₀.dmem a0 8 (s₀.regs.get64 .rax).toBitVec.toInt) a8 8
          (s₀.regs.get64 .rcx).toBitVec.toInt) a8 8 = some (s₀.regs.get64 .rcx).toBitVec.toInt) :
    ⦃fun env rip sd => env = env₀ ∧ rip = 0 ∧ sd = ⟨s₀, ()⟩⦄ move2Prog
      ⦃fun _ _ _ s => (s.machine.regs.get64 .r12).toBitVec = (s₀.regs.get64 .rax).toBitVec ∧
        (s.machine.regs.get64 .r13).toBitVec = (s₀.regs.get64 .rcx).toBitVec ∧
        s.machine.regs.rdi = s₀.regs.rdi; fun _ _ => True⦄ := by
  vcgen [move2Prog] with (first (easm) (skip))
  all_goals (simp_all [BitVec.ofInt_toInt] <;> bv_decide)
