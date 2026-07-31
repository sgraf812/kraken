/-
Register swap through three `xor`s: with the source and destination exchanged on
the middle instruction, the pair ends holding each other's initial value.
-/
import Kraken.Tactics
import Std.Tactic.BVDecide

open Std.Internal.Do
open Kraken

set_option mvcgen.warning false
set_option grind.warning false
set_option maxHeartbeats 1000000

def swapProg : X64M Unit := do
  Op.xorRR .rax .rbx
  Op.xorRR .rbx .rax
  Op.xorRR .rax .rbx

theorem swap_correct (a b : BitVec 64) :
    ⦃fun s => s.regs.get64 .rax = a ∧ s.regs.get64 .rbx = b⦄
      swapProg
      ⦃fun _ s => s.regs.get64 .rax = b ∧ s.regs.get64 .rbx = a⦄ := by
  sym =>
    vcgen [swapProg]
    all_goals finish (splits := 40)
