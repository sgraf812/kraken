/-
Register add chain: `n` immediate adds to `rax`, with a symbolic initial value.

The program is a recursive function of `n`, so a benchmark run elaborates and
compiles a fixed amount of source no matter the size, and the driver reports
stepping, discharge and kernel time separately.
-/
import Kraken.Specs
import Std.Tactic.BVDecide

open Std.Internal.Do

namespace AddChain

def chain : Nat → X64M Unit
  | 0 => pure ()
  | n+1 => do Op.addRI .rax 3; chain n

def Goal (n : Nat) : Prop :=
  ∀ k : BitVec 64,
    ⦃fun s => s.regs.get64 .rax = k⦄ chain n ⦃fun _ s => s.regs.get64 .rax = k + BitVec.ofNat 64 (3*n)⦄

end AddChain
