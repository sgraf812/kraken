/-
Register decrement chain: `n` decrements of `rax` from a concrete start.

Ground values throughout, so the discharge folds constants at every step.
Contrast `AddChain`, whose initial value is symbolic.
-/
import Kraken.Specs

open Std.Internal.Do

namespace DecChain

def chain : Nat → X64M Unit
  | 0 => pure ()
  | n+1 => do Op.decR .rax; chain n

def Goal (n : Nat) : Prop :=
  ⦃fun s => s.regs.get64 .rax = BitVec.ofNat 64 n⦄ chain n ⦃fun _ s => s.regs.get64 .rax = 0#64⦄

end DecChain
