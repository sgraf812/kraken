/-
Carry chain: `n` add-with-carry steps of `rbx` into `rax`.

Each step reads the carry the previous one wrote, so the flag equations are
live and the discharge has to fold a chain of them. The prefix clears the
carry so the result is determined.
-/
import Kraken.Specs

open Std.Internal.Do

namespace AdcChain

def chain : Nat → X64M Unit
  | 0 => pure ()
  | n+1 => do Op.adcRR .rax .rbx; chain n

def prog (n : Nat) : X64M Unit := do
  Op.movRI .rax 0
  Op.addRI .rax 0   -- clears the carry
  Op.movRI .rbx 3
  chain n

def Goal (n : Nat) : Prop :=
  ⦃fun _ => True⦄ prog n ⦃fun _ s => s.regs.get64 .rax = BitVec.ofNat 64 (3*n)⦄

end AdcChain
