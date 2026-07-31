/-
Register add chain against the let-form specs: `n` immediate adds to `rax`,
with a symbolic initial value. Same program and postcondition as `AddChain`,
stepped with `OpL.addRI_spec_let` instead of the accessor triple.
-/
import KrakenTactics.LetSpecs
import Std.Tactic.BVDecide

open Std.Internal.Do

namespace AddChainLet

def chain : Nat → X64M Unit
  | 0 => pure ()
  | n+1 => do OpL.addRI .rax 3; chain n

def Goal (n : Nat) : Prop :=
  ∀ k : BitVec 64,
    ⦃fun s => s.regs.get64 .rax = k⦄ chain n ⦃fun _ s => s.regs.get64 .rax = k + BitVec.ofNat 64 (3*n)⦄

end AddChainLet
