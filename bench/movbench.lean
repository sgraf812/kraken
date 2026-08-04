/-
The immediate-mov chain on X64MNew, stepped and discharged. Each state read is
projected through the `Sys` wrapper the framework adds.
-/
import Kraken.X64MNew
import KrakenTactics.Fold
import Std.Tactic.BVDecide
import Driver

open Std.Internal.Do Kraken Lean Order Parser Meta Elab Tactic Sym

set_option mvcgen.warning false
set_option grind.warning false
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

namespace MovChain
def chain : Nat → X64MNew Unit Unit
  | 0 => pure ()
  | n+1 => do Op.mov (.reg (.low .rax .W64)) (.imm (.int64 1)); chain n
def Goal (n : Nat) : Prop :=
  ⦃fun _ _ _ => True⦄ chain (n+1)
    ⦃fun _ _ _ s => s.machine.regs.get64 .rax = .ofBitVec (BitVec.setWidth 64 (1 : Int64).toBitVec);
      fun _ _ => True⦄
end MovChain

#eval IO.println "=== MovChain (X64MNew): prefix(n): STEPPING ms, ..., kernel: K ms ==="
#eval runBenchUsingTactic ``MovChain.Goal [``MovChain.chain]
  `(tactic| vcgen -internalize simplifying_assumptions) `(tactic| grind) [40, 160]
