/-
A carry chain with a conditional exit after each step: `add $0, %rax`
followed by `n` copies of `adc %rbx, %rax; jz out`, on symbolic registers.
Each `jz` exits at `out` exactly when the sum is zero, so the exit post
`rax = 0` gives one verification condition per step.
-/
module

public import Kraken.StateCfg

open Std.WP
open scoped Program.WP

namespace CarryJumps

@[expose] public def chain : Nat → Program
  | 0 => []
  | n + 1 =>
    Directive.instr (.regular .W64 .W64
      (.adc (.reg (.low .rax .W64)) (.regOrMem (.reg (.low .rbx .W64)))))
    :: Directive.instr (.regular .W64 .W64 (.jcc .z "out")) :: chain n

@[expose] public def prog (n : Nat) : Program :=
  Directive.instr (.regular .W64 .W64
      (.add (.reg (.low .rax .W64)) (.imm (.int64 0))))
    :: chain n

@[expose] public def Goal (n : Nat) : Prop :=
  ∀ [Host] [FunDecls],
    Triple (prog n) (fun (_ : MachineData) => True)
      (fun (_ : Unit) (_ : MachineData) => True)
      (fun (_ : Int64) (s' : MachineData) => s'.regs.rax = 0)

end CarryJumps
