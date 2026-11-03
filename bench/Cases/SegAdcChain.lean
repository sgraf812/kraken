/-
Carry chain on the deep embedding: `n` add-with-carry instructions stepped by
the directive specs of `Program.WP`. The chain holds no label, so the goal
holds under every host and every function table.
-/
module

public import Kraken.StateCfg

open Std.WP
open scoped Program.WP

namespace SegAdcChain

@[expose] public def chain : Nat → Program
  | 0 => []
  | n + 1 =>
    Directive.instr (.regular .W64 .W64
      (.adc (.reg (.low .rax .W64)) (.regOrMem (.reg (.low .rbx .W64))))) :: chain n

@[expose] public def prog (n : Nat) : Program :=
  Directive.instr (.regular .W64 .W64
      (.mov (.reg (.low .rax .W64)) (.imm (.int64 0))))
    :: Directive.instr (.regular .W64 .W64
      (.add (.reg (.low .rax .W64)) (.imm (.int64 0))))   -- clears the carry
    :: Directive.instr (.regular .W64 .W64
      (.mov (.reg (.low .rbx .W64)) (.imm (.int64 3))))
    :: chain n

@[expose] public def Goal (n : Nat) : Prop :=
  ∀ [Host] [FunDecls],
    Triple (prog n) (fun (_ : MachineData) => True)
      (fun (_ : Unit) (s' : MachineData) => s'.regs.rax.toNat = 3 * n)
      (fun (_ : Int64) (_ : MachineData) => False)

end SegAdcChain
