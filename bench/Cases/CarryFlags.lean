/-
Flags of a carry chain on symbolic registers: `add $0, %rax` followed by `n`
copies of `adc %rbx, %rax`, with a post that ties the zero and sign flags of the
last `adc` to the final `rax`. Both flags and `rax` come from the same sum, so
each step leaves the flags and the register as terms over the start state.
-/
module

public import Cases.AdcChain

open Std.WP
open scoped Program.WP

namespace CarryFlags

@[expose] public def prog (n : Nat) : Program :=
  Directive.instr (.regular .W64 .W64
      (.add (.reg (.low .rax .W64)) (.imm (.int64 0))))
    :: AdcChain.chain n

@[expose] public def Goal (n : Nat) : Prop :=
  ∀ [Host] [FunDecls],
    Triple (prog n) (fun (_ : MachineData) => True)
      (fun (_ : Unit) (s' : MachineData) =>
        (s'.status.zf = true ↔ s'.regs.rax = 0) ∧ s'.status.sf = s'.regs.rax.toBitVec.msb)
      (fun (_ : Int64) (_ : MachineData) => False)

end CarryFlags
