/-
Carry chain on the deep embedding: `n` add-with-carry instructions stepped by
the run weakest-precondition specs of Kraken/SegmentWP.lean. The program, the
prefix and the postcondition mirror `AdcChain`, so the two report the stepping
cost of the same verification through the two encodings.
-/
import Kraken.SegmentWP

open Std.Internal.Do
open Program.ClosedWP

namespace SegAdcChain

def chain : Nat → Program
  | 0 => []
  | n + 1 =>
    Directive.instr (.regular .W64 .W64
      (.adc (.reg (.low .rax .W64)) (.regOrMem (.reg (.low .rbx .W64))))) :: chain n

def prog (n : Nat) : Program :=
  Directive.instr (.regular .W64 .W64
      (.mov (.reg (.low .rax .W64)) (.imm (.int64 0))))
    :: Directive.instr (.regular .W64 .W64
      (.add (.reg (.low .rax .W64)) (.imm (.int64 0))))   -- clears the carry
    :: Directive.instr (.regular .W64 .W64
      (.mov (.reg (.low .rbx .W64)) (.imm (.int64 3))))
    :: chain n

def Goal (n : Nat) : Prop :=
  ⦃ fun _ => True ⦄
  prog n
  ⦃ fun _ s => s.regs.get64 .rax = BitVec.ofNat 64 (3 * n) ⦄

end SegAdcChain
