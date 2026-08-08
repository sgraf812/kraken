/-
Carry chain on the deep embedding: `n` add-with-carry directives stepped by
the segment weakest-precondition specs of Kraken/SegmentWP.lean. The program,
the prefix and the postcondition mirror `AdcChain`, so the two report the
stepping cost of the same verification through the two encodings.
-/
import Kraken.SegmentWP

open Std.Internal.Do

namespace SegAdcChain

def chain : Nat → List (Directive × Nat)
  | 0 => []
  | n + 1 =>
    (Directive.instr (.regular .W64 .W64
      (.adc (.reg (.low .rax .W64)) (.regOrMem (.reg (.low .rbx .W64))))), 4) :: chain n

def prog (n : Nat) : List (Directive × Nat) :=
  (Directive.instr (.regular .W64 .W64
      (.mov (.reg (.low .rax .W64)) (.imm (.int64 0)))), 4)
    :: (Directive.instr (.regular .W64 .W64
      (.add (.reg (.low .rax .W64)) (.imm (.int64 0)))), 4)   -- clears the carry
    :: (Directive.instr (.regular .W64 .W64
      (.mov (.reg (.low .rbx .W64)) (.imm (.int64 3)))), 4)
    :: chain n

def Goal (n : Nat) : Prop :=
  ⦃ fun _ _ => True ⦄
  prog n
  ⦃ fun _ _ st => st.1.regs.get64 .rax = BitVec.ofNat 64 (3 * n) ⦄

end SegAdcChain
