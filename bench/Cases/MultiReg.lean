/-
Multi-register chain: `n` rounds writing all fifteen general-purpose
registers, with a postcondition that reads every one of them.

Each round rewrites the same constants, so the final state is reached after
one round; what grows with `n` is the number of write equations the discharge
must look through per queried register.
-/
import Kraken.Specs

open Std.Internal.Do

namespace MultiReg

def round : X64M Unit := do
  Op.movRI .rax 1; Op.movRI .rbx 2; Op.movRI .rcx 3; Op.movRI .rdx 4
  Op.movRI .rsi 5; Op.movRI .rdi 6; Op.movRI .rbp 7; Op.movRI .r8 8
  Op.movRI .r9 9; Op.movRI .r10 10; Op.movRI .r11 11; Op.movRI .r12 12
  Op.movRI .r13 13; Op.movRI .r14 14; Op.movRI .r15 15

def chain : Nat → X64M Unit
  | 0 => pure ()
  | n+1 => do round; chain n

def Goal (n : Nat) : Prop :=
  ⦃fun _ => True⦄ chain (n+1) ⦃fun _ s =>
    s.regs.get64 .rax = 1#64 ∧ s.regs.get64 .rbx = 2#64 ∧ s.regs.get64 .rcx = 3#64 ∧
    s.regs.get64 .rdx = 4#64 ∧ s.regs.get64 .rsi = 5#64 ∧ s.regs.get64 .rdi = 6#64 ∧
    s.regs.get64 .rbp = 7#64 ∧ s.regs.get64 .r8 = 8#64 ∧ s.regs.get64 .r9 = 9#64 ∧
    s.regs.get64 .r10 = 10#64 ∧ s.regs.get64 .r11 = 11#64 ∧ s.regs.get64 .r12 = 12#64 ∧
    s.regs.get64 .r13 = 13#64 ∧ s.regs.get64 .r14 = 14#64 ∧ s.regs.get64 .r15 = 15#64⦄

end MultiReg
