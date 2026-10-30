module

public import Kraken.StateCfg
public import Kraken.SeparationMem
import Kraken.FunSpec
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace State.EvenOdd

def even : Program := parse("
even:
  test %rdi, %rdi
  jz even_zero
  dec %rdi
  call odd
  ret
even_zero:
  mov $1, %rax
  ret
")

def odd : Program := parse("
odd:
  test %rdi, %rdi
  jz odd_zero
  dec %rdi
  call even
  ret
odd_zero:
  mov $0, %rax
  ret
")

mutual

funspec even_spec "even" [Host] [FunDecls] [Embeds even] [Embeds odd]
    (he : FunDecls.at (label "even") = some ⟨even⟩) (ho : FunDecls.at (label "odd") = some ⟨odd⟩)
    (base : BitVec 64) (sz : Nat) at s
    requires 8 * (s.regs.rdi.toBitVec.toNat + 1) ≤ (s.regs.rsp.toBitVec - base).toNat
      ∧ (s.regs.rsp.toBitVec - base).toNat ≤ sz ∧ Mem.Mapped [(base, sz)] s.dmem
    ensures s' => s'.regs.rax.toBitVec.toNat = (s.regs.rdi.toBitVec.toNat + 1) % 2
    autoframes calling_conv SysV reserve s.regs.rdi.toBitVec.toNat
      preserves rcx rdx rsi r8 r9 r10 r11 := by
  refine Program.Triple.cfg
    (fun s₀ => fun
      | "even", s' => s' = s₀
      | _, s' => s'.regs = s₀.regs ∧ s'.dmem = s₀.dmem ∧ s.regs.rdi.toBitVec.toNat = 0)
    (fun _ _ _ => 0) fun s₀ ⟨h₀, _⟩ => ?_
  cfg_cases
  all_goals kvcgen64 [odd_spec] with finish
termination_by s.regs.rdi.toBitVec.toNat

funspec odd_spec "odd" [Host] [FunDecls] [Embeds even] [Embeds odd]
    (he : FunDecls.at (label "even") = some ⟨even⟩) (ho : FunDecls.at (label "odd") = some ⟨odd⟩)
    (base : BitVec 64) (sz : Nat) at s
    requires 8 * (s.regs.rdi.toBitVec.toNat + 1) ≤ (s.regs.rsp.toBitVec - base).toNat
      ∧ (s.regs.rsp.toBitVec - base).toNat ≤ sz ∧ Mem.Mapped [(base, sz)] s.dmem
    ensures s' => s'.regs.rax.toBitVec.toNat = s.regs.rdi.toBitVec.toNat % 2
    autoframes calling_conv SysV reserve s.regs.rdi.toBitVec.toNat
      preserves rcx rdx rsi r8 r9 r10 r11 := by
  refine Program.Triple.cfg
    (fun s₀ => fun
      | "odd", s' => s' = s₀
      | _, s' => s'.regs = s₀.regs ∧ s'.dmem = s₀.dmem ∧ s.regs.rdi.toBitVec.toNat = 0)
    (fun _ _ _ => 0) fun s₀ ⟨h₀, _⟩ => ?_
  cfg_cases
  all_goals kvcgen64 [even_spec] with finish
termination_by s.regs.rdi.toBitVec.toNat

end

end State.EvenOdd
