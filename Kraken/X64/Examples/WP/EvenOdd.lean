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

def evenOddProg : Program := parse("
start:
  call even
  jmp done
") ++ even ++ odd ++ parse("
done:
  nop
")

theorem evenOdd_correct [Host] (hp : evenOddProg.IsInfix Host.prog)
    (hne : label "even" ≠ label "odd") (s : MachineData) (base : BitVec 64) (sz : Nat)
    (hstack : 8 * (s.regs.rdi.toBitVec.toNat + 1) ≤ (s.regs.rsp.toBitVec - base).toNat)
    (hsz : (s.regs.rsp.toBitVec - base).toNat ≤ sz) (hmap : Mem.Mapped [(base, sz)] s.dmem) :
    Eventually (step1 Host.exe)
      (fun st => st.data.regs.rax.toBitVec.toNat = (s.regs.rdi.toBitVec.toNat + 1) % 2)
      ⟨s, startAddr hp⟩ := by
  have hk := List.isInfixAt_infixIdx hp
  generalize evenOddProg.infixIdx Host.prog hp = k at hk
  have hev : even.IsInfixAt Host.prog (k + 3) :=
    List.IsInfixAt.trans (⟨_, rfl⟩ : even.IsInfixAt evenOddProg 3) hk
  have hod : odd.IsInfixAt Host.prog (k + 12) :=
    List.IsInfixAt.trans (⟨_, rfl⟩ : odd.IsInfixAt evenOddProg 12) hk
  letI : Embeds even := ⟨⟨k + 3, hev⟩⟩
  letI : Embeds odd := ⟨⟨k + 12, hod⟩⟩
  letI : FunDecls := ⟨[Fragment.mk even, Fragment.mk odd]⟩
  have hse : (Fragment.mk even).startAddr = label "even" := (Host.label_eq (i := 0) hev rfl).symm
  have hso : (Fragment.mk odd).startAddr = label "odd" := (Host.label_eq (i := 0) hod rfl).symm
  have he : FunDecls.at (label "even") = some (Fragment.mk even) := by
    show List.find? _ [_, _] = _
    simp [hse]
  have ho : FunDecls.at (label "odd") = some (Fragment.mk odd) := by
    show List.find? _ [_, _] = _
    simp [hse, hso, hne]
  apply Program.WP.step1_of_wp hp
  refine Triple.le_wp (Program.Triple.cfg (P := (· = s)) (fun _ l s' => match l with
      | "start" => s' = s
      | "done" => s'.regs.rax.toBitVec.toNat = (s.regs.rdi.toBitVec.toNat + 1) % 2
      | _ => False)
    (fun _ _ _ => 0) fun _ h₀ => ?_) s rfl
  subst h₀
  cfg_cases
  all_goals kvcgen64 [even_spec he ho base sz] with finish

end State.EvenOdd
