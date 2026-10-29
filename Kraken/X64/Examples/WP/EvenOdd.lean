module

public import Kraken.StateCfg
public import Kraken.SeparationMem
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

abbrev even_spec.Frame (s s' : MachineData) : Prop :=
  s'.regs.rbx = s.regs.rbx ∧ s'.regs.rcx = s.regs.rcx ∧ s'.regs.rdx = s.regs.rdx ∧ s'.regs.rsi = s.regs.rsi
    ∧ s'.regs.rbp = s.regs.rbp ∧ s'.regs.r8 = s.regs.r8 ∧ s'.regs.r9 = s.regs.r9
    ∧ s'.regs.r10 = s.regs.r10 ∧ s'.regs.r11 = s.regs.r11 ∧ s'.regs.r12 = s.regs.r12
    ∧ s'.regs.r13 = s.regs.r13 ∧ s'.regs.r14 = s.regs.r14 ∧ s'.regs.r15 = s.regs.r15
    ∧ Mem.WritesOnly [Mem.Block.ofStackSlots s.regs.rsp s.regs.rdi.toBitVec.toNat] s.dmem s'.dmem

abbrev odd_spec.Frame (s s' : MachineData) : Prop :=
  s'.regs.rbx = s.regs.rbx ∧ s'.regs.rcx = s.regs.rcx ∧ s'.regs.rdx = s.regs.rdx ∧ s'.regs.rsi = s.regs.rsi
    ∧ s'.regs.rbp = s.regs.rbp ∧ s'.regs.r8 = s.regs.r8 ∧ s'.regs.r9 = s.regs.r9
    ∧ s'.regs.r10 = s.regs.r10 ∧ s'.regs.r11 = s.regs.r11 ∧ s'.regs.r12 = s.regs.r12
    ∧ s'.regs.r13 = s.regs.r13 ∧ s'.regs.r14 = s.regs.r14 ∧ s'.regs.r15 = s.regs.r15
    ∧ Mem.WritesOnly [Mem.Block.ofStackSlots s.regs.rsp s.regs.rdi.toBitVec.toNat] s.dmem s'.dmem

abbrev Spec [Host] [FunDecls] (f : Label) (r : Nat) (Fr : MachineData → MachineData → Prop)
    (base : BitVec 64) (sz : Nat) (G : MachineData → Prop) : Prop :=
  ∀ s ra (Q' : Unit → MachineData → Prop) (E' : Int64 → MachineData → Prop),
    ⦃ fun s₀ => s₀ = s.push64 ra ∧ G s
        ∧ (8 * (s.regs.rdi.toBitVec.toNat + 1) ≤ (s.regs.rsp.toBitVec - base).toNat
          ∧ (s.regs.rsp.toBitVec - base).toNat ≤ sz ∧ Mem.Mapped [(base, sz)] s.dmem)
        ∧ (∀ s', s'.regs.rax.toBitVec.toNat = (s.regs.rdi.toBitVec.toNat + r) % 2 ∧ s'.regs.rsp = s.regs.rsp ∧ Fr s s' → E' ra s')
        ∧ (∀ a s', a ≠ ra → False ∧ Fr s s' → E' a s') ⦄
      FunDecls.body f
    ⦃ Q'; E' ⦄

theorem evenOdd_spec [Host] [FunDecls] [Embeds even] [Embeds odd]
    (he : FunDecls.at (label "even") = some ⟨even⟩) (ho : FunDecls.at (label "odd") = some ⟨odd⟩)
    (base : BitVec 64) (sz : Nat) (n : Nat) :
    Spec "even" 1 even_spec.Frame base sz (fun s => s.regs.rdi.toBitVec.toNat = n)
      ∧ Spec "odd" 0 odd_spec.Frame base sz (fun s => s.regs.rdi.toBitVec.toNat = n) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  have hodd : Spec "odd" 0 odd_spec.Frame base sz (fun s => s.regs.rdi.toBitVec.toNat < n) :=
    fun s ra Q' E' => ⟨fun s₀ ⟨h₀, hlt, hp⟩ => ((ih _ hlt).2 s ra Q' E').1 s₀ ⟨h₀, rfl, hp⟩⟩
  have heven : Spec "even" 1 even_spec.Frame base sz (fun s => s.regs.rdi.toBitVec.toNat < n) :=
    fun s ra Q' E' => ⟨fun s₀ ⟨h₀, hlt, hp⟩ => ((ih _ hlt).1 s ra Q' E').1 s₀ ⟨h₀, rfl, hp⟩⟩
  have hcodd := Program.WP.call_spec ho
  have hceven := Program.WP.call_spec he
  clear ih
  have keven : ∀ s ra, s.regs.rdi.toBitVec.toNat = n
      → 8 * (s.regs.rdi.toBitVec.toNat + 1) ≤ (s.regs.rsp.toBitVec - base).toNat
        ∧ (s.regs.rsp.toBitVec - base).toNat ≤ sz ∧ Mem.Mapped [(base, sz)] s.dmem
      → WP.wp even (fun _ _ => False) (fun a s' => a = ra
        ∧ s'.regs.rax.toBitVec.toNat = (s.regs.rdi.toBitVec.toNat + 1) % 2 ∧ s'.regs.rsp = s.regs.rsp ∧ even_spec.Frame s s') (s.push64 ra) := by
    intro s ra hn _
    subst hn
    refine Program.WP.cfg (fun
        | .entry, s' | .label "even", s' => s' = s.push64 ra
        | .label _, s' => s'.regs = (s.push64 ra).regs ∧ s'.dmem = (s.push64 ra).dmem
            ∧ s.regs.rdi.toBitVec.toNat = 0
        | .exit, _ => False)
      (fun _ _ => 0) ?_ rfl
    cfg_cases
    all_goals kvcgen64 [hcodd, hodd] with finish
  have kodd : ∀ s ra, s.regs.rdi.toBitVec.toNat = n
      → 8 * (s.regs.rdi.toBitVec.toNat + 1) ≤ (s.regs.rsp.toBitVec - base).toNat
        ∧ (s.regs.rsp.toBitVec - base).toNat ≤ sz ∧ Mem.Mapped [(base, sz)] s.dmem
      → WP.wp odd (fun _ _ => False) (fun a s' => a = ra
        ∧ s'.regs.rax.toBitVec.toNat = (s.regs.rdi.toBitVec.toNat + 0) % 2 ∧ s'.regs.rsp = s.regs.rsp ∧ odd_spec.Frame s s') (s.push64 ra) := by
    intro s ra hn _
    subst hn
    refine Program.WP.cfg (fun
        | .entry, s' | .label "odd", s' => s' = s.push64 ra
        | .label _, s' => s'.regs = (s.push64 ra).regs ∧ s'.dmem = (s.push64 ra).dmem
            ∧ s.regs.rdi.toBitVec.toNat = 0
        | .exit, _ => False)
      (fun _ _ => 0) ?_ rfl
    cfg_cases
    all_goals kvcgen64 [hceven, heven] with finish
  refine ⟨fun s ra Q' E' => ⟨fun s₀ ⟨h₀, hn, hpre, hok, _⟩ => ?_⟩,
    fun s ra Q' E' => ⟨fun s₀ ⟨h₀, hn, hpre, hok, _⟩ => ?_⟩⟩ <;> subst h₀
  · rw [FunDecls.body_eq he]
    exact Program.wp_mono (fun _ h => False.elim h) (fun u hu => hu.1 ▸ hok u.data hu.2) (keven s ra hn hpre)
  · rw [FunDecls.body_eq ho]
    exact Program.wp_mono (fun _ h => False.elim h) (fun u hu => hu.1 ▸ hok u.data hu.2) (kodd s ra hn hpre)

theorem even_spec [Host] [FunDecls] [Embeds even] [Embeds odd]
    (he : FunDecls.at (label "even") = some ⟨even⟩) (ho : FunDecls.at (label "odd") = some ⟨odd⟩)
    (base : BitVec 64) (sz : Nat) :
    ∀ s ra (Q' : Unit → MachineData → Prop) (E' : Int64 → MachineData → Prop),
      ⦃ fun s₀ => s₀ = s.push64 ra
          ∧ (8 * (s.regs.rdi.toBitVec.toNat + 1) ≤ (s.regs.rsp.toBitVec - base).toNat
            ∧ (s.regs.rsp.toBitVec - base).toNat ≤ sz ∧ Mem.Mapped [(base, sz)] s.dmem)
          ∧ (∀ s', s'.regs.rax.toBitVec.toNat = (s.regs.rdi.toBitVec.toNat + 1) % 2 ∧ s'.regs.rsp = s.regs.rsp ∧ even_spec.Frame s s' → E' ra s')
          ∧ (∀ a s', a ≠ ra → False ∧ even_spec.Frame s s' → E' a s') ⦄
        FunDecls.body "even"
      ⦃ Q'; E' ⦄ :=
  fun s ra Q' E' => ⟨fun s₀ ⟨h₀, hp, hq, hx⟩ =>
    ((evenOdd_spec he ho base sz s.regs.rdi.toBitVec.toNat).1 s ra Q' E').1 s₀ ⟨h₀, rfl, hp, hq, hx⟩⟩

theorem odd_spec [Host] [FunDecls] [Embeds even] [Embeds odd]
    (he : FunDecls.at (label "even") = some ⟨even⟩) (ho : FunDecls.at (label "odd") = some ⟨odd⟩)
    (base : BitVec 64) (sz : Nat) :
    ∀ s ra (Q' : Unit → MachineData → Prop) (E' : Int64 → MachineData → Prop),
      ⦃ fun s₀ => s₀ = s.push64 ra
          ∧ (8 * (s.regs.rdi.toBitVec.toNat + 1) ≤ (s.regs.rsp.toBitVec - base).toNat
            ∧ (s.regs.rsp.toBitVec - base).toNat ≤ sz ∧ Mem.Mapped [(base, sz)] s.dmem)
          ∧ (∀ s', s'.regs.rax.toBitVec.toNat = (s.regs.rdi.toBitVec.toNat) % 2 ∧ s'.regs.rsp = s.regs.rsp ∧ odd_spec.Frame s s' → E' ra s')
          ∧ (∀ a s', a ≠ ra → False ∧ odd_spec.Frame s s' → E' a s') ⦄
        FunDecls.body "odd"
      ⦃ Q'; E' ⦄ :=
  fun s ra Q' E' => ⟨fun s₀ ⟨h₀, hp, hq, hx⟩ =>
    ((evenOdd_spec he ho base sz s.regs.rdi.toBitVec.toNat).2 s ra Q' E').1 s₀ ⟨h₀, rfl, hp, hq, hx⟩⟩

end State.EvenOdd
