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

abbrev even_spec.Frame (c t : MachineData) : Prop :=
  t.regs.rbx = c.regs.rbx ∧ t.regs.rcx = c.regs.rcx ∧ t.regs.rdx = c.regs.rdx ∧ t.regs.rsi = c.regs.rsi
    ∧ t.regs.rbp = c.regs.rbp ∧ t.regs.r8 = c.regs.r8 ∧ t.regs.r9 = c.regs.r9
    ∧ t.regs.r10 = c.regs.r10 ∧ t.regs.r11 = c.regs.r11 ∧ t.regs.r12 = c.regs.r12
    ∧ t.regs.r13 = c.regs.r13 ∧ t.regs.r14 = c.regs.r14 ∧ t.regs.r15 = c.regs.r15
    ∧ Mem.WritesOnly [Mem.Block.ofStackSlots c.regs.rsp c.regs.rdi.toBitVec.toNat] c.dmem t.dmem

abbrev odd_spec.Frame (c t : MachineData) : Prop :=
  t.regs.rbx = c.regs.rbx ∧ t.regs.rcx = c.regs.rcx ∧ t.regs.rdx = c.regs.rdx ∧ t.regs.rsi = c.regs.rsi
    ∧ t.regs.rbp = c.regs.rbp ∧ t.regs.r8 = c.regs.r8 ∧ t.regs.r9 = c.regs.r9
    ∧ t.regs.r10 = c.regs.r10 ∧ t.regs.r11 = c.regs.r11 ∧ t.regs.r12 = c.regs.r12
    ∧ t.regs.r13 = c.regs.r13 ∧ t.regs.r14 = c.regs.r14 ∧ t.regs.r15 = c.regs.r15
    ∧ Mem.WritesOnly [Mem.Block.ofStackSlots c.regs.rsp c.regs.rdi.toBitVec.toNat] c.dmem t.dmem

abbrev Spec [Host] [FunDecls] (f : Label) (r : Nat) (Fr : MachineData → MachineData → Prop)
    (base : BitVec 64) (sz : Nat) (G : MachineData → Prop) : Prop :=
  ∀ c ra (Q' : Unit → MachineData → Prop) (E' : Int64 → MachineData → Prop),
    ⦃ fun s => s = c.push64 ra ∧ G c
        ∧ (8 * (c.regs.rdi.toBitVec.toNat + 1) ≤ (c.regs.rsp.toBitVec - base).toNat
          ∧ (c.regs.rsp.toBitVec - base).toNat ≤ sz ∧ Mem.Mapped [(base, sz)] c.dmem)
        ∧ (∀ t, t.regs.rax.toBitVec.toNat = (c.regs.rdi.toBitVec.toNat + r) % 2 ∧ t.regs.rsp = c.regs.rsp ∧ Fr c t → E' ra t)
        ∧ (∀ a t, a ≠ ra → False ∧ Fr c t → E' a t) ⦄
      FunDecls.body f
    ⦃ Q'; E' ⦄

theorem evenOdd_spec [Host] [FunDecls] [Embeds even] [Embeds odd]
    (he : FunDecls.at (label "even") = some ⟨even⟩) (ho : FunDecls.at (label "odd") = some ⟨odd⟩)
    (base : BitVec 64) (sz : Nat) (n : Nat) :
    Spec "even" 1 even_spec.Frame base sz (fun c => c.regs.rdi.toBitVec.toNat = n)
      ∧ Spec "odd" 0 odd_spec.Frame base sz (fun c => c.regs.rdi.toBitVec.toNat = n) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  have hodd : Spec "odd" 0 odd_spec.Frame base sz (fun c => c.regs.rdi.toBitVec.toNat < n) :=
    fun c ra Q' E' => ⟨fun s ⟨h₀, hlt, hp⟩ => ((ih _ hlt).2 c ra Q' E').1 s ⟨h₀, rfl, hp⟩⟩
  have heven : Spec "even" 1 even_spec.Frame base sz (fun c => c.regs.rdi.toBitVec.toNat < n) :=
    fun c ra Q' E' => ⟨fun s ⟨h₀, hlt, hp⟩ => ((ih _ hlt).1 c ra Q' E').1 s ⟨h₀, rfl, hp⟩⟩
  have hcodd := Program.WP.call_spec ho
  have hceven := Program.WP.call_spec he
  clear ih
  have keven : ∀ c ra, c.regs.rdi.toBitVec.toNat = n
      → 8 * (c.regs.rdi.toBitVec.toNat + 1) ≤ (c.regs.rsp.toBitVec - base).toNat
        ∧ (c.regs.rsp.toBitVec - base).toNat ≤ sz ∧ Mem.Mapped [(base, sz)] c.dmem
      → WP.wp even (fun _ _ => False) (fun a t => a = ra
        ∧ t.regs.rax.toBitVec.toNat = (c.regs.rdi.toBitVec.toNat + 1) % 2 ∧ t.regs.rsp = c.regs.rsp ∧ even_spec.Frame c t) (c.push64 ra) := by
    intro c ra hn _
    subst hn
    refine Program.WP.cfg (fun
        | .entry, t | .label "even", t => t = c.push64 ra
        | .label _, t => t.regs = (c.push64 ra).regs ∧ t.dmem = (c.push64 ra).dmem
            ∧ c.regs.rdi.toBitVec.toNat = 0
        | .exit, _ => False)
      (fun _ _ => 0) ?_ rfl
    cfg_cases
    all_goals kvcgen64 [hcodd, hodd] with finish
  have kodd : ∀ c ra, c.regs.rdi.toBitVec.toNat = n
      → 8 * (c.regs.rdi.toBitVec.toNat + 1) ≤ (c.regs.rsp.toBitVec - base).toNat
        ∧ (c.regs.rsp.toBitVec - base).toNat ≤ sz ∧ Mem.Mapped [(base, sz)] c.dmem
      → WP.wp odd (fun _ _ => False) (fun a t => a = ra
        ∧ t.regs.rax.toBitVec.toNat = (c.regs.rdi.toBitVec.toNat + 0) % 2 ∧ t.regs.rsp = c.regs.rsp ∧ odd_spec.Frame c t) (c.push64 ra) := by
    intro c ra hn _
    subst hn
    refine Program.WP.cfg (fun
        | .entry, t | .label "odd", t => t = c.push64 ra
        | .label _, t => t.regs = (c.push64 ra).regs ∧ t.dmem = (c.push64 ra).dmem
            ∧ c.regs.rdi.toBitVec.toNat = 0
        | .exit, _ => False)
      (fun _ _ => 0) ?_ rfl
    cfg_cases
    all_goals kvcgen64 [hceven, heven] with finish
  refine ⟨fun c ra Q' E' => ⟨fun s₀ ⟨h₀, hn, hpre, hok, _⟩ => ?_⟩,
    fun c ra Q' E' => ⟨fun s₀ ⟨h₀, hn, hpre, hok, _⟩ => ?_⟩⟩ <;> subst h₀
  · rw [FunDecls.body_eq he]
    exact Program.wp_mono (fun _ h => False.elim h) (fun u hu => hu.1 ▸ hok u.data hu.2) (keven c ra hn hpre)
  · rw [FunDecls.body_eq ho]
    exact Program.wp_mono (fun _ h => False.elim h) (fun u hu => hu.1 ▸ hok u.data hu.2) (kodd c ra hn hpre)

theorem even_spec [Host] [FunDecls] [Embeds even] [Embeds odd]
    (he : FunDecls.at (label "even") = some ⟨even⟩) (ho : FunDecls.at (label "odd") = some ⟨odd⟩)
    (base : BitVec 64) (sz : Nat) :
    ∀ c ra (Q' : Unit → MachineData → Prop) (E' : Int64 → MachineData → Prop),
      ⦃ fun s => s = c.push64 ra
          ∧ (8 * (c.regs.rdi.toBitVec.toNat + 1) ≤ (c.regs.rsp.toBitVec - base).toNat
            ∧ (c.regs.rsp.toBitVec - base).toNat ≤ sz ∧ Mem.Mapped [(base, sz)] c.dmem)
          ∧ (∀ t, t.regs.rax.toBitVec.toNat = (c.regs.rdi.toBitVec.toNat + 1) % 2 ∧ t.regs.rsp = c.regs.rsp ∧ even_spec.Frame c t → E' ra t)
          ∧ (∀ a t, a ≠ ra → False ∧ even_spec.Frame c t → E' a t) ⦄
        FunDecls.body "even"
      ⦃ Q'; E' ⦄ :=
  fun c ra Q' E' => ⟨fun s ⟨h₀, hp, hq, hx⟩ =>
    ((evenOdd_spec he ho base sz c.regs.rdi.toBitVec.toNat).1 c ra Q' E').1 s ⟨h₀, rfl, hp, hq, hx⟩⟩

theorem odd_spec [Host] [FunDecls] [Embeds even] [Embeds odd]
    (he : FunDecls.at (label "even") = some ⟨even⟩) (ho : FunDecls.at (label "odd") = some ⟨odd⟩)
    (base : BitVec 64) (sz : Nat) :
    ∀ c ra (Q' : Unit → MachineData → Prop) (E' : Int64 → MachineData → Prop),
      ⦃ fun s => s = c.push64 ra
          ∧ (8 * (c.regs.rdi.toBitVec.toNat + 1) ≤ (c.regs.rsp.toBitVec - base).toNat
            ∧ (c.regs.rsp.toBitVec - base).toNat ≤ sz ∧ Mem.Mapped [(base, sz)] c.dmem)
          ∧ (∀ t, t.regs.rax.toBitVec.toNat = (c.regs.rdi.toBitVec.toNat) % 2 ∧ t.regs.rsp = c.regs.rsp ∧ odd_spec.Frame c t → E' ra t)
          ∧ (∀ a t, a ≠ ra → False ∧ odd_spec.Frame c t → E' a t) ⦄
        FunDecls.body "odd"
      ⦃ Q'; E' ⦄ :=
  fun c ra Q' E' => ⟨fun s ⟨h₀, hp, hq, hx⟩ =>
    ((evenOdd_spec he ho base sz c.regs.rdi.toBitVec.toNat).2 c ra Q' E').1 s ⟨h₀, rfl, hp, hq, hx⟩⟩

end State.EvenOdd
