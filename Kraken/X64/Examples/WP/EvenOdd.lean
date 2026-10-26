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

abbrev Pre (base : BitVec 64) (sz : Nat) (s : MachineData) : Prop :=
  8 * ((s.regs.get64 .rdi).toNat + 1) ≤ (s.regs.get64 .rsp - base).toNat
    ∧ (s.regs.get64 .rsp - base).toNat ≤ sz ∧ Mem.Mapped [(base, sz)] s.dmem

abbrev Post (base : BitVec 64) (sz r : Nat) (s t : MachineData) : Prop :=
  (t.regs.get64 .rax).toNat = ((s.regs.get64 .rdi).toNat + r) % 2 ∧ Mem.Mapped [(base, sz)] t.dmem

abbrev mod (base : BitVec 64) (s : MachineData) : Modifies :=
  ⟨[.rax, .rdi], [(base, (s.regs.get64 .rsp - base).toNat)]⟩

abbrev Spec [Host] [FunDecls] (p : Program) (base : BitVec 64) (sz r : Nat) (s : MachineData)
    (ra : Int64) : Prop :=
  ⦃ fun t => t = s.pushRa ra ∧ Pre base sz s ⦄ p
    ⦃ (fun _ _ => False); fun a t => a = ra ∧ Post base sz r s t ∧ (mod base s).Agree s t ⦄

theorem evenOdd_spec [Host] [FunDecls] [Embeds even] [Embeds odd]
    (he : FunDecls.at (label "even") = some ⟨even⟩) (ho : FunDecls.at (label "odd") = some ⟨odd⟩)
    (base : BitVec 64) (sz : Nat) (s : MachineData) (ra : Int64) :
    Spec even base sz 1 s ra ∧ Spec odd base sz 0 s ra := by
  induction h : (s.regs.get64 .rdi).toNat using Nat.strongRecOn generalizing s ra with
  | _ n ih =>
  have hcall {f : Label} {p : Program} [Embeds p] (hf : FunDecls.at (label f) = some ⟨p⟩) {r : Nat}
      (hs : ∀ s ra, (s.regs.get64 .rdi).toNat < n → Spec p base sz r s ra) :
      Program.WP.CallSpec f (fun t => (t.regs.get64 .rdi).toNat < n ∧ Pre base sz t)
        (Post base sz r) (mod base) :=
    Program.WP.callSpec_of_triple hf fun t ra => ⟨fun t₀ ⟨h₀, hlt, hp⟩ => (hs t ra hlt).1 t₀ ⟨h₀, hp⟩⟩
  have hodd := hcall ho fun t ra hlt => (ih _ hlt t ra rfl).2
  have heven := hcall he fun t ra hlt => (ih _ hlt t ra rfl).1
  clear hcall ih
  refine ⟨⟨fun s₀ ⟨h₀, _⟩ => ?_⟩, ⟨fun s₀ ⟨h₀, _⟩ => ?_⟩⟩ <;> subst h₀
  · refine Program.WP.cfg (fun
        | .entry, t | .label "even", t => t = s.pushRa ra
        | .label _, t => t.regs = (s.pushRa ra).regs ∧ t.dmem = (s.pushRa ra).dmem ∧ n = 0
        | _, _ => False)
      (fun _ _ => 0) ?_ rfl
    cfg_cases
    all_goals kvcgen64 [hodd] with finish
  · refine Program.WP.cfg (fun
        | .entry, t | .label "odd", t => t = s.pushRa ra
        | .label _, t => t.regs = (s.pushRa ra).regs ∧ t.dmem = (s.pushRa ra).dmem ∧ n = 0
        | _, _ => False)
      (fun _ _ => 0) ?_ rfl
    cfg_cases
    all_goals kvcgen64 [heven] with finish

end State.EvenOdd
