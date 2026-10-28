module

public import Kraken.StateCfg
import Kraken.SeparationMem
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace State

def swap : Program := parse("
swap:
  xor %rbx, %rax
  xor %rax, %rbx
  xor %rbx, %rax
  ret
")

def pswap : Program := parse("
start:
  call swap
  call swap
  jmp done
") ++ swap ++ parse("
done:
  nop
")

abbrev swap_spec.Frame (c t : MachineData) : Prop :=
  t.regs.rcx = c.regs.rcx ∧ t.regs.rdx = c.regs.rdx ∧ t.regs.rsi = c.regs.rsi ∧ t.regs.rdi = c.regs.rdi
    ∧ t.regs.rbp = c.regs.rbp ∧ t.regs.r8 = c.regs.r8 ∧ t.regs.r9 = c.regs.r9
    ∧ t.regs.r10 = c.regs.r10 ∧ t.regs.r11 = c.regs.r11 ∧ t.regs.r12 = c.regs.r12
    ∧ t.regs.r13 = c.regs.r13 ∧ t.regs.r14 = c.regs.r14 ∧ t.regs.r15 = c.regs.r15
    ∧ Mem.WritesOnly [Mem.Block.ofStackSlots c.regs.rsp 0] c.dmem t.dmem

theorem swap_spec [Host] [FunDecls] [Embeds swap] (hs : FunDecls.at (label "swap") = some ⟨swap⟩) :
    ∀ c ra (Q' : Unit → MachineData → Prop) (E' : Int64 → MachineData → Prop),
      ⦃ fun s => s = c.push64 ra
          ∧ Mem.Mapped [(c.regs.rsp.toBitVec - 8#64, 8)] c.dmem
          ∧ (∀ t, t.regs.rax.toBitVec = c.regs.rbx.toBitVec ∧ t.regs.rbx.toBitVec = c.regs.rax.toBitVec ∧ t.regs.rsp = c.regs.rsp ∧ swap_spec.Frame c t → E' ra t)
          ∧ (∀ a t, a ≠ ra → False ∧ swap_spec.Frame c t → E' a t) ⦄
        FunDecls.body "swap"
      ⦃ Q'; E' ⦄ := by
  have k : ∀ c ra, Mem.Mapped [(c.regs.rsp.toBitVec - 8#64, 8)] c.dmem
      → WP.wp swap (fun _ _ => False) (fun a t => a = ra
        ∧ t.regs.rax.toBitVec = c.regs.rbx.toBitVec ∧ t.regs.rbx.toBitVec = c.regs.rax.toBitVec ∧ t.regs.rsp = c.regs.rsp ∧ swap_spec.Frame c t) (c.push64 ra) := by
    intro c ra _
    refine Program.WP.cfg (fun
        | .entry, t | .label "swap", t => t = c.push64 ra
        | _, _ => False)
      (fun _ _ => 0) ?_ rfl
    cfg_cases
    all_goals kvcgen64 with finish
  refine fun c ra Q' E' => ⟨fun s₀ ⟨h₀, hpre, hok, _⟩ => ?_⟩
  subst h₀
  rw [FunDecls.body_eq hs]
  exact Program.wp_mono (fun _ h => False.elim h) (fun u hu => hu.1 ▸ hok u.data hu.2) (k c ra hpre)

theorem pswap_correct [Host] (hp : pswap.IsInfix Host.prog)
    (d : MachineData)
    (hmem : Mem.Mapped [(d.regs.rsp.toBitVec - 8#64, 8)] d.dmem) :
    Eventually (step1 Host.exe)
      (fun s => s.data.regs.rax.toBitVec = d.regs.rax.toBitVec ∧ s.data.regs.rbx.toBitVec = d.regs.rbx.toBitVec
        ∧ s.data.regs.rsp.toBitVec = d.regs.rsp.toBitVec)
      ⟨d, startAddr hp⟩ := by
  have hk := List.isInfixAt_infixIdx hp
  generalize pswap.infixIdx Host.prog hp = k at hk
  have hsp : swap.IsInfixAt pswap 4 := ⟨_, rfl⟩
  have hsw : swap.IsInfixAt Host.prog (k + 4) := List.IsInfixAt.trans hsp hk
  letI : Embeds swap := ⟨⟨k + 4, hsw⟩⟩
  letI : FunDecls := ⟨[Fragment.mk swap]⟩
  have hstart : (Fragment.mk swap).startAddr = label "swap" := (Host.label_eq (i := 0) hsw rfl).symm
  have hg : FunDecls.at (label "swap") = some (Fragment.mk swap) := by
    show List.find? _ [_] = _
    simp [hstart]
  have hcall := Program.WP.call_spec hg
  have hswap := swap_spec hg
  apply Program.WP.step1_of_wp hp
  refine Program.WP.cfg (fun
      | .entry, s | .label "start", s => s = d
      | .label "done", s | .exit, s => s.regs.rax.toBitVec = d.regs.rax.toBitVec
          ∧ s.regs.rbx.toBitVec = d.regs.rbx.toBitVec ∧ s.regs.rsp.toBitVec = d.regs.rsp.toBitVec
      | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 [hcall, hswap] with finish

end State
