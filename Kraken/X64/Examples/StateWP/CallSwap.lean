module

public import Kraken.StateCfg
import Kraken.SeparationMem
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped StateWP

set_option experimental.vcgen true

namespace State

def pswap : Program := parse("
start:
  call swap
  call swap
  jmp done
swap:
  xor %rbx, %rax
  xor %rax, %rbx
  xor %rbx, %rax
  ret
done:
  nop
")

abbrev pswap.body : Program := parse("
swap:
  xor %rbx, %rax
  xor %rax, %rbx
  xor %rbx, %rax
  ret
")

/-- `swap` clobbers `rax` and `rbx`. -/
private abbrev swapMod : Modifies := ⟨[.rax, .rbx]⟩

private abbrev pswap_table (d : MachineData) (R : DataMem → Prop) : Label → MachineData → Prop
  | "start", s => s = d ∧ d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rsp - 8#64, 8)] ⋆ R
  | "done", s => s.regs.get64 .rax = d.regs.get64 .rax ∧ s.regs.get64 .rbx = d.regs.get64 .rbx
      ∧ s.regs.get64 .rsp = d.regs.get64 .rsp
  | _, _ => False

variable [layout : Layout]

omit layout in
private theorem pswap_body_spec [LinkedProgram] (R : DataMem → Prop) (s : MachineData) (ra : Int64) :
    ⦃ fun t => t = s.pushRa ra ∧ s.dmem =⋆ Mem.Blocks [(s.regs.get64 .rsp - 8#64, 8)] ⋆ R ⦄
      pswap.body
    ⦃ (fun _ _ => False); fun a s' => a = ra
      ∧ (s'.regs.get64 .rax = s.regs.get64 .rbx ∧ s'.regs.get64 .rbx = s.regs.get64 .rax
        ∧ s'.dmem =⋆ Mem.Blocks [(s.regs.get64 .rsp - 8#64, 8)] ⋆ R)
      ∧ swapMod.Agree s s' ⦄ := by
  refine ⟨fun t ⟨ht, hpre⟩ => ?_⟩
  subst ht
  simp only [MachineData.pushRa]
  kvcgen64
  · grind
  · refine ⟨by grind, by grind, fun r _ => ?_⟩
    cases r <;> simp_all

theorem pswap_correct [Kraken.Executable.ValidExecutable (layout pswap)]
    (d : MachineData) (R : DataMem → Prop)
    (hmem : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rsp - 8#64, 8)] ⋆ R) :
    Eventually (straightlineStep (layout pswap))
      (fun s => s.1.regs.get64 .rax = d.regs.get64 .rax
        ∧ s.1.regs.get64 .rbx = d.regs.get64 .rbx
        ∧ s.1.regs.get64 .rsp = d.regs.get64 .rsp)
      (d, layout.start) := by
  apply eventually_straightlineStep_of_wp
  intro _
  refine StateWP.cfg_wp (l₀ := "start") (pswap_table d R) (fun _ _ => 0) _ ⊥ ?_ d ⟨rfl, hmem⟩
  cfg_cases [pswap]
  · intro k hlink
    have hswap := StateWP.callSpec_of_triple (body := pswap.body.tail) hlink (by rfl)
      (pswap_body_spec (R := R))
    kvcgen64 [hswap] with finish
  · kvcgen64 with finish

end State
