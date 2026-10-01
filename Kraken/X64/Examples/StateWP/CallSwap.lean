module

public import Kraken.StateCfg
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
  xor %rbx, %rax
  xor %rax, %rbx
  xor %rbx, %rax
  ret
")

@[grind .] private theorem pswap_idx_start_lt_done :
    Program.blockIdx pswap "start" < Program.blockIdx pswap "done" := by decide

@[grind .] private theorem pswap_done_isSome :
    (Program.blockAt pswap "done").isSome := by decide

private abbrev SwapPre (s : MachineData) : Prop :=
  (Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome = true

private abbrev SwapPost (s s' : MachineData) : Prop :=
  s'.regs.get64 .rax = s.regs.get64 .rbx ∧ s'.regs.get64 .rbx = s.regs.get64 .rax
    ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp ∧ SwapPre s'

private abbrev swapC : Contract := ⟨"swap", SwapPre, SwapPost⟩

private abbrev pswap_table (d : MachineData) : Label → MachineData → Prop
  | "start", s => s = d
  | "done", s => s.regs.get64 .rax = d.regs.get64 .rax ∧ s.regs.get64 .rbx = d.regs.get64 .rbx
      ∧ s.regs.get64 .rsp = d.regs.get64 .rsp
  | _, _ => False

variable [layout : Layout]

omit layout in
private theorem pswap_body_spec [Host] (s : MachineData) (ra : Int64) :
    ⦃ fun t => t = s.pushRa ra ∧ SwapPre s ⦄
      pswap.body
    ⦃ (fun _ _ => False); fun a s' => a = ra ∧ SwapPost s s' ⦄ := by
  refine ⟨fun t ⟨ht, hpre⟩ => ?_⟩
  subst ht
  simp only [MachineData.pushRa]
  kvcgen64 with finish

private theorem swap_call_spec [Host] {Q : Unit → MachineData → Prop}
    {E : Int64 → MachineData → Prop} (asz osz : Width) :
    ⦃ fun s => (Host.Placed ∧ swapC.Implemented)
        ⊓ ((Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome = true)
        ⊓ SwapPre s ⊓ (∀ s', SwapPost s s' → Q () s') ⦄
      Directive.instr (.regular asz osz (.call (.rel (.sub (.label "swap") .after_current_instruction))))
    ⦃ Q; E ⦄ :=
  StateWP.call_spec asz osz swapC

theorem pswap_correct [hv : Kraken.Executable.ValidLayout (layout pswap)]
    (d : MachineData) (hslot : SwapPre d) :
    Eventually (straightlineStep (layout pswap))
      (fun s => s.1.regs.get64 .rax = d.regs.get64 .rax
        ∧ s.1.regs.get64 .rbx = d.regs.get64 .rbx
        ∧ s.1.regs.get64 .rsp = d.regs.get64 .rsp)
      (d, layout.start) := by
  refine StateWP.cfg (l₀ := "start") (pswap_table d) (fun _ _ => 0) ?_ (by rfl) (by decide) d rfl
  cfg_cases [pswap]
  · intro _ hhost
    haveI : Kraken.Executable.ValidLayout Host.exe := hhost ▸ hv
    have hplaced : Host.Placed := Host.placed_of_valid
    have himpl : swapC.Implemented :=
      StateWP.implemented_of_triple (body := pswap.body) hhost (by decide) swapC (by rfl)
        pswap_body_spec
    kvcgen64 [swap_call_spec] with finish
  · kvcgen64 with finish
  · kvcgen64 with finish

end State
