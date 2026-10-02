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
swap:
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

/-- `rax` and `rbx` exchanged, and the return slot still mapped. -/
private abbrev SwapPost (s s' : MachineData) : Prop :=
  s'.regs.get64 .rax = s.regs.get64 .rbx ∧ s'.regs.get64 .rbx = s.regs.get64 .rax ∧ SwapPre s'

/-- `swap` clobbers `rax` and `rbx` and writes no memory. -/
private abbrev swapMod : Modifies := ⟨[.rax, .rbx], fun _ => 0, fun _ => 0⟩

private abbrev pswap_table (d : MachineData) : Label → MachineData → Prop
  | "start", s => s = d
  | "done", s => s.regs.get64 .rax = d.regs.get64 .rax ∧ s.regs.get64 .rbx = d.regs.get64 .rbx
      ∧ s.regs.get64 .rsp = d.regs.get64 .rsp
  | _, _ => False

variable [layout : Layout]

omit layout in
private theorem pswap_body_spec [LinkedProgram] (s : MachineData) (ra : Int64) :
    ⦃ fun t => t = s.pushRa ra ∧ SwapPre s ⦄
      pswap.body
    ⦃ (fun _ _ => False); fun a s' => a = ra ∧ SwapPost s s' ∧ swapMod.Agree s s' ⦄ := by
  refine ⟨fun t ⟨ht, hpre⟩ => ?_⟩
  subst ht
  simp only [MachineData.pushRa]
  kvcgen64
  · grind
  · refine ⟨by grind, by grind, fun r hr => ?_, fun a _ h2 => ?_⟩
    · cases r <;> simp_all
    · exact Mem.get?_storeInt_of_ne _ _ _ _ _ (ne_add_of_dist h2)

theorem pswap_correct [Kraken.Executable.ValidExecutable (layout pswap)]
    (d : MachineData) (hslot : SwapPre d) :
    Eventually (straightlineStep (layout pswap))
      (fun s => s.1.regs.get64 .rax = d.regs.get64 .rax
        ∧ s.1.regs.get64 .rbx = d.regs.get64 .rbx
        ∧ s.1.regs.get64 .rsp = d.regs.get64 .rsp)
      (d, layout.start) := by
  apply eventually_straightlineStep_of_wp
  intro _
  refine StateWP.cfg_wp (pswap_table d) (fun _ _ => 0) _ ⊥ ?_ d rfl
  cfg_cases [pswap]
  · intro k hlink
    have hswap : CallSpec "swap" SwapPre SwapPost swapMod :=
      StateWP.callSpec_of_triple (body := pswap.body.tail) hlink (by rfl) pswap_body_spec
    kvcgen64 [hswap] with finish
  · kvcgen64 with finish

end State
