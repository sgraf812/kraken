/-
The original `swap` (three `xor`s exchanging `rax` and `rbx`), wrapped as a
procedure and called twice: the involution restores both registers, and the
stack pointer comes back to its entry value. `MachineWP.call_spec` links each
call to its return: the machine pushes the address behind the call cell, and
the callee's `ret` at that address continues the caller's run.
-/
import Kraken.Parser
import Kraken.MachineWP

open Kraken.Parser
open Std.Internal.Do
open MachineWP
open Lean.Order

set_option mvcgen.warning false

/-- The program: the caller, the procedure it calls twice, the tail. -/
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

/-- The procedure's body: the three `xor`s and the return. -/
abbrev pswap.body : Program := parse("
  xor %rbx, %rax
  xor %rax, %rbx
  xor %rbx, %rax
  ret
")

/-- The jump edge of the caller goes forward in the text. -/
@[grind .] private theorem pswap_idx_start_lt_done :
    Program.blockIdx pswap "start" < Program.blockIdx pswap "done" := by decide

/-- The jump target of the caller is mapped. -/
@[grind .] private theorem pswap_done_isSome :
    (Program.blockAt pswap "done").isSome := by decide

/-- The spec table: the caller starts on `d`, the tail holds the answer, and
the procedure is entered by a call rather than by an edge of the table. -/
private abbrev pswap_table (d : MachineData) : Label → MachineData → Prop
  | "start", s => s = d
  | "done", s => s.regs.get64 .rax = d.regs.get64 .rax ∧ s.regs.get64 .rbx = d.regs.get64 .rbx
      ∧ s.regs.get64 .rsp = d.regs.get64 .rsp
  | _, _ => False

variable [layout : Layout] [Executable.ValidLayout (layout pswap)]

/-- The ambient code of the example: `pswap`, laid out. -/
local instance pswap.env : CodeEnv := ⟨layout pswap⟩

/-- The procedure sits at its label. -/
private theorem pswap_body_placed : cenv.sits (cenv.labels.label "swap") pswap.body :=
  (Program.placed_of_layout (p := pswap) (l₀ := "start") (by decide) (by rfl) (by decide)).block
    "swap" ⟨"swap", pswap.body, some "done"⟩ (by decide)

/-- What the procedure needs of its caller: the slot the call writes is
mapped, so the return address has somewhere to go. -/
private abbrev SwapPre (s : MachineData) : Prop :=
  (Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv)
    Width.W64.bytes).isSome = true

/-- What the procedure leaves the caller: the two registers exchanged, the
stack pointer restored, and the slot it used still mapped. -/
private abbrev SwapPost (s s' : MachineData) : Prop :=
  s'.regs.get64 .rax = s.regs.get64 .rbx ∧ s'.regs.get64 .rbx = s.regs.get64 .rax
    ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp ∧ SwapPre s'

omit [Executable.ValidLayout (layout pswap)] in
/-- The procedure, from the state its caller pushed: it exchanges the two
registers and returns to the address on the stack. -/
private theorem pswap_body_spec (ra : Int64) (s : MachineData) :
    ⦃ fun t => t = s.pushRa ra ∧ SwapPre s ⦄
      pswap.body
    ⦃ (fun _ _ => False); fun a s' => a = ra ∧ SwapPost s s' ⦄ := by
  refine Triple.intro fun t ht => ?_
  obtain ⟨rfl, hpre⟩ := ht
  vcgen simplifying_assumptions with finish

theorem pswap_correct (d : MachineData) (hslot : SwapPre d) :
    ⦃ fun s => s = d ⦄
      pswap
    ⦃ fun _ s => s.regs.get64 .rax = d.regs.get64 .rax
        ∧ s.regs.get64 .rbx = d.regs.get64 .rbx
        ∧ s.regs.get64 .rsp = d.regs.get64 .rsp ⦄ := by
  have hcall := MachineWP.fun_spec_from_label pswap_body_placed pswap_body_spec
  apply MachineWP.cfg (pswap_table d) (fun _ _ => 0)
  cfg_cases [pswap]
  · vcgen [hcall] simplifying_assumptions with finish
  · exact Triple.intro fun s hs => hs.1.elim
  · vcgen simplifying_assumptions with finish

/-- `pswap_correct`, read at the machine as the baseline judgment. -/
theorem pswap_correct_run (d : MachineData) (hslot : SwapPre d) :
    Eventually (straightlineStep (layout pswap))
      (fun s => s.1.regs.get64 .rax = d.regs.get64 .rax
        ∧ s.1.regs.get64 .rbx = d.regs.get64 .rbx
        ∧ s.1.regs.get64 .rsp = d.regs.get64 .rsp)
      (d, layout.start) :=
  Program.run_of_triple (pswap_correct d hslot) rfl
