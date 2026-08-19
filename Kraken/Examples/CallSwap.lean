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

omit [Executable.ValidLayout (layout pswap)] in
/-- The procedure: it exchanges the two registers, pops the return address and
returns to it, and leaves memory as it found it. -/
private theorem pswap_body_spec (ra : Int64) (rax rbx rsp : BitVec 64) (dmem : DataMem) :
    ⦃ fun t => t.regs.get64 .rax = rax ∧ t.regs.get64 .rbx = rbx
        ∧ t.regs.get64 .rsp = rsp ∧ t.dmem = dmem ∧ t.retAddr = some ra ⦄
      pswap.body
    ⦃ (fun _ _ => False);
      fun a s' => a = ra ∧ s'.regs.get64 .rax = rbx ∧ s'.regs.get64 .rbx = rax
        ∧ s'.regs.get64 .rsp = rsp + Width.W64.bytesv ∧ s'.dmem = dmem ⦄ := by
  vcgen simplifying_assumptions with finish

omit [Executable.ValidLayout (layout pswap)] in
/-- One call of the procedure, as the premise of the call rule: the callee
enters on the caller's state pushed with the return address, and returns with
the two registers exchanged, the stack pointer restored, and the slot it used
still mapped. -/
private theorem pswap_call (ra : Int64) (s : MachineData)
    {K : MachineData → Prop} {E : Int64 → MachineData → Prop}
    (hslot : (Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv)
      Width.W64.bytes).isSome = true)
    (hK : ∀ s' : MachineData,
      s'.regs.get64 .rax = s.regs.get64 .rbx → s'.regs.get64 .rbx = s.regs.get64 .rax →
      s'.regs.get64 .rsp = s.regs.get64 .rsp →
      (Mem.loadInt s'.dmem (s'.regs.get64 .rsp - Width.W64.bytesv)
        Width.W64.bytes).isSome = true → K s') :
    ⦃ fun t => t = s.pushRa ra ⦄
      pswap.body
    ⦃ (fun _ _ => False); fun a s' => if a = ra then K s' else E a s' ⦄ := by
  refine Triple.intro fun t ht => ?_
  subst ht
  rw [MachineWP.wp_eq]
  have hrun := (pswap_body_spec ra (s.regs.get64 .rax) (s.regs.get64 .rbx)
    (s.regs.get64 .rsp - Width.W64.bytesv) (s.pushRa ra).dmem).le_wp (s.pushRa ra)
    ⟨by simp [MachineData.pushRa], by simp [MachineData.pushRa],
      by simp [MachineData.pushRa], rfl, MachineData.retAddr_pushRa s ra⟩
  rw [MachineWP.wp_eq] at hrun
  refine Executable.wp_mono (fun _ hq => hq) ?_ hrun
  rintro a s' ⟨hra, hrax, hrbx, hrsp, hdmem⟩
  rw [if_pos hra]
  refine hK s' hrax hrbx ?_ ?_
  · rw [hrsp, BitVec.sub_add_cancel]
  · rw [hdmem, hrsp, BitVec.sub_add_cancel]
    simp only [MachineData.pushRa, Reg64s.get64_set64, reduceIte]
    rw [Mem.loadInt_storeInt _ _ _ _ (by decide)]
    rfl

theorem pswap_correct (d : MachineData)
    (hslot : (Mem.loadInt d.dmem (d.regs.get64 .rsp - Width.W64.bytesv)
      Width.W64.bytes).isSome = true) :
    ⦃ fun s => s = d ⦄
      pswap
    ⦃ fun _ s => s.regs.get64 .rax = d.regs.get64 .rax
        ∧ s.regs.get64 .rbx = d.regs.get64 .rbx
        ∧ s.regs.get64 .rsp = d.regs.get64 .rsp ⦄ := by
  apply MachineWP.cfg (pswap_table d) (fun _ _ => 0)
  cfg_cases [pswap]
  · -- the caller: two calls, then the jump to the tail
    refine Triple.intro fun s hs => ?_
    obtain ⟨rfl, hn⟩ := hs
    refine (MachineWP.call_spec (P := fun ra u => u = s.pushRa ra) _ _ "swap" pswap.body
      pswap_body_placed ?_).le_wp s ⟨fun _ => rfl, hslot⟩
    intro ra₁
    refine pswap_call ra₁ s hslot (fun s' hrax hrbx hrsp hslot' => ?_)
    refine (MachineWP.call_spec (P := fun ra u => u = s'.pushRa ra) _ _ "swap" pswap.body
      pswap_body_placed ?_).le_wp s' ⟨fun _ => rfl, hslot'⟩
    intro ra₂
    refine pswap_call ra₂ s' hslot' (fun s'' hrax' hrbx' hrsp' _ => ?_)
    refine (MachineWP.jmp_label_spec _ _ "done").le_wp s'' ?_
    refine Table.ofLabels_at ⟨by decide, ⟨?_, ?_, ?_⟩, Or.inr ⟨hn, by decide⟩⟩
    · rw [hrax', hrbx]
    · rw [hrbx', hrax]
    · rw [hrsp', hrsp]
  · -- the procedure is entered by a call, never by an edge of the table
    exact Triple.intro fun s hs => hs.1.elim
  · -- the tail
    vcgen simplifying_assumptions with finish

/-- `pswap_correct`, read at the machine as the baseline judgment. -/
theorem pswap_correct_run (d : MachineData)
    (hslot : (Mem.loadInt d.dmem (d.regs.get64 .rsp - Width.W64.bytesv)
      Width.W64.bytes).isSome = true) :
    Eventually (straightlineStep (layout pswap))
      (fun s => s.1.regs.get64 .rax = d.regs.get64 .rax
        ∧ s.1.regs.get64 .rbx = d.regs.get64 .rbx
        ∧ s.1.regs.get64 .rsp = d.regs.get64 .rsp)
      (d, layout.start) :=
  Program.run_of_triple (pswap_correct d hslot) rfl
