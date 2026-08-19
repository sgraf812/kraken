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
private theorem pswap_body_spec (ra : Int64) (rax rbx rsp : BitVec 64) (dmem : DataMem)
    (hload : Mem.loadInt dmem rsp Width.W64.bytes = some ra.toBitVec.toInt) :
    ⦃ fun t => t.regs.get64 .rax = rax ∧ t.regs.get64 .rbx = rbx
        ∧ t.regs.get64 .rsp = rsp ∧ t.dmem = dmem ⦄
      pswap.body
    ⦃ (fun _ _ => False);
      fun a s' => a = ra ∧ s'.regs.get64 .rax = rbx ∧ s'.regs.get64 .rbx = rax
        ∧ s'.regs.get64 .rsp = rsp + Width.W64.bytesv ∧ s'.dmem = dmem ⦄ := by
  have hround : Int64.ofBitVec (BitVec.ofInt Width.W64.bits ra.toBitVec.toInt) = ra := by
    apply Int64.toBitVec_inj.mp
    simp
  vcgen simplifying_assumptions with finish

/-- The stack slot a call writes reads back what the call wrote. -/
private abbrev SlotRoundtrip : Prop :=
  ∀ (m : DataMem) (a v : BitVec 64),
    Mem.loadInt (Mem.storeInt m a Width.W64.bytes v.toInt) a Width.W64.bytes = some v.toInt

omit [Executable.ValidLayout (layout pswap)] in
/-- One call of the procedure: the run enters at the label with the return
address on the stack, and comes back with the registers exchanged, the stack
pointer restored, and memory as the call left it. -/
private theorem pswap_call (hmem : SlotRoundtrip) (ra : Int64) (s : MachineData)
    {K : MachineData → Prop} {E : Int64 → MachineData → Prop}
    (hK : ∀ s' : MachineData,
      s'.regs.get64 .rax = s.regs.get64 .rbx → s'.regs.get64 .rbx = s.regs.get64 .rax →
      s'.regs.get64 .rsp = s.regs.get64 .rsp →
      s'.dmem = Mem.storeInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv)
        Width.W64.bytes ra.toBitVec.toInt → K s') :
    cenv.wp pswap.body (fun _ => False)
      (fun a s' => if a = ra then K s' else E a s') (s.pushRa ra) := by
  have hload : Mem.loadInt
      (Mem.storeInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv) Width.W64.bytes
        ra.toBitVec.toInt)
      (s.regs.get64 .rsp - Width.W64.bytesv) Width.W64.bytes = some ra.toBitVec.toInt :=
    hmem _ _ _
  have hrun := (pswap_body_spec ra (s.regs.get64 .rax) (s.regs.get64 .rbx)
      (s.regs.get64 .rsp - Width.W64.bytesv) _ hload).le_wp (s.pushRa ra)
      ⟨rfl, rfl, rfl, rfl⟩
  rw [MachineWP.wp_eq] at hrun
  refine Executable.wp_mono (fun _ hq => hq) ?_ hrun
  rintro a s' ⟨rfl, hrax, hrbx, hrsp, hdmem⟩
  rw [if_pos rfl]
  refine hK s' hrax hrbx ?_ hdmem
  rw [hrsp]
  apply BitVec.sub_add_cancel

theorem pswap_correct (hmem : SlotRoundtrip) (d : MachineData)
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
    refine (MachineWP.call_spec (P := fun t => t = s) _ _ "swap" pswap.body
      pswap_body_placed ?_).le_wp s ⟨rfl, hslot⟩
    rintro ra₁ t rfl
    refine pswap_call hmem ra₁ t (fun s' hrax hrbx hrsp hdmem => ?_)
    have hslot' : (Mem.loadInt s'.dmem (s'.regs.get64 .rsp - Width.W64.bytesv)
        Width.W64.bytes).isSome = true := by
      rw [hdmem, hrsp, hmem]
      rfl
    refine (MachineWP.call_spec (P := fun u => u = s') _ _ "swap" pswap.body
      pswap_body_placed ?_).le_wp s' ⟨rfl, hslot'⟩
    rintro ra₂ u rfl
    refine pswap_call hmem ra₂ u (fun s'' hrax' hrbx' hrsp' _ => ?_)
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
theorem pswap_correct_run (hmem : SlotRoundtrip) (d : MachineData)
    (hslot : (Mem.loadInt d.dmem (d.regs.get64 .rsp - Width.W64.bytesv)
      Width.W64.bytes).isSome = true) :
    Eventually (straightlineStep (layout pswap))
      (fun s => s.1.regs.get64 .rax = d.regs.get64 .rax
        ∧ s.1.regs.get64 .rbx = d.regs.get64 .rbx
        ∧ s.1.regs.get64 .rsp = d.regs.get64 .rsp)
      (d, layout.start) :=
  Program.run_of_triple (pswap_correct hmem d hslot) rfl
