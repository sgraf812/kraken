module

/-
A caller that moves a byte range onto an overlapping range through a call to `memmove`, after
Erbsen et al., "Foundational Integration Verification of a Cryptographic Server" (PLDI 2024,
§2.3). `memmove_spec` proves the callee on its own: the `rdx` bytes at `rsi` are mapped, the
destination is mapped, and on return the destination holds those bytes and the memory outside
the destination and the return slot is unchanged. The source can overlap the destination.
`memmove_correct` proves the caller from `memmove_spec` alone.
-/
public import Kraken.StateCfg
public import Kraken.SeparationMem
import Kraken.FunSpec
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace State

/-- The callee: copy `rdx` bytes from `rsi` to `rdi`, forward when `rdi ≤ rsi` and backward
otherwise, so that an overlapping source is read before it is overwritten. -/
def memmove : Program := parse("
memmove:
  cmp %rsi, %rdi
  jbe fwd
  add %rdx, %rsi
  add %rdx, %rdi
bwd:
  test %rdx, %rdx
  je bdone
  dec %rsi
  dec %rdi
  movb (%rsi), %al
  movb %al, (%rdi)
  dec %rdx
  jmp bwd
bdone:
  ret
fwd:
  test %rdx, %rdx
  je fdone
  movb (%rsi), %al
  movb %al, (%rdi)
  add $1, %rsi
  add $1, %rdi
  dec %rdx
  jmp fwd
fdone:
  ret
")

/-- The caller, with the callee linked between its two blocks. -/
def memmoveProg : Program := parse("
start:
  call memmove
  jmp done
") ++ memmove ++ parse("
done:
  nop
")

funspec memmove_spec "memmove" [Host] [FunDecls] [Embeds memmove]
    (hm : FunDecls.at (label "memmove") = some ⟨memmove⟩) at c
  requires c.regs.rsi.toBitVec.toNat + c.regs.rdx.toBitVec.toNat < 2 ^ 64
    ∧ c.regs.rdi.toBitVec.toNat + c.regs.rdx.toBitVec.toNat < 2 ^ 64
    ∧ Mem.Mapped [(c.regs.rsi.toBitVec, c.regs.rdx.toBitVec.toNat), (c.regs.rsp.toBitVec - 8#64, 8),
        (c.regs.rdi.toBitVec, c.regs.rdx.toBitVec.toNat)] c.dmem
    ∧ Mem.Blocks.Disjoint
        [(c.regs.rsi.toBitVec, c.regs.rdx.toBitVec.toNat), (c.regs.rdi.toBitVec, c.regs.rdx.toBitVec.toNat)]
        [(c.regs.rsp.toBitVec - 8#64, 8)];
  ensures t => Mem.Contains t.dmem c.regs.rdi.toBitVec
    (c.dmem.loadBytes c.regs.rsi.toBitVec c.regs.rdx.toBitVec.toNat).get!
  autoframes calling_conv SysV preserves rcx r8 r9 r10 r11
    writes c.regs.rdi.toBitVec[*...<c.regs.rdx.toBitVec.toNat] := by
  intro c ra
  refine ⟨fun _ ⟨h₀, _⟩ => ?_⟩
  subst h₀
  refine Program.WP.cfg (fun
      | .entry, t | .label "memmove", t => t = c.push64 ra
      | .label "bwd", t => MMBwd c ra t
      | .label "bdone", t => MMBwd c ra t ∧ t.regs.rdx.toBitVec = 0
      | .label "fwd", t => MMFwd c ra t
      | .label "fdone", t => MMFwd c ra t ∧ t.regs.rdx.toBitVec = 0
      | _, _ => False)
    (fun _ t => t.regs.rdx.toBitVec.toNat) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish
where
  bytes (c : MachineData) : List UInt8 :=
    (c.dmem.loadBytes c.regs.rsi.toBitVec c.regs.rdx.toBitVec.toNat).get!
  MMFwd (c : MachineData) (ra : Int64) (t : MachineData) : Prop :=
    c.regs.rdi.toBitVec.toNat ≤ c.regs.rsi.toBitVec.toNat
      ∧ t.regs.rdx.toBitVec.toNat ≤ c.regs.rdx.toBitVec.toNat
      ∧ t.regs.rsi.toBitVec
        = c.regs.rsi.toBitVec + .ofNat 64 (c.regs.rdx.toBitVec.toNat - t.regs.rdx.toBitVec.toNat)
      ∧ t.regs.rdi.toBitVec
        = c.regs.rdi.toBitVec + .ofNat 64 (c.regs.rdx.toBitVec.toNat - t.regs.rdx.toBitVec.toNat)
      ∧ Frame c t ∧ t.regs.rsp.toBitVec = c.regs.rsp.toBitVec - 8#64
      ∧ Mem.Contains t.dmem (c.regs.rsp.toBitVec - 8#64) (Int.toBytes 8 ra.toBitVec.toInt)
      ∧ Mem.Contains t.dmem c.regs.rdi.toBitVec
          ((bytes c).take (c.regs.rdx.toBitVec.toNat - t.regs.rdx.toBitVec.toNat))
      ∧ Mem.Contains t.dmem t.regs.rsi.toBitVec
          ((bytes c).drop (c.regs.rdx.toBitVec.toNat - t.regs.rdx.toBitVec.toNat))
  MMBwd (c : MachineData) (ra : Int64) (t : MachineData) : Prop :=
    c.regs.rsi.toBitVec.toNat < c.regs.rdi.toBitVec.toNat
      ∧ t.regs.rdx.toBitVec.toNat ≤ c.regs.rdx.toBitVec.toNat
      ∧ t.regs.rsi.toBitVec = c.regs.rsi.toBitVec + t.regs.rdx.toBitVec
      ∧ t.regs.rdi.toBitVec = c.regs.rdi.toBitVec + t.regs.rdx.toBitVec
      ∧ Frame c t ∧ t.regs.rsp.toBitVec = c.regs.rsp.toBitVec - 8#64
      ∧ Mem.Contains t.dmem (c.regs.rsp.toBitVec - 8#64) (Int.toBytes 8 ra.toBitVec.toInt)
      ∧ Mem.Contains t.dmem t.regs.rdi.toBitVec ((bytes c).drop t.regs.rdx.toBitVec.toNat)
      ∧ Mem.Contains t.dmem c.regs.rsi.toBitVec ((bytes c).take t.regs.rdx.toBitVec.toNat)

theorem memmove_correct [Host] (hp : memmoveProg.IsInfix Host.prog)
    (d : MachineData) (bs : List UInt8)
    (hn : bs.length = d.regs.rdx.toBitVec.toNat)
    (hsrc : d.regs.rsi.toBitVec.toNat + bs.length < 2 ^ 64)
    (hdst : d.regs.rdi.toBitVec.toNat + bs.length < 2 ^ 64)
    (hbs : Mem.Contains d.dmem d.regs.rsi.toBitVec bs)
    (hmap : Mem.Mapped [(d.regs.rsp.toBitVec - 8#64, 8), (d.regs.rdi.toBitVec, bs.length)] d.dmem)
    (hdisj : Mem.Blocks.Disjoint [(d.regs.rsi.toBitVec, bs.length), (d.regs.rdi.toBitVec, bs.length)]
      [(d.regs.rsp.toBitVec - 8#64, 8)]) :
    Eventually (step1 Host.exe)
      (fun st => Mem.Contains st.data.dmem d.regs.rdi.toBitVec bs
        ∧ Mem.WritesOnly [Mem.Block.ofStackSlots d.regs.rsp 0, (d.regs.rdi.toBitVec, d.regs.rdx.toBitVec.toNat)]
            d.dmem st.data.dmem)
      ⟨d, startAddr hp⟩ := by
  have hk := List.isInfixAt_infixIdx hp
  generalize memmoveProg.infixIdx Host.prog hp = k at hk
  have hmm : memmove.IsInfixAt Host.prog (k + 3) :=
    List.IsInfixAt.trans (⟨_, rfl⟩ : memmove.IsInfixAt memmoveProg 3) hk
  letI : Embeds memmove := ⟨⟨k + 3, hmm⟩⟩
  letI : FunDecls := ⟨[Fragment.mk memmove]⟩
  have hstart : (Fragment.mk memmove).startAddr = label "memmove" := (Host.label_eq (i := 0) hmm rfl).symm
  have hg : FunDecls.at (label "memmove") = some (Fragment.mk memmove) := by
    show List.find? _ [_] = _
    simp [hstart]
  have hcall := Program.WP.call_spec hg
  apply Program.WP.step1_of_wp hp
  refine Program.WP.cfg (fun
      | .entry, s | .label "start", s => s = d
      | .label "done", s => s.regs.rsp = d.regs.rsp ∧ Mem.Contains s.dmem d.regs.rdi.toBitVec bs
          ∧ Mem.WritesOnly [Mem.Block.ofStackSlots d.regs.rsp 0, (d.regs.rdi.toBitVec, d.regs.rdx.toBitVec.toNat)]
              d.dmem s.dmem
      | .exit, s => Mem.Contains s.dmem d.regs.rdi.toBitVec bs
          ∧ Mem.WritesOnly [Mem.Block.ofStackSlots d.regs.rsp 0, (d.regs.rdi.toBitVec, d.regs.rdx.toBitVec.toNat)]
              d.dmem s.dmem
      | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 [hcall] with finish

end State
