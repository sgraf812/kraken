module

/-
A caller that moves a byte range onto an overlapping range through a call to `memmove`, after
Erbsen et al., "Foundational Integration Verification of a Cryptographic Server" (PLDI 2024,
§2.3). `memmove_spec` proves the callee on its own: the source holds the bytes `bs`, the
destination is mapped, and on return the destination holds `bs` and the memory outside the
destination and the return slot is unchanged. The source can overlap the destination. `memmove_correct` proves the caller from
`memmove_spec` alone.
-/
public import Kraken.StateCfg
public import Kraken.SeparationMem
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

abbrev memmove_spec.Frame (c t : MachineData) : Prop :=
  t.regs.rbx = c.regs.rbx ∧ t.regs.rcx = c.regs.rcx ∧ t.regs.rbp = c.regs.rbp
    ∧ t.regs.r8 = c.regs.r8 ∧ t.regs.r9 = c.regs.r9 ∧ t.regs.r10 = c.regs.r10 ∧ t.regs.r11 = c.regs.r11
    ∧ t.regs.r12 = c.regs.r12 ∧ t.regs.r13 = c.regs.r13 ∧ t.regs.r14 = c.regs.r14 ∧ t.regs.r15 = c.regs.r15
    ∧ Mem.WritesOnly [Mem.Block.ofStackSlots c.regs.rsp 0, (c.regs.rdi.toBitVec, c.regs.rdx.toBitVec.toNat)]
        c.dmem t.dmem

private abbrev MMFwd (bs : List UInt8) (c : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  c.regs.rdi.toBitVec.toNat ≤ c.regs.rsi.toBitVec.toNat ∧ t.regs.rdx.toBitVec.toNat ≤ bs.length
    ∧ t.regs.rsi.toBitVec = c.regs.rsi.toBitVec + .ofNat 64 (bs.length - t.regs.rdx.toBitVec.toNat)
    ∧ t.regs.rdi.toBitVec = c.regs.rdi.toBitVec + .ofNat 64 (bs.length - t.regs.rdx.toBitVec.toNat)
    ∧ memmove_spec.Frame c t ∧ t.regs.rsp.toBitVec = c.regs.rsp.toBitVec - 8#64
    ∧ Mem.Contains t.dmem (c.regs.rsp.toBitVec - 8#64) (Int.toBytes 8 ra.toBitVec.toInt)
    ∧ Mem.Contains t.dmem c.regs.rdi.toBitVec (bs.take (bs.length - t.regs.rdx.toBitVec.toNat))
    ∧ Mem.Contains t.dmem t.regs.rsi.toBitVec (bs.drop (bs.length - t.regs.rdx.toBitVec.toNat))

private abbrev MMBwd (bs : List UInt8) (c : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  c.regs.rsi.toBitVec.toNat < c.regs.rdi.toBitVec.toNat ∧ t.regs.rdx.toBitVec.toNat ≤ bs.length
    ∧ t.regs.rsi.toBitVec = c.regs.rsi.toBitVec + t.regs.rdx.toBitVec
    ∧ t.regs.rdi.toBitVec = c.regs.rdi.toBitVec + t.regs.rdx.toBitVec
    ∧ memmove_spec.Frame c t ∧ t.regs.rsp.toBitVec = c.regs.rsp.toBitVec - 8#64
    ∧ Mem.Contains t.dmem (c.regs.rsp.toBitVec - 8#64) (Int.toBytes 8 ra.toBitVec.toInt)
    ∧ Mem.Contains t.dmem t.regs.rdi.toBitVec (bs.drop t.regs.rdx.toBitVec.toNat)
    ∧ Mem.Contains t.dmem c.regs.rsi.toBitVec (bs.take t.regs.rdx.toBitVec.toNat)

theorem memmove_spec [Host] [FunDecls] [Embeds memmove]
    (hm : FunDecls.at (label "memmove") = some ⟨memmove⟩) (bs : List UInt8) :
    ∀ c ra (Q' : Unit → MachineData → Prop) (E' : Int64 → MachineData → Prop),
      ⦃ fun s => s = c.push64 ra
          ∧ (bs.length = c.regs.rdx.toBitVec.toNat
            ∧ c.regs.rsi.toBitVec.toNat + bs.length < 2 ^ 64
            ∧ c.regs.rdi.toBitVec.toNat + bs.length < 2 ^ 64
            ∧ Mem.Contains c.dmem c.regs.rsi.toBitVec bs
            ∧ Mem.Mapped [(c.regs.rsp.toBitVec - 8#64, 8), (c.regs.rdi.toBitVec, bs.length)] c.dmem
            ∧ Mem.Blocks.Disjoint [(c.regs.rsi.toBitVec, bs.length), (c.regs.rdi.toBitVec, bs.length)]
                [(c.regs.rsp.toBitVec - 8#64, 8)])
          ∧ (∀ t, Mem.Contains t.dmem c.regs.rdi.toBitVec bs ∧ t.regs.rsp = c.regs.rsp ∧ memmove_spec.Frame c t → E' ra t)
          ∧ (∀ a t, a ≠ ra → False ∧ memmove_spec.Frame c t → E' a t) ⦄
        FunDecls.body "memmove"
      ⦃ Q'; E' ⦄ := by
  have k : ∀ c ra, bs.length = c.regs.rdx.toBitVec.toNat
        ∧ c.regs.rsi.toBitVec.toNat + bs.length < 2 ^ 64
        ∧ c.regs.rdi.toBitVec.toNat + bs.length < 2 ^ 64
        ∧ Mem.Contains c.dmem c.regs.rsi.toBitVec bs
        ∧ Mem.Mapped [(c.regs.rsp.toBitVec - 8#64, 8), (c.regs.rdi.toBitVec, bs.length)] c.dmem
        ∧ Mem.Blocks.Disjoint [(c.regs.rsi.toBitVec, bs.length), (c.regs.rdi.toBitVec, bs.length)]
            [(c.regs.rsp.toBitVec - 8#64, 8)]
      → WP.wp memmove (fun _ _ => False) (fun a t => a = ra
        ∧ Mem.Contains t.dmem c.regs.rdi.toBitVec bs ∧ t.regs.rsp = c.regs.rsp ∧ memmove_spec.Frame c t) (c.push64 ra) := by
    intro c ra _
    refine Program.WP.cfg (fun
        | .entry, t | .label "memmove", t => t = c.push64 ra
        | .label "bwd", t => MMBwd bs c ra t
        | .label "bdone", t => MMBwd bs c ra t ∧ t.regs.rdx.toBitVec = 0
        | .label "fwd", t => MMFwd bs c ra t
        | .label "fdone", t => MMFwd bs c ra t ∧ t.regs.rdx.toBitVec = 0
        | _, _ => False)
      (fun _ t => t.regs.rdx.toBitVec.toNat) ?_ rfl
    cfg_cases
    all_goals kvcgen64 with finish
  refine fun c ra Q' E' => ⟨fun s₀ ⟨h₀, hpre, hok, _⟩ => ?_⟩
  subst h₀
  rw [FunDecls.body_eq hm]
  exact Program.wp_mono (fun _ h => False.elim h) (fun u hu => hu.1 ▸ hok u.data hu.2) (k c ra hpre)

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
  have hmemmove := memmove_spec hg bs
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
  all_goals kvcgen64 [hcall, hmemmove] with finish

end State
