module

public import Kraken.StateCfg
public import Kraken.SeparationMem
import Kraken.FunSpec
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace ChangingFrames

public def poke : Program := ⸨prog|
poke:
  movq %rax, (%rdi)
  ret
⸩

public funspec poke_spec "poke" [Host] [FunDecls] [Embeds poke]
    (hp : FunDecls.at (label "poke") = some ⟨poke⟩) at s
    requires Mem.Mapped [(s.regs.rsp.toBitVec - 8#64, 8)] s.dmem
      ∧ Mem.Mapped [(s.regs.rdi.toBitVec, 8)] s.dmem
      ∧ Mem.Blocks.Disjoint [(s.regs.rdi.toBitVec, 8)] [(s.regs.rsp.toBitVec - 8#64, 8)]
    ensures s' => True
    autoframes calling_conv SysV preserves rax rcx rdx rsi rdi r8 r9 r10 r11
      writes s.regs.rdi.toBitVec[*...<8] := by
  vcgen [poke]
    invariants
    · fun {s₀} l s' => match l with
        | "poke" => s' = s₀
        | _ => False
    · fun _ _ => 0
    with kfinish

@[expose] public def pokes : Nat → Program
  | 0 => [(@Kraken.Directive.instr Instr ConstExpr) (.regular .W64 .W64 .ret)]
  | n + 1 =>
    (@Kraken.Directive.instr Instr ConstExpr) (.regular .W64 .W64
      (.call (.rel (.sub (.label "poke") .after_current_instruction))))
    :: (@Kraken.Directive.instr Instr ConstExpr) (.regular .W64 .W64
      (.add (.reg (.low .rdi .W64)) (.imm (.int64 8))))
    :: pokes n

@[expose] public def many (n : Nat) : Program := (@Kraken.Directive.label Instr ConstExpr) "many" :: pokes n

@[expose] public def Goal (n : Nat) : Prop :=
  ∀ [Host] [FunDecls] [Embeds poke] [Embeds (many n)],
    FunDecls.at (label "poke") = some ⟨poke⟩ →
    FunDecls.at (label "many") = some ⟨many n⟩ →
    ∀ (s : MachineData) (ra : Int64),
      Triple (many n)
        (fun s₀ => s₀ = MachineData.push64 s ra
          ∧ Mem.Mapped [(s.regs.rsp.toBitVec - 16#64, 8)] s.dmem
          ∧ Mem.Mapped [(s.regs.rsp.toBitVec - 8#64, 8), (s.regs.rdx.toBitVec, 16)] s.dmem
          ∧ Mem.Blocks.Disjoint [(s.regs.rdx.toBitVec, 16)] [Mem.Block.ofStackSlots s.regs.rsp 1]
          ∧ Mem.Mapped [(s.regs.rdi.toBitVec, 8 * n)] s.dmem
          ∧ Mem.Blocks.Disjoint [(s.regs.rdi.toBitVec, 8 * n)] [(s.regs.rsp.toBitVec - 16#64, 8)]
          ∧ Mem.Blocks.Disjoint [(s.regs.rdi.toBitVec, 8 * n)] [(s.regs.rsp.toBitVec - 8#64, 8)]
          ∧ Mem.Blocks.Disjoint [(s.regs.rdx.toBitVec, 16)] [(s.regs.rdi.toBitVec, 8 * n)])
        (fun (_ : Unit) (_ : MachineData) => False)
        (fun a s' => (a = ra →
            s'.dmem.loadBytes s.regs.rdx.toBitVec 16 = s.dmem.loadBytes s.regs.rdx.toBitVec 16)
          ∧ (a ≠ ra → False))

example : Goal 4 := by
  simp only [Goal, many, pokes]
  intro _ _ _ _ _ _ _ _
  vcgen [poke_spec]
    invariants
    · fun {s₀} l s' => match l with
        | "many" => s' = s₀
        | _ => False
    · fun _ _ => 0
    with kfinish

end ChangingFrames
