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

namespace ManyCalls

public def touch : Program := parse("
touch:
  ret
")

public funspec touch_spec "touch" [Host] [FunDecls] [Embeds touch]
    (ht : FunDecls.at (label "touch") = some ⟨touch⟩) at s
    requires Mem.Mapped [(s.regs.rsp.toBitVec - 8#64, 8)] s.dmem
    ensures s' => True
    autoframes calling_conv SysV preserves rax rcx rdx rsi rdi r8 r9 r10 r11 := by
  vcgen [touch]
    invariants
    · fun s₀ l s' => match l with
        | "touch" => s' = s₀
        | _ => False
    · fun _ _ => 0
    with kfinish

@[expose] public def calls : Nat → Program
  | 0 =>
    [Directive.instr (.regular .W64 .W64
        (.mov (.reg (.low .rax .W64)) (.imm (.int64 0)))),
      Directive.instr (.regular .W64 .W64
        (.add (.reg (.low .rax .W64))
          (.regOrMem (.mem { base := some (.reg .rdi), idx := none, disp := .int64 0 })))),
      Directive.instr (.regular .W64 .W64 .ret)]
  | n + 1 =>
    Directive.instr (.regular .W64 .W64
      (.call (.rel (.sub (.label "touch") .after_current_instruction)))) :: calls n

@[expose] public def many (n : Nat) : Program := Directive.label "many" :: calls n

@[expose] public def Goal (n : Nat) : Prop :=
  ∀ [Host] [FunDecls] [Embeds touch] [Embeds (many n)],
    FunDecls.at (label "touch") = some ⟨touch⟩ →
    FunDecls.at (label "many") = some ⟨many n⟩ →
    ∀ (s : MachineData) (ra : Int64),
      Triple (many n)
        (fun s₀ => s₀ = MachineData.push64 s ra
          ∧ Mem.Mapped [(s.regs.rsp.toBitVec - 16#64, 8)] s.dmem
          ∧ Mem.Mapped [(s.regs.rsp.toBitVec - 8#64, 8), (s.regs.rdi.toBitVec, 8),
            (s.regs.rdx.toBitVec, 16)] s.dmem
          ∧ Mem.Blocks.Disjoint [(s.regs.rdi.toBitVec, 8)] [Mem.Block.ofStackSlots s.regs.rsp 1]
          ∧ Mem.Blocks.Disjoint [(s.regs.rdx.toBitVec, 16)] [Mem.Block.ofStackSlots s.regs.rsp 1])
        (fun (_ : Unit) (_ : MachineData) => False)
        (fun a s' => (a = ra →
            s'.dmem.loadInt s.regs.rdi.toBitVec 8 = s.dmem.loadInt s.regs.rdi.toBitVec 8
            ∧ s'.dmem.loadBytes s.regs.rdx.toBitVec 16 = s.dmem.loadBytes s.regs.rdx.toBitVec 16)
          ∧ (a ≠ ra → False))

end ManyCalls
