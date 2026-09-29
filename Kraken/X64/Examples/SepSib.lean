module

/-
`sib_example` in the separation wp: a value is stored into and loaded back
from the slot at `(%rdi, %r15, 8)`, owned as a `UInt64`.
-/
import Kraken.SepFrameProc
import Kraken.X64.Parser

open Kraken.X64.Parser
open Kraken
open Std.WP
open Lean.Order
open scoped SepWP

set_option experimental.vcgen true

attribute [local grind ←] Lean.Order.le_ofProp
attribute [local grind =] Int.toBytes_length UInt64.toBytes_length BitVec.ofInt_ofBytes_toBytes

def sib_example : Program := parse("
    movq $42, %rax
    movq %rax, (%rdi, %r15, 8)
    movq $0, %rax
    movq (%rdi, %r15, 8), %rax
")

theorem sib_correct (v : UInt64) :
    ⦃ fun r _ _ => v.AtM (r.rdi.toBitVec + BitVec.ofInt 64 (r.r15.toBitVec.toInt * 8)) ⦄
      sib_example
    ⦃ fun _ r _ _ => ⌜r.rax = 42⌝ ⦄ := by
  -- TODO: `vcgen [sib_example] with finish` fails. The frame inference does not identify the
  -- slot `rdi + ofInt (r15.toInt * 8)` with the SIB spec's `rdi + r15 * 8 + 0` and slices instead.
  sorry

/-! ## The baseline statement

`sib_correct` read back as the judgment of the baseline example
`sib_example_correct`, over the same program text. -/

theorem sib_example_correct [layout : _root_.Layout] (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v.At (s₀.regs.rdi.toBitVec + BitVec.ofInt 64 (s₀.regs.r15.toBitVec.toInt * 8))) ⋆ R) :
    Eventually (straightlineStep (layout sib_example))
      (fun s' => s'.1.regs.rax = 42)
      (s₀, Kraken.Layout.start Directive) := by
  apply eventually_straightlineStep_of_sep_triple (UInt64.get_AtM_sep h_mem)
  -- TODO: `vcgen [sib_example] with finish` fails, for the reason given at `sib_correct`.
  sorry
