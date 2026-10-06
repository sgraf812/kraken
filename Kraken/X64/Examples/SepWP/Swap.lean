module

/-
`swap` in the separation wp: three `xor`s exchange `rax` and `rbx`. The
program owns no memory.
-/
import Kraken.SepFrameProc
import Kraken.X64.Parser

open Kraken.X64.Parser
open Kraken
open Std.WP
open Lean.Order
open scoped Program.FrameWP

set_option experimental.vcgen true

attribute [local grind ←] Lean.Order.le_ofProp

def swap : Program := parse("
  xor %rbx, %rax
  xor %rax, %rbx
  xor %rbx, %rax")

theorem swap_spec [LinkedProgram] (a b : BitVec 64) :
    ⦃ fun r _ _ => ⌜r.get Reg.rax = a ∧ r.get Reg.rbx = b⌝ ⊓ MProp.emp ⦄
      swap
    ⦃ fun _ r _ _ => ⌜r.get Reg.rax = b ∧ r.get Reg.rbx = a⌝ ⦄ := by
  kvcgen64 [swap] with finish

/-! ## The baseline statement

`swap_spec` read back as the judgment of the baseline example `swap_correct`,
over the same program text. -/

theorem swap_correct [layout : _root_.Layout] [Kraken.Executable.Assembled (layout swap)] (d : MachineData) :
      Eventually (straightlineStep (layout swap))
      (fun s' =>
          s'.1.regs.get Reg.rax = d.regs.get Reg.rbx ∧
          s'.1.regs.get Reg.rbx = d.regs.get Reg.rax)
      (d, Kraken.Layout.start Directive) := by
  apply Program.FrameWP.straightline_of_wp (footprint := MProp.emp)
    (frame := MProp.mk fun _ => True) (by rw [MProp.emp_sep, MProp.get_mk]; trivial)
  kvcgen64 [swap] with finish
