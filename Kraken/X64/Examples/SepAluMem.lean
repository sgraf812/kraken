/-
`alu_mem` in the separation wp: the four-instruction program of the baseline
example, with the slot at `136(%rdx)` owned as a `UInt64`. The post fixes the register
and owns the slot with the stored value.
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

def alu_mem : Program := parse("
  movq $42, %rax
  movq %rax, 136(%rdx)
  movq $100, %rcx
  addq 136(%rdx), %rcx
")

theorem alu_mem_correct [CodeEnv] (v : UInt64) :
    ⦃ fun r z f => MProp.bytesAt v.toBytes (r.get64 .rdx + 136#64) ⦄
      alu_mem
    ⦃ fun _ r z f => ⌜r.get64 .rcx = 142#64⌝
        ⊓ MProp.bytesAt (Int.toBytes 8 42) (r.get64 .rdx + 136#64) ⦄ := by
  vcgen [alu_mem] with finish
