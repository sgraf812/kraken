/-
`alu_mem` in the separation wp: a store of an immediate into a slot, then an
`add` from that slot into a register. The precondition owns the slot with any
contents and fixes the register; the post owns the slot with the immediate and
fixes the register's new value.
-/
import Kraken.SepFrameProc
import Kraken.X64.Parser

open Kraken.X64.Parser
open Kraken
open Std.WP
open Lean.Order
open scoped SepWP

set_option mvcgen.warning false

attribute [local grind ←] Lean.Order.le_ofProp
attribute [local grind =] Int.toBytes_length

def alu_mem : Program := parse("
  movq $42, 136(%rdx)
  addq 136(%rdx), %rcx
")

theorem alu_mem_correct [CodeEnv] (bs : List UInt8) (hlen : bs.length = 8) :
    ⦃ fun r z f => ⌜r.get64 .rcx = 100#64⌝
        ⊓ MProp.bytesAt bs (r.get64 .rdx + BitVec.ofInt 64 (136 : Int64).toInt) ⦄
      alu_mem
    ⦃ fun _ r z f => ⌜r.get64 .rcx = 142#64⌝
        ⊓ MProp.bytesAt (Int.toBytes 8 42) (r.get64 .rdx + BitVec.ofInt 64 (136 : Int64).toInt) ⦄ := by
  have h42 : (BitVec.setWidth 64 (42 : Int64).toBitVec).toInt = 42 := by decide
  have hback := BitVec.ofInt_ofBytes_toBytes 64 8 rfl (BitVec.setWidth 64 (42 : Int64).toBitVec)
  vcgen [alu_mem] with finish
