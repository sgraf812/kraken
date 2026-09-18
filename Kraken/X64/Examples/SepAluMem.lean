/-
`alu_mem` in the separation wp: the four-instruction program of the baseline
example, with the slot at `136(%rdx)` owned as a `UInt64`. The post is the
register's value; the slot and its frame are carried by the frame rule.
-/
import Kraken.SepFrameProc
import Kraken.X64.Parser

open Kraken.X64.Parser
open Kraken
open Std.WP
open Lean.Order
open scoped SepWP

set_option mvcgen.warning false

def alu_mem : Program := parse("
  movq $42, %rax
  movq %rax, 136(%rdx)
  movq $100, %rcx
  addq 136(%rdx), %rcx
")

theorem alu_mem_correct [CodeEnv] (v : UInt64) :
    ⦃ fun r z f => MProp.bytesAt v.toBytes (r.get64 .rdx + 136#64) ⦄
      alu_mem
    ⦃ fun _ r z f => ⌜r.get64 .rcx = 142#64⌝ ⦄ := by
  have hv := UInt64.toBytes_length v
  have h42 : BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 42)) = 42#64 := by decide
  vcgen [alu_mem]
  all_goals first
    | exact SepWP.frames_directive _ _
    | exact hv
    | (simp only [Int.toBytes_length]; done)
    | (refine Lean.Order.le_ofProp _ _ ?_; simp [h42])
