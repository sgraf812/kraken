/-
`dynamic_stack` in the separation wp: a frame is carved out of a 1024-byte
region below the stack pointer at an offset that depends on two registers, a
value is stored into and loaded back from a slot of that frame, and a value
saved below the entry stack pointer is restored at the end. The precondition
owns the region; the post fixes the three registers.
-/
import Kraken.SepFrameProc
import Kraken.X64.Parser

open Kraken.X64.Parser
open Kraken
open Std.WP
open Lean.Order
open scoped SepWP

set_option mvcgen.warning false
set_option maxRecDepth 20000


/-- The offset of the saved cell in the region: `-8(%rsp)` sits `1016` bytes
above `rsp - 1024`. -/
theorem off_saved (x : BitVec 64) :
    x + 18446744073709551608#64 - (x - 1024#64) = 1016#64 := by bv_decide

/-- The offset of the frame slot in the region: `16(%rsp', %r15, 8)` with
`rsp' = rsp + 8·r9 - 1024` sits `8·r9 + 8·r15 + 16` bytes above `rsp - 1024`. -/
theorem off_slot (x a b : BitVec 64) :
    x + a * 8#64 + 18446744073709550592#64 + b * 8#64 + 16#64 - (x - 1024#64)
      = a * 8#64 + b * 8#64 + 16#64 := by bv_decide

def dynamic_stack : Program := parse("
  movq $99, -8(%rsp)
  movq %rsp, %rbp
  leaq -1024(%rsp, %r9, 8), %rsp
  movq $42, %rax
  movq %rax, 16(%rsp, %r15, 8)
  movq $0, %rax
  movq 16(%rsp, %r15, 8), %rax
  movq %rbp, %rsp
  movq -8(%rsp), %rbx
")

attribute [local grind ←] Lean.Order.le_ofProp
attribute [local grind =] Int.toBytes_length ofBytes_toBytes off_saved off_slot
  List.length_take List.length_drop
attribute [local grind] MProp.SliceBound

set_option maxHeartbeats 400000 in
theorem dynamic_stack_correct [CodeEnv] (stack : List UInt8) (lstack : stack.length = 1024)
    (r₀ : Reg64s) (h : (r₀.get64 .r9).toNat + (r₀.get64 .r15).toNat < 125) :
    ⦃ fun r z f => ⌜r = r₀⌝ ⊓ MProp.bytesAt stack (r.get64 .rsp - 1024#64) ⦄
      dynamic_stack
    ⦃ fun _ r z f => ⌜r.get64 .rax = 42#64 ∧ r.get64 .rbx = 99#64 ∧ r.get64 .rsp = r₀.get64 .rsp⌝ ⦄ := by
  vcgen [dynamic_stack] with finish
