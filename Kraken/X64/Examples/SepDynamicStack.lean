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

attribute [local grind ←] Lean.Order.le_ofProp MProp.SliceBound.intro
attribute [local grind =] Int.toBytes_length ofBytes_toBytes List.length_take List.length_drop

theorem dynamic_stack_correct [CodeEnv] (stack : List UInt8) (lstack : stack.length = 1024)
    (r₀ : Reg64s) (h : (r₀.get64 .r9).toNat + (r₀.get64 .r15).toNat < 125) :
    ⦃ fun r z f => ⌜r = r₀⌝ ⊓ MProp.bytesAt stack (r.get64 .rsp - 1024#64) ⦄
      dynamic_stack
    ⦃ fun _ r z f => ⌜r.get64 .rax = 42#64 ∧ r.get64 .rbx = 99#64 ∧ r.get64 .rsp = r₀.get64 .rsp⌝ ⦄ := by
  -- the offsets of the two slots in the region, as the frameproc computes them
  have hsaved : (r₀.get64 .rsp + 18446744073709551608#64 - (r₀.get64 .rsp - 1024#64)).toNat
      = 1016 := by bv_omega
  have hslot : (r₀.get64 .rsp + r₀.get64 .r9 * 8#64 + 18446744073709550592#64
      + r₀.get64 .r15 * 8#64 + 16#64 - (r₀.get64 .rsp - 1024#64)).toNat
      = 8 * (r₀.get64 .r9).toNat + 8 * (r₀.get64 .r15).toNat + 16 := by bv_omega
  vcgen [dynamic_stack] with finish
