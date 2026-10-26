module

public import Kraken.StateCfg
public import Kraken.SeparationMem
import Kraken.X64.Parser

/-!
# Butterflies over blocks: an SSE loop over two arrays

A variant of `Butterflies.lean` that states the machine-level theorem over
`Mem.Blocks`: each array is an owned region of `4 * len` bytes whose contents
are not tracked. (`Butterflies.lean` states it over the arrays' bytes, and
converts to and from blocks.)

The loop walks two 16-byte-aligned float arrays `v1`, `v2` of `len` floats
(`4 * len` bytes) in 16-byte chunks, replacing `(a, b)` by `(a + b, a - b)`.
Both pointers are first advanced to one past the end of their array, and a
single negative index `rdx` counts up towards zero, so the loop needs only one
`add` and a `jl`.

We prove that the loop terminates without faulting, and that on exit the two
arrays (with some new contents) are still where they were, separated from each
other and from the frame `R`.

`butterflies_correct` is the program's `wp`, proved through the control-flow
rule `Program.WP.cfg`: the table gives the assertion at each label (at `loop`,
the loop invariant), the variant is the bytes still to process, and
`cfg_cases` produces one obligation per block, each closed by `kvcgen64`.
`Program.WP.step1_of_wp_at` reads the `wp` back at the machine
(`butterflies_float_terminates_and_safe`).
-/

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

/- The `sib1` rules leave a zero displacement as `+ 0` in the address. -/
attribute [local grind =] BitVec.add_zero


public section

namespace State.ButterfliesBlocks

/-- The program: the prologue moves both pointers to the end of their array
and negates the byte count into `rdx`; each iteration of the loop does one
16-byte chunk of both arrays. -/
def butterflies_float_prog : Program := parse("
start:
    shl $2, %edx
    add %rdx, %rdi
    add %rdx, %rsi
    neg %rdx
loop:
    movaps (%rdi,%rdx,1), %xmm0
    movaps (%rsi,%rdx,1), %xmm1
    movaps %xmm0, %xmm2
    subps %xmm1, %xmm2
    addps %xmm1, %xmm0
    movaps %xmm2, (%rsi,%rdx,1)
    movaps %xmm0, (%rdi,%rdx,1)
    add $16, %rdx
    jl loop
")

theorem butterflies_correct [Host] [FunDecls] (d : MachineData) (len : Nat)
    (h_len_reg : (d.regs.get64 .rdx).take 32 = BitVec.ofNat 32 len)
    (h_len_mod : len % 4 = 0) (h_len_bound : len * 4 < 2 ^ 31) (h_len_gt : len > 0)
    (h_v1_aligned : isAligned 16 (d.regs.get64 .rdi) = true)
    (h_v2_aligned : isAligned 16 (d.regs.get64 .rsi) = true)
    (R : DataMem → Prop)
    (h_mem : d.dmem =⋆
      Mem.Blocks [(d.regs.get64 .rdi, len * 4), (d.regs.get64 .rsi, len * 4)] ⋆ R) :
    WP.wp butterflies_float_prog
      (fun _ t => t.dmem =⋆
        Mem.Blocks [(d.regs.get64 .rdi, len * 4), (d.regs.get64 .rsi, len * 4)] ⋆ R)
      (fun _ _ => False) d := by
  refine Program.WP.cfg
    (fun b t =>
      let L := len * 4
      let j := (-t.regs.get64 .rdx).toNat
      match b with
      | .entry | .label "start" => t = d
      | .label "loop" =>
          t.regs.get64 .rdi = d.regs.get64 .rdi + BitVec.ofNat 64 L ∧
          t.regs.get64 .rsi = d.regs.get64 .rsi + BitVec.ofNat 64 L ∧
          0 < j ∧ j ≤ L ∧ j % 16 = 0 ∧ t.regs.get64 .rsp = d.regs.get64 .rsp ∧
          t.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, L), (d.regs.get64 .rsi, L)] ⋆ R
      | .exit => t.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, L), (d.regs.get64 .rsi, L)] ⋆ R
      | _ => False)
    (fun l t => match l with
      | "loop" => (-t.regs.get64 .rdx).toNat
      | _ => 2 ^ 64) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

end State.ButterfliesBlocks

end
