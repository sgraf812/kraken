module

public import Kraken.StateCfg
public import Kraken.SeparationMem
import Kraken.X64.Parser

/-!
# `ff_vector_fmul_sse`: an SSE loop that writes an array its inputs may overlap

FFmpeg's `vector_fmul` multiplies two vectors `src0`, `src1` of `len` floats
elementwise into a third, `dst` (`vector_fmul_c` in `libavutil/float_dsp.c`).
Its SSE version (`libavutil/x86/float_dsp.asm`, the `VECTOR_FMUL` macro under
`INIT_XMM sse`) walks the arrays from the end down, 64 bytes per iteration:
`lea` turns the float count in `ecx` into the offset of the last 64-byte chunk,
and each iteration loads the four 16-byte pieces of the chunk of `src0`,
multiplies them by those of `src1` (`mulps`), stores the products into `dst`,
and lowers the offset by 64, until it goes negative.

The program below is the routine's machine code, disassembled from the object
file, in the parser's AT&T syntax. The seven `nop`s are the `ALIGN 16` padding
before `.loop`. The final `ret` is left off, so a run ends by falling off the
end of the program after the `jge`, as in `SbrNegOdd64.lean`. Where an operand
has a displacement, NASM put the offset register in the base slot and the array
pointer in the index slot, as in `0x10(%rcx,%rsi,1)`.

We prove that the routine terminates without faulting, and that it writes no
memory outside `dst`: on exit, `dst` is still an owned block of `4 * len` bytes
(with new contents), and the rest of memory still satisfies the frame `R`. The
floats themselves are not tracked. Compared with the API in
`libavutil/float_dsp.h` (all three pointers 32-byte aligned, `len` a multiple
of 16), the proof finds:

* `len = 0` is not safe, although the API allows it. The 32-bit `lea` computes
  `4 * 0 - 64`, which wraps to `2^32 - 64`, and the loop, which tests at the
  bottom, then runs over the 4 GiB above each pointer. The precondition asks
  for `0 < len`.
* The byte count is computed in 32 bits. The precondition `len * 4 < 2^32`
  keeps it from wrapping. For `2^30 < len < 2^31` the wrap makes the loop
  multiply only the first `len - 2^30` floats: in bounds, but not what the
  caller asked for.
* The pointers need only 16-byte alignment, which the legacy SSE memory
  operands of `movaps` and `mulps` require; the API promises 32.
* The upper half of `rcx` is ignored: the ABI leaves it unspecified for an
  `int` argument, and the 32-bit `lea` reads only `ecx`.
* The prototype marks none of the pointers `restrict`, so the arrays may
  overlap in any way. The precondition owns each array in its own fact about
  the initial memory, and none of these facts says where one array is relative
  to another. The proof covers every overlap, but for safety only: with
  partially overlapping arrays, the routine can compute a different result than
  the C code, which runs from the first element up. Exact aliasing
  (`dst == src0` or `dst == src1`) gives the C code's result.

The proof has the shape of `ButterfliesBlocks.lean`: the table of
`Program.WP.cfg` gives the assertion at each label (at `.loop`, the loop
invariant), the variant is the offset of the current chunk, and `cfg_cases`
leaves one obligation per block, each closed by `kvcgen64`. The invariant keeps
`dst`'s block, which `Mem.Blocks.storeInt` carries across each store, and
`Mem.SubDom d.dmem s.dmem`: a store never unmaps an address, so the loads from
`src0` and `src1`, which their facts show readable in the initial memory, stay
readable whatever the stores into `dst` change.
-/

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

/- The `sib1` rules leave a zero displacement as `+ 0` in the address. -/
attribute [local grind =] BitVec.add_zero

namespace State.FfVectorFmulSse

/-- The program: `ff_vector_fmul_sse` from the object file, without its `ret`. -/
def vector_fmul_sse_prog : Program := parse("
start:
    lea -0x40(,%ecx,4),%rcx
    nop
    nop
    nop
    nop
    nop
    nop
    nop
.loop:
    movaps (%rsi,%rcx,1),%xmm0
    movaps 0x10(%rcx,%rsi,1),%xmm1
    mulps (%rdx,%rcx,1),%xmm0
    mulps 0x10(%rcx,%rdx,1),%xmm1
    movaps %xmm0,(%rdi,%rcx,1)
    movaps %xmm1,0x10(%rcx,%rdi,1)
    movaps 0x20(%rcx,%rsi,1),%xmm0
    movaps 0x30(%rcx,%rsi,1),%xmm1
    mulps 0x20(%rcx,%rdx,1),%xmm0
    mulps 0x30(%rcx,%rdx,1),%xmm1
    movaps %xmm0,0x20(%rcx,%rdi,1)
    movaps %xmm1,0x30(%rcx,%rdi,1)
    sub $0x40,%rcx
    jge .loop
")

theorem vector_fmul_sse_correct [Host] [FunDecls] (d : MachineData) (len : Nat)
    (h_len_reg : (d.regs.get64 .rcx).take 32 = BitVec.ofNat 32 len)
    (h_len_mod : len % 16 = 0) (h_len_pos : 0 < len) (h_len_bound : len * 4 < 2 ^ 32)
    (h_dst_aligned : isAligned 16 (d.regs.get64 .rdi) = true)
    (h_src0_aligned : isAligned 16 (d.regs.get64 .rsi) = true)
    (h_src1_aligned : isAligned 16 (d.regs.get64 .rdx) = true)
    (R R₀ R₁ : DataMem → Prop)
    (h_dst : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, len * 4)] ⋆ R)
    (h_src0 : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rsi, len * 4)] ⋆ R₀)
    (h_src1 : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdx, len * 4)] ⋆ R₁) :
    WP.wp vector_fmul_sse_prog
      (fun _ t => t.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, len * 4)] ⋆ R)
      (fun _ _ => False) d := by
  refine Program.WP.cfg
    (fun b t =>
      let L := len * 4
      let rcx := (t.regs.get64 .rcx).toNat
      match b with
      | .entry | .label "start" => t = d
      | .label ".loop" =>
          t.regs.get64 .rdi = d.regs.get64 .rdi ∧ t.regs.get64 .rsi = d.regs.get64 .rsi ∧
          t.regs.get64 .rdx = d.regs.get64 .rdx ∧ t.regs.get64 .rsp = d.regs.get64 .rsp ∧
          rcx + 64 ≤ L ∧ rcx % 64 = 0 ∧
          (t.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, L)] ⋆ R) ∧ Mem.SubDom d.dmem t.dmem
      | .exit => t.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, L)] ⋆ R
      | _ => False)
    (fun l t => match l with
      | "start" => 2 ^ 64
      | ".loop" => (t.regs.get64 .rcx).toNat
      | _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

end State.FfVectorFmulSse
