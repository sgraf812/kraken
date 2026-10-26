module

public import Kraken.X64.Examples.ButterfliesBlocks

/-!
# Butterflies: an SSE loop over two arrays

The loop of `ButterfliesBlocks.lean`, stated over the arrays' bytes. The loop
walks two 16-byte-aligned float arrays `v1`, `v2` of `len` floats (`4 * len`
bytes) in 16-byte chunks, replacing `(a, b)` by `(a + b, a - b)`.

We prove that the loop terminates without faulting, and that on exit the two
arrays (with some new contents) are still where they were, separated from each
other and from the frame `R`.

`butterflies_bytes` reads `ButterfliesBlocks.butterflies_correct` at the bytes:
the two arrays, with their contents, are the two blocks, and the blocks on exit
are two arrays with some contents.
-/

open Std.WP
open scoped Program.WP

namespace State.Butterflies

open State.ButterfliesBlocks Std.ExtHashMap

theorem butterflies_bytes [Host] [FunDecls] (d : MachineData) (v1 v2 : List UInt8) (len : Nat)
    (h_len_reg : (d.regs.get64 .rdx).take 32 = BitVec.ofNat 32 len)
    (h_len_mod : len % 4 = 0) (h_len_bound : len * 4 < 2 ^ 31) (h_len_gt : len > 0)
    (h_v1_len : v1.length = len * 4) (h_v2_len : v2.length = len * 4)
    (h_v1_aligned : isAligned 16 (d.regs.get64 .rdi) = true)
    (h_v2_aligned : isAligned 16 (d.regs.get64 .rsi) = true)
    (R : DataMem → Prop)
    (h_mem : d.dmem =⋆ Eq (v1.At (d.regs.get64 .rdi)) ⋆ Eq (v2.At (d.regs.get64 .rsi)) ⋆ R) :
    WP.wp butterflies_float_prog
      (fun _ t => ∃ v1' v2' : List UInt8, v1'.length = len * 4 ∧ v2'.length = len * 4 ∧
        t.dmem =⋆ Eq (v1'.At (d.regs.get64 .rdi)) ⋆ Eq (v2'.At (d.regs.get64 .rsi)) ⋆ R)
      (fun _ _ => False) d := by
  have hw : len * 4 ≤ 2 ^ 64 := by omega
  have hb : d.dmem =⋆
      Mem.Blocks [(d.regs.get64 .rdi, len * 4), (d.regs.get64 .rsi, len * 4)] ⋆ R := by
    rw [Mem.Blocks_cons_sep, Mem.Blocks_cons_sep, Mem.Blocks_nil_sep]
    rw [sep_assoc] at h_mem
    have h1 := Mem.Block.sep_intro h_v1_len hw h_mem
    rw [sep_comm_l] at h1
    have h2 := Mem.Block.sep_intro h_v2_len hw h1
    rwa [sep_comm_l] at h2
  refine Program.wp_mono (fun u hu => ?_) (fun _ h => h)
    (butterflies_correct d len h_len_reg h_len_mod h_len_bound h_len_gt h_v1_aligned
      h_v2_aligned R hb)
  have hu : u.data.dmem =⋆
      Mem.Block (d.regs.get64 .rdi) (len * 4) ⋆ (Mem.Block (d.regs.get64 .rsi) (len * 4) ⋆ R) := by
    rwa [Mem.Blocks_cons_sep, Mem.Blocks_cons_sep, Mem.Blocks_nil_sep] at hu
  obtain ⟨-, v1', h1, hu⟩ := Mem.Block.sep_elim hu
  rw [sep_comm_l] at hu
  obtain ⟨-, v2', h2, hu⟩ := Mem.Block.sep_elim hu
  rw [sep_comm_l, ← sep_assoc] at hu
  exact ⟨v1', v2', h1, h2, hu⟩

end State.Butterflies
