/-
The `alu_mem` example on the separation wp: a constant goes to `rax`, through
the slot at `136(%rdx)`, and back into an addition, with the slot the one
owned resource. The proof chains the four dictionary specs by hand; the frame
inference of `vcgen` will replace the chaining.
-/
import Kraken.SepSpecs
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped SepWP

/-- The program: write 42 through memory, read it back into an addition. -/
def aluMem : Program := parse("
  mov $42, %rax
  mov %rax, 136(%rdx)
  mov $100, %rcx
  add 136(%rdx), %rcx
")

theorem aluMem_correct [CodeEnv] (bs : List UInt8) (hlen : bs.length = 8) :
    ⦃ fun r _ _ => MProp.bytesAt bs (r.get64 .rdx + 136#64) ⦄
      aluMem
    ⦃ fun _ r _ _ => fun m => r.get64 .rcx = 142#64
        ∧ MProp.bytesAt (Int.toBytes 8 (42#64 : BitVec 64).toInt)
            (r.get64 .rdx + 136#64) m;
      fun _ _ _ _ => (⊥ : MProp 64) ⦄ := by
  refine ⟨?_⟩
  show _ ⊑ WP.wp (Directive.instr (.regular .W64 .W64
      (.mov (.reg (.low .rax .W64)) (.imm (.int64 42)))) :: _) _ _
  refine PartialOrder.rel_trans ?_ (SepWP.mov_reg_imm_spec .W64 .rax 42).le_wp
  intro r z f
  refine PartialOrder.rel_trans ?_ ((SepWP.mov_store_reg_spec .rdx 136 .rax bs hlen).le_wp
    (r.set64 .rax (BitVec.setWidth 64 (42 : Int64).toBitVec)) z f)
  -- the footprint is the whole precondition; the wand absorbs `emp`
  rw [show (r.set64 .rax (BitVec.setWidth 64 (42 : Int64).toBitVec)).get64 .rdx
      = r.get64 .rdx by simp]
  refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (MProp.sep_emp _).symm) ?_
  refine MProp.sep_mono_right _ (MProp.wand_intro ?_)
  rw [MProp.sep_emp,
    show ((r.set64 Reg64.rax (BitVec.setWidth 64 (Int64.toBitVec 42))).get64 Reg64.rax)
      = 42#64 by simp,
    show BitVec.ofInt 64 (Int64.toInt 136) = 136#64 from rfl]
  -- the two register writes between the store and the add
  refine PartialOrder.rel_trans ?_
    ((SepWP.mov_reg_imm_spec .W64 .rcx 100).le_wp _ z f)
  refine PartialOrder.rel_trans ?_
    ((SepWP.add_reg_mem_spec .rcx .rdx 136 (Int.toBytes 8 (42#64).toInt)
      (Int.toBytes_length 8 _)).le_wp _ z f)
  simp only [Reg64s.get64_set64, reduceIte,
    show BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 (42#64).toInt)) = 42#64 from
      BitVec.ofInt_ofBytes_toBytes 64 8 rfl 42#64,
    show BitVec.setWidth 64 (Int64.toBitVec 100) = 100#64 from rfl,
    show BitVec.ofInt 64 (Int64.toInt 136) = 136#64 from rfl]
  refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (MProp.sep_emp _).symm) ?_
  refine MProp.sep_mono_right _ (MProp.wand_intro ?_)
  rw [MProp.sep_emp]
  refine PartialOrder.rel_trans ?_ ((SepWP.nil_spec).le_wp _ z _)
  intro m hm
  refine ⟨by simp, ?_⟩
  simpa using hm
