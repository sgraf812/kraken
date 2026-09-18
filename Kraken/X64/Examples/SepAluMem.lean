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

/-! ## The baseline statement

`alu_mem_correct` read back as the judgment of the baseline example
`alu_mem_example_correct`, over the same program text. -/

section Baseline

variable [layout : _root_.Layout] [Executable.ValidLayout (layout alu_mem)]

local instance alu_mem.env : CodeEnv := ⟨layout alu_mem⟩

theorem alu_mem_example_correct (s₀ : MachineData) (v : UInt64) (R : Mem 64 → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v.At (s₀.regs.rdx.toBitVec + 136#64)) ⋆ R) :
    Eventually (straightlineStep (layout alu_mem))
      (fun s' => s'.1.regs.rcx = 142)
      (s₀, Kraken.Layout.start Directive) := by
  have hpre : (R ∗ MProp.bytesAt v.toBytes (s₀.regs.get64 .rdx + 136#64)) s₀.dmem := by
    obtain ⟨m₁, m₂, hu, hd, hm₁, hR⟩ := h_mem
    refine ⟨m₂, m₁, ?_, Std.ExtHashMap.disjoint_symm hd, hR,
      by simpa [Reg64s.get64_rdx, UInt64.At, MProp.bytesAt] using hm₁⟩
    rw [← hu]; exact (Std.ExtHashMap.union_comm_of_disjoint m₁ m₂ hd).symm
  have hrun := run_of_sep_triple (alu_mem_correct v).le_wp R hpre
  refine eventually_weaken _ _ _ _ (fun st hst => ?_) hrun
  have hφ : st.1.regs.get64 .rcx = 142#64 := by
    obtain ⟨m₁, m₂, hu, hd, hR, hq⟩ := hst
    exact (MProp.ofProp_apply_iff _ m₂).mp ((MProp.meet_apply _ _ m₂).mp hq).1
  simp only [Reg64s.get64_rcx] at hφ
  exact UInt64.toBitVec_inj.mp hφ

end Baseline
