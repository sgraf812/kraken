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

set_option experimental.vcgen true


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
attribute [local grind =] Int.toBytes_length BitVec.ofInt_ofBytes_toBytes List.length_take List.length_drop

theorem dynamic_stack_correct [CodeEnv] (stack : List UInt8) (lstack : stack.length = 1024)
    (r₀ : Reg64s) (h : (r₀.get64 .r9).toNat + (r₀.get64 .r15).toNat < 125) :
    ⦃ fun r z f => ⌜r = r₀⌝ ⊓ MProp.bytesAt stack (r.get64 .rsp - 1024#64) ⦄
      dynamic_stack
    ⦃ fun _ r z f => ⌜r.get64 .rax = 42#64 ∧ r.get64 .rbx = 99#64 ∧ r.get64 .rsp = r₀.get64 .rsp⌝ ⦄ := by
  vcgen [dynamic_stack] with finish

/-! ## The baseline statement

`dynamic_stack_correct` read back as the judgment of the baseline example
`dynamic_stack_example_correct`, over the same program text: a run from any
state whose memory holds the region below the stack pointer next to a frame
`R` ends with the three registers as stated. -/

section Baseline

variable [layout : _root_.Layout] [Executable.ValidLayout (layout dynamic_stack)]

local instance dynamic_stack.env : CodeEnv := ⟨layout dynamic_stack⟩

theorem dynamic_stack_example_correct (s₀ : MachineData)
    (stack : List UInt8) (lstack : stack.length = 1024) (R : Mem 64 → Prop)
    (h : s₀.regs.r9.toNat + s₀.regs.r15.toNat < 125)
    (h_mem : s₀.dmem =⋆ Eq (stack.At (s₀.regs.rsp.toBitVec - 1024)) ⋆ R) :
    Eventually (straightlineStep (layout dynamic_stack))
      (fun s' => s'.1.regs.rax = 42 ∧ s'.1.regs.rbx = 99 ∧ s'.1.regs.rsp = s₀.regs.rsp)
      (s₀, Kraken.Layout.start Directive) := by
  have hpre : (R ∗ (⌜s₀.regs = s₀.regs⌝ ⊓ MProp.bytesAt stack (s₀.regs.get64 .rsp - 1024#64)))
      s₀.dmem := by
    obtain ⟨m₁, m₂, hu, hd, hm₁, hR⟩ := h_mem
    refine ⟨m₂, m₁, ?_, Std.ExtHashMap.disjoint_symm hd, hR, (MProp.meet_apply _ _ m₁).mpr
      ⟨(MProp.ofProp_apply_iff _ m₁).mpr rfl, by simpa [Reg64s.get64_rsp, MProp.bytesAt] using hm₁⟩⟩
    rw [← hu]; exact (Std.ExtHashMap.union_comm_of_disjoint m₁ m₂ hd).symm
  have hrun := run_of_sep_triple
    (dynamic_stack_correct stack lstack s₀.regs (by simpa [Reg64s.get64_r9, Reg64s.get64_r15] using h)).le_wp
    R hpre
  refine eventually_weaken _ _ _ _ (fun st hst => ?_) hrun
  have hφ := MProp.sep_ofProp_elim hst
  simp only [Reg64s.get64_rax, Reg64s.get64_rbx, Reg64s.get64_rsp] at hφ
  obtain ⟨h1, h2, h3⟩ := hφ
  exact ⟨UInt64.toBitVec_inj.mp h1, UInt64.toBitVec_inj.mp h2, UInt64.toBitVec_inj.mp h3⟩

end Baseline
