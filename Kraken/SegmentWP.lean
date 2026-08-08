/-
Weakest preconditions on the deep embedding. The program of a triple is the
sized directive segment that `Executable.directivesFromAddress` yields, and
its predicate transformer runs the baseline omni-semantics: the wp of a
segment `ds` at `(labels, st)` demands `Effects.All` of the postcondition
over `Directives.interp` from `st`, so a postcondition is a predicate on the
`MachineState` at the exit. The baseline delivers a jump out of
the segment and running past its final directive to the same continuation, so
every exit reaches the success postcondition and the exception row is
`EPost⟨⟩`. `straightlineStep_of_wp` converts the transformer into the
judgment that `Eventually` composes.
-/
import Kraken.Specs

open Std.Internal.Do

/-- `Effects.All` is monotone in the postcondition. -/
theorem Effects.All.mono {p q : MachineState → Prop} (h : ∀ st, p st → q st) :
    ∀ e : Effects, e.All p → e.All q := by
  intro e
  induction e with
  | done a => exact h a
  | unimplemented _ => exact id
  | nonmem_load _ _ _ _ => exact id
  | nonmem_store _ _ _ _ => exact id
  | undefined _ ih => exact fun hp v => ih v (hp v)
  | require_read_access _ _ _ ih => exact fun hp => ih () hp
  | require_write_access _ _ _ ih => exact fun hp => ih () hp
  | require_exec_access _ _ ih => exact fun hp => ih () hp

/-- The predicate transformer of a straightline segment: every resolution of
the baseline omni-semantics reaches an exit state satisfying the
postcondition. -/
def Directives.wpTrans (ds : List (Directive × Nat)) :
    PredTrans (Labels → MachineState → Prop) EPost⟨⟩ Unit :=
  ⟨fun Q _E labels st =>
    (@Directives.interp labels ds st.1 st.2 (fun pc s' => .done (s', pc))).All (Q () labels)⟩

instance instWPDirectives :
    WP (List (Directive × Nat)) Unit (Labels → MachineState → Prop) EPost⟨⟩ where
  wpTrans := Directives.wpTrans
  wp_trans_monotone _ _ _ _ _ _ hQ := fun labels _ =>
    Effects.All.mono (hQ () labels) _

@[simp] theorem Directives.wp_nil (Q : Unit → Labels → MachineState → Prop)
    (E : EPost⟨⟩) (labels : Labels) (st : MachineState) :
    wp ([] : List (Directive × Nat)) Q E labels st = Q () labels st := rfl

/-- A segment triple establishes the omni-semantics straightline judgment: the
segment at `pc` is the wp's program, the judgment's postcondition is the wp's,
read off the rip and machine slots at the exit. -/
theorem straightlineStep_of_wp [Layout] {e : Executable} {s : MachineData} {pc : Int64}
    {post : MachineState → Prop}
    (h : wp (e.directivesFromAddress pc) (fun _ _ => post) epost⟨⟩ e.labels (s, pc)) :
    straightlineStep e (s, pc) post :=
  h

/- `straightlineStep` is the API boundary: every proof enters through
`straightlineStep_of_wp`. Sealing it stops the elaborator from partially
evaluating the interpreter on a concrete executable whenever a goal or
expected type is headed by it, which gets stuck only after seconds of
symbolic `withAddresses`/`idxOf` reduction. -/
set_option allowUnsafeReducibility true in
attribute [irreducible] straightlineStep

/- Same seal for the segment computation: reducing `directivesFromAddress` on
a concrete executable partially evaluates `withAddresses` and `idxOf` over a
symbolic layout. Its API is the extraction equations
(Kraken/SegmentExtract.lean), which rewrite syntactically. -/
set_option allowUnsafeReducibility true in
attribute [irreducible] Executable.directivesFromAddress

/-! ## Per-instruction specs

One triple per instruction shape, stated on the cons cell: the precondition is
the wp of the tail applied to the record update the instruction performs, with
rip advanced by the carried size. Each proof unfolds the one instruction of
`Directives.interp` and lands on the tail's wp. -/

/-- Unfold a segment wp into the omni-semantics fold. -/
theorem Directives.wp_eq (ds : List (Directive × Nat))
    (Q : Unit → Labels → MachineState → Prop) (E : EPost⟨⟩)
    (labels : Labels) (st : MachineState) :
    wp ds Q E labels st =
      (@Directives.interp labels ds st.1 st.2 (fun pc s' => .done (s', pc))).All
        (Q () labels) := rfl

section Specs

variable {Q : Unit → Labels → MachineState → Prop} {E : EPost⟨⟩}
  {ds : List (Directive × Nat)}

/-- Unfold one instruction of the segment wp: the wp equation, the directive
and instruction interpreters, operand evaluation, and the `Effects.All`
equations, normalizing register access to `get64`/`set64`. -/
local macro "wp_step" : tactic =>
  `(tactic| simp only [Directives.wp_eq, Directives.interp, Directive.interp, Instr.interp,
      Operation.interp, Operand.interp, RegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, Reg64s.get_low64, Reg64s.set_low64, Effects.All])

@[spec] theorem Directives.nil_spec :
    ⦃ fun labels st => Q () labels st ⦄ (([] : List (Directive × Nat))) ⦃ Q; E ⦄ :=
  Triple.intro fun _ _ h => h

@[spec] theorem Directives.label_spec (l : Label) (sz : Nat) :
    ⦃ fun labels st => wp ds Q E labels (st.1, st.2 + .ofNat sz) ⦄
      ((Directive.label l, sz) :: ds)
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ _ h => by wp_step; exact h

@[spec] theorem Directives.nop_spec (asz osz : Width) (n sz : Nat) :
    ⦃ fun labels st => wp ds Q E labels (st.1, st.2 + .ofNat sz) ⦄
      ((Directive.instr (.regular asz osz (.nop n)), sz) :: ds)
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ _ h => by wp_step; exact h

@[spec] theorem Directives.mov_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) (sz : Nat) :
    ⦃ fun labels st =>
        wp ds Q E labels
          ({ st.1 with regs := st.1.regs.set64 r (BitVec.setWidth 64 i.toBitVec) },
            st.2 + .ofNat sz) ⦄
      ((Directive.instr (.regular asz .W64 (.mov (.reg (.low r .W64)) (.imm (.int64 i)))), sz) :: ds)
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ _ h => by wp_step; exact h

@[spec] theorem Directives.sub_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) (sz : Nat) :
    ⦃ fun labels st =>
        let b := st.1.regs.get64 r
        let a := BitVec.setWidth 64 i.toBitVec
        let v := b - a
        wp ds Q E labels
          ({ st.1 with
              regs := st.1.regs.set64 r v,
              status := StatusFlags.from_result v
                { cf := v.unsigned != b.unsigned - a.unsigned,
                  af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                  of := v.signed != b.signed - a.signed } },
            st.2 + .ofNat sz) ⦄
      ((Directive.instr (.regular asz .W64 (.sub (.reg (.low r .W64)) (.imm (.int64 i)))), sz) :: ds)
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ _ h => by wp_step; exact h

@[spec] theorem Directives.mulx_reg_spec (asz : Width) (hi lo rs : Reg64) (sz : Nat) :
    ⦃ fun labels st =>
        let v := (st.1.regs.get64 rs).unsigned * (st.1.regs.get64 .rdx).unsigned
        wp ds Q E labels
          ({ st.1 with regs :=
              (st.1.regs.set64 lo (BitVec.ofInt 64 v)).set64 hi (BitVec.ofInt 64 (v >>> 64)) },
            st.2 + .ofNat sz) ⦄
      ((Directive.instr (.regular asz .W64
          (.mulx (.low hi .W64) (.low lo .W64) (.reg (.low rs .W64)))), sz) :: ds)
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ _ h => by wp_step; exact h

@[spec] theorem Directives.jcc_spec (asz osz : Width) (cc : CondCode) (l : Label) (sz : Nat) :
    ⦃ fun labels st =>
        if cc.interp st.1.status then Q () labels (st.1, labels.label l)
        else wp ds Q E labels (st.1, st.2 + .ofNat sz) ⦄
      ((Directive.instr (.regular asz osz (.jcc cc l)), sz) :: ds)
    ⦃ Q; E ⦄ :=
  Triple.intro fun labels st h => by
    wp_step
    split <;> rename_i hc <;> simp only [hc, reduceIte] at h <;> exact h

@[spec] theorem Directives.jmp_label_spec (asz osz : Width) (l : Label) (sz : Nat) :
    ⦃ fun labels st => Q () labels (st.1, labels.label l) ⦄
      ((Directive.instr (.regular asz osz
          (.jmp (.rel (.sub (.label l) .after_current_instruction)))), sz) :: ds)
    ⦃ Q; E ⦄ :=
  Triple.intro fun labels st h => by
    wp_step
    have hcancel : st.2 + .ofNat sz + (labels.label l - (st.2 + .ofNat sz))
        = labels.label l := by
      apply Int64.toBitVec_inj.mp
      simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    simp only [hcancel, Int64.ofBitVec_toBitVec]
    exact h

end Specs

-- Driver compatibility check: `vcgen` steps a deep segment by applying the
-- registered cons specs and leaves the postcondition on the updated state.
set_option mvcgen.warning false in
example :
    ⦃ fun (_ : Labels) (_ : MachineState) => True ⦄
      (([(Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low .rax .W64)) (.imm (.int64 1)))), 5)]) : List (Directive × Nat))
    ⦃ fun _ _ st => st.1.regs.get64 .rax = 1#64 ⦄ := by
  vcgen
  all_goals simp
