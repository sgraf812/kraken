/-
Weakest preconditions on the deep embedding. `Directive.wp1` is the
transformer of a single directive, with a fall-through postcondition and a
jump postcondition: each disjunct runs the baseline `Directive.interp` with
one continuation poisoned by the `Effects.All = False` leaf, so the left
disjunct states that every resolution falls through and the right that every
resolution jumps, at the target the interpreter hands to the jump
continuation. `Directives.wpE` folds `wp1` over a directive list, threading
the fall-through continuation and passing the jump postcondition through, so
`wpE (as ++ bs) Q E = wpE as (wpE bs Q E) E`. Kraken/SegmentWPSound.lean
recovers the closed straightline judgment as the diagonal `Q := E`.
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

/-- Every resolution of `d` falls through, into `next`: the jump continuation
is poisoned with the `All = False` leaf. -/
def Directive.stepFall [Labels] (d : Directive) (p : Std.Rco Int64) (s : MachineData)
    (next : MachineData → Prop) : Prop :=
  (d.interp s p (fun s' => .done (s', 0)) (fun _ _ => .unimplemented "jump")).All
    (fun st => next st.1)

/-- Every resolution of `d` jumps, into `jmp` at the interpreter's target: the
fall-through continuation is poisoned. -/
def Directive.stepJump [Labels] (d : Directive) (p : Std.Rco Int64) (s : MachineData)
    (jmp : MachineState → Prop) : Prop :=
  (d.interp s p (fun _ => .unimplemented "fallthrough") (fun pc' s' => .done (s', pc'))).All jmp

/-- The transformer of one directive. The disjunction is exact because
`Operation.interp` decides jump-ness before any nondeterminism: each tree
calls only one of its two continuations. -/
def Directive.wp1 [Labels] (d : Directive) (p : Std.Rco Int64)
    (next : MachineData → Prop) (jmp : MachineState → Prop) (s : MachineData) : Prop :=
  d.stepFall p s next ∨ d.stepJump p s jmp

/-- The transformer of a directive list: `Q` at fall-through past the final
directive, `E` at a jump out of any directive. -/
def Directives.wpE [Labels] :
    List (Directive × Nat) → (Q E : MachineState → Prop) → MachineState → Prop
  | [], Q, _, st => Q st
  | (d, sz) :: ds, Q, E, st =>
      d.wp1 ⟨st.2, st.2 + .ofNat sz⟩ (fun s' => wpE ds Q E (s', st.2 + .ofNat sz)) E st.1

theorem Directive.wp1_mono [Labels] {d : Directive} {p : Std.Rco Int64} {s : MachineData}
    {n₁ n₂ : MachineData → Prop} {j₁ j₂ : MachineState → Prop}
    (hn : ∀ s', n₁ s' → n₂ s') (hj : ∀ st, j₁ st → j₂ st) :
    d.wp1 p n₁ j₁ s → d.wp1 p n₂ j₂ s :=
  Or.imp (Effects.All.mono (fun st => hn st.1) _) (Effects.All.mono hj _)

theorem Directives.wpE_mono [Labels] {Q₁ Q₂ E₁ E₂ : MachineState → Prop}
    (hQ : ∀ st, Q₁ st → Q₂ st) (hE : ∀ st, E₁ st → E₂ st) :
    ∀ ds st, Directives.wpE ds Q₁ E₁ st → Directives.wpE ds Q₂ E₂ st
  | [], st => hQ st
  | (d, sz) :: ds, st =>
    Directive.wp1_mono (fun s' => wpE_mono hQ hE ds (s', st.2 + .ofNat sz)) hE

def Directives.wpTrans (ds : List (Directive × Nat)) :
    PredTrans (Labels → MachineState → Prop) (MachineState → Prop) Unit :=
  ⟨fun Q E labels st => @Directives.wpE labels ds (Q () labels) E st⟩

instance instWPDirectives :
    WP (List (Directive × Nat)) Unit (Labels → MachineState → Prop) (MachineState → Prop) where
  wpTrans := Directives.wpTrans
  wp_trans_monotone _ _ _ _ _ hE hQ := fun labels st =>
    Directives.wpE_mono (fun st' => hQ () labels st') hE _ st

/-- Unfold a segment wp into the transformer fold. -/
theorem Directives.wp_eq (ds : List (Directive × Nat))
    (Q : Unit → Labels → MachineState → Prop) (E : MachineState → Prop)
    (labels : Labels) (st : MachineState) :
    wp ds Q E labels st = @Directives.wpE labels ds (Q () labels) E st := rfl

@[simp] theorem Directives.wp_nil (Q : Unit → Labels → MachineState → Prop)
    (E : MachineState → Prop) (labels : Labels) (st : MachineState) :
    wp ([] : List (Directive × Nat)) Q E labels st = Q () labels st := rfl

/-- Sequential composition: a fall-through of `as` continues into `bs`, a jump
exits the whole list. -/
theorem Directives.wpE_append [Labels] (as bs : List (Directive × Nat))
    (Q E : MachineState → Prop) :
    ∀ st, Directives.wpE (as ++ bs) Q E st = Directives.wpE as (Directives.wpE bs Q E) E st := by
  induction as with
  | nil => intro st; rfl
  | cons dsz ds ih =>
    intro st
    obtain ⟨d, sz⟩ := dsz
    have hnext : (fun s' => Directives.wpE (ds ++ bs) Q E (s', st.2 + .ofNat sz))
        = fun s' => Directives.wpE ds (Directives.wpE bs Q E) E (s', st.2 + .ofNat sz) :=
      funext fun s' => ih (s', st.2 + .ofNat sz)
    simp only [List.cons_append, Directives.wpE, hnext]

/-! ## Per-instruction specs

One triple per instruction shape, stated on the cons cell. A fall-through
instruction's precondition is the tail's wp applied to the record update it
performs, with rip advanced by the carried size; a jump's precondition sends
`E` the target. Each proof picks the live `wp1` disjunct and unfolds the one
instruction of `Directive.interp`. -/

section Specs

variable {Q : Unit → Labels → MachineState → Prop} {E : MachineState → Prop}
  {ds : List (Directive × Nat)}

/-- Unfold one instruction of the segment wp down to its two disjuncts: the wp
equation, the transformer, the directive and instruction interpreters, operand
evaluation, and the `Effects.All` equations, normalizing register access to
`get64`/`set64` and discarding the poisoned disjunct. -/
local macro "wp_step" : tactic =>
  `(tactic| simp only [Directives.wp_eq, Directives.wpE, Directive.wp1, Directive.stepFall,
      Directive.stepJump, Directive.interp, Instr.interp,
      Operation.interp, Operand.interp, RegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, Reg64s.get_low64, Reg64s.set_low64, Effects.All,
      or_false, false_or])

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

@[spec] theorem Directives.add_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) (sz : Nat) :
    ⦃ fun labels st =>
        let a := BitVec.setWidth 64 i.toBitVec
        let b := st.1.regs.get64 r
        let v := a + b
        wp ds Q E labels
          ({ st.1 with
              regs := st.1.regs.set64 r v,
              status := StatusFlags.from_result v
                { cf := v.unsigned != a.unsigned + b.unsigned,
                  af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                  of := v.signed != a.signed + b.signed } },
            st.2 + .ofNat sz) ⦄
      ((Directive.instr (.regular asz .W64 (.add (.reg (.low r .W64)) (.imm (.int64 i)))), sz) :: ds)
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ _ h => by wp_step; exact h

@[spec] theorem Directives.adc_reg_reg_spec (asz : Width) (rd rs : Reg64) (sz : Nat) :
    ⦃ fun labels st =>
        let a := st.1.regs.get64 rs
        let b := st.1.regs.get64 rd
        let c := st.1.status.cf
        let v := a + b + BitVec.ofNat 64 c.toNat
        wp ds Q E labels
          ({ st.1 with
              regs := st.1.regs.set64 rd v,
              status := StatusFlags.from_result v
                { cf := v.unsigned != a.unsigned + b.unsigned + c,
                  af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned + c,
                  of := v.signed != a.signed + b.signed + c } },
            st.2 + .ofNat sz) ⦄
      ((Directive.instr (.regular asz .W64
          (.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))), sz) :: ds)
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
        if cc.interp st.1.status then E (st.1, labels.label l)
        else wp ds Q E labels (st.1, st.2 + .ofNat sz) ⦄
      ((Directive.instr (.regular asz osz (.jcc cc l)), sz) :: ds)
    ⦃ Q; E ⦄ :=
  Triple.intro fun labels st h => by
    wp_step
    cases hc : CondCode.interp cc st.1.status <;>
      simp only [hc, Bool.false_eq_true, if_true, if_false, reduceIte,
        Effects.All, or_false, false_or] at h ⊢ <;>
      exact h

@[spec] theorem Directives.jmp_label_spec (asz osz : Width) (l : Label) (sz : Nat) :
    ⦃ fun labels st => E (st.1, labels.label l) ⦄
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
    simp only [hcancel]
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
