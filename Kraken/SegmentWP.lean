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
open Lean.Order

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
  | (_, sz) :: ds, st =>
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

/-- Weakening a segment: strengthen what a fall-through and a jump may conclude. -/
theorem Directives.wp_mono {Q₁ Q₂ : Unit → Labels → MachineState → Prop}
    {E₁ E₂ : MachineState → Prop} (ds : List (Directive × Nat))
    (labels : Labels) (st : MachineState)
    (hQ : ∀ st', Q₁ () labels st' → Q₂ () labels st') (hE : ∀ st', E₁ st' → E₂ st')
    (h : wp ds Q₁ E₁ labels st) : wp ds Q₂ E₂ labels st :=
  @Directives.wpE_mono labels _ _ _ _ hQ hE ds st h

@[simp] theorem Directives.wp_nil (Q : Unit → Labels → MachineState → Prop)
    (E : MachineState → Prop) (labels : Labels) (st : MachineState) :
    wp ([] : List (Directive × Nat)) Q E labels st = Q () labels st := rfl

/-- Sequential composition: a fall-through of `as` continues into `bs`, a jump
exits the whole list. -/
theorem Directives.wpE_append [Labels] (as bs : List (Directive × Nat))
    (Q E : MachineState → Prop) :
    Directives.wpE (as ++ bs) Q E = Directives.wpE as (Directives.wpE bs Q E) E := by
  induction as with
  | nil => rfl
  | cons dsz ds ih =>
    funext st
    obtain ⟨d, sz⟩ := dsz
    have hnext : (fun s' => Directives.wpE (ds ++ bs) Q E (s', st.2 + .ofNat sz))
        = fun s' => Directives.wpE ds (Directives.wpE bs Q E) E (s', st.2 + .ofNat sz) :=
      funext fun s' => by simp [ih]
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

/-- `wp_step`, applied to a hypothesis. -/
local macro "wp_step_at" h:ident : tactic =>
  `(tactic| simp only [Directives.wp_eq, Directives.wpE, Directive.wp1, Directive.stepFall,
      Directive.stepJump, Directive.interp, Instr.interp,
      Operation.interp, Operand.interp, RegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, Reg64s.get_low64, Reg64s.set_low64, Effects.All,
      or_false, false_or] at $h:ident)

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
        (cc.interp st.1.status = true → E (st.1, labels.label l))
          ⊓ (cc.interp st.1.status = false → wp ds Q E labels (st.1, st.2 + .ofNat sz)) ⦄
      ((Directive.instr (.regular asz osz (.jcc cc l)), sz) :: ds)
    ⦃ Q; E ⦄ :=
  Triple.intro fun labels st h => by
    wp_step
    cases hc : CondCode.interp cc st.1.status <;>
      simp only [hc, Bool.false_eq_true, if_true, if_false, meet_prop_eq_and,
        Effects.All, or_false, false_or] at h ⊢
    · exact h.2 trivial
    · exact h.1 trivial

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

/-! ## Equations

For the fall-through instructions the spec preconditions are exact: the wp of
the cons is equal to the tail's wp at the updated state, and a conditional or
unconditional jump equals its exit dispatch. The equations rewrite a segment
wp into the nested form a composite rule states in its precondition. -/

theorem Directives.wp_cons_label (l : Label) (sz : Nat) (labels st) :
    wp ((Directive.label l, sz) :: ds) Q E labels st
      = wp ds Q E labels (st.1, st.2 + .ofNat sz) := by
  refine propext ⟨fun h => ?_, fun h => ?_⟩ <;> (wp_step_at h; wp_step; exact h)

theorem Directives.wp_cons_nop (asz osz : Width) (n sz : Nat) (labels st) :
    wp ((Directive.instr (.regular asz osz (.nop n)), sz) :: ds) Q E labels st
      = wp ds Q E labels (st.1, st.2 + .ofNat sz) := by
  refine propext ⟨fun h => ?_, fun h => ?_⟩ <;> (wp_step_at h; wp_step; exact h)

theorem Directives.wp_cons_sub_reg_imm (asz : Width) (r : Reg64) (i : Int64) (sz : Nat)
    (labels st) :
    wp ((Directive.instr (.regular asz .W64
        (.sub (.reg (.low r .W64)) (.imm (.int64 i)))), sz) :: ds) Q E labels st
      = (let b := st.1.regs.get64 r
         let a := BitVec.setWidth 64 i.toBitVec
         let v := b - a
         wp ds Q E labels
          ({ st.1 with
              regs := st.1.regs.set64 r v,
              status := StatusFlags.from_result v
                { cf := v.unsigned != b.unsigned - a.unsigned,
                  af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                  of := v.signed != b.signed - a.signed } },
            st.2 + .ofNat sz)) := by
  refine propext ⟨fun h => ?_, fun h => ?_⟩ <;> (wp_step_at h; wp_step; exact h)

theorem Directives.wp_cons_mulx_reg (asz : Width) (hi lo rs : Reg64) (sz : Nat) (labels st) :
    wp ((Directive.instr (.regular asz .W64
        (.mulx (.low hi .W64) (.low lo .W64) (.reg (.low rs .W64)))), sz) :: ds) Q E labels st
      = (let v := (st.1.regs.get64 rs).unsigned * (st.1.regs.get64 .rdx).unsigned
         wp ds Q E labels
          ({ st.1 with regs :=
              (st.1.regs.set64 lo (BitVec.ofInt 64 v)).set64 hi (BitVec.ofInt 64 (v >>> 64)) },
            st.2 + .ofNat sz)) := by
  refine propext ⟨fun h => ?_, fun h => ?_⟩ <;> (wp_step_at h; wp_step; exact h)

theorem Directives.wp_cons_jcc (asz osz : Width) (cc : CondCode) (l : Label) (sz : Nat)
    (labels st) :
    wp ((Directive.instr (.regular asz osz (.jcc cc l)), sz) :: ds) Q E labels st
      = if cc.interp st.1.status then E (st.1, labels.label l)
        else wp ds Q E labels (st.1, st.2 + .ofNat sz) := by
  refine propext ⟨fun h => ?_, fun h => ?_⟩ <;>
    ((try wp_step_at h) <;> (try wp_step) <;>
      cases hc : CondCode.interp cc st.1.status <;>
      simp only [hc, Bool.false_eq_true, if_true, if_false, Effects.All, or_false, false_or]
        at h ⊢ <;>
      exact h)

theorem Directives.wp_cons_jmp_label (asz osz : Width) (l : Label) (sz : Nat) (labels st) :
    wp ((Directive.instr (.regular asz osz
        (.jmp (.rel (.sub (.label l) .after_current_instruction)))), sz) :: ds)
        Q E labels st
      = E (st.1, labels.label l) := by
  have hcancel : st.2 + .ofNat sz + (labels.label l - (st.2 + .ofNat sz))
      = labels.label l := by
    apply Int64.toBitVec_inj.mp
    simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
    rw [BitVec.add_comm, BitVec.sub_add_cancel]
  refine propext ⟨fun h => ?_, fun h => ?_⟩ <;>
    ((try wp_step_at h) <;> (try wp_step) <;>
      (try simp only [hcancel, Int64.ofBitVec_toBitVec] at h ⊢) <;> exact h)

/-! ### Fragments

A laid-out fragment is stepped through the same rules as a directive list: the
three specs below let `vcgen` walk `Layout.frag` down to the cons cells the
per-directive specs are keyed on, and split it where the program splits. -/

/-- The fragment `p` as it is laid out from position `n` of the program that
contains it: each directive paired with the size the layout assigns to its
position. -/
def Layout.frag [layout : Layout] (n : Nat) (p : Program) : List (Directive × Nat) :=
  p.mapIdx (fun i d => (d, layout.size (n + i)))

@[simp] theorem Layout.frag_nil [Layout] (n : Nat) :
    Layout.frag n [] = [] := rfl

@[simp] theorem Layout.frag_length [Layout] (n : Nat) (p : Program) :
    (Layout.frag n p).length = p.length := by simp [Layout.frag]

@[simp] theorem Layout.frag_cons [layout : Layout] (n : Nat) (d : Directive) (ds : Program) :
    Layout.frag n (d :: ds) = (d, layout.size n) :: Layout.frag (n + 1) ds := by
  simp [Layout.frag, List.mapIdx_cons, Nat.add_assoc, Nat.add_comm 1]

/-- A fragment splits where the program it lays out splits. -/
theorem Layout.frag_append [layout : Layout] (n : Nat) (as bs : Program) :
    Layout.frag n (as ++ bs) = Layout.frag n as ++ Layout.frag (n + as.length) bs := by
  simp [Layout.frag, List.mapIdx_append, Nat.add_left_comm, Nat.add_comm]

@[spec] theorem Directives.frag_nil_spec [Layout] (n : Nat) :
    ⦃ fun labels st => Q () labels st ⦄ (Layout.frag n ([] : Program)) ⦃ Q; E ⦄ :=
  Triple.intro fun _ _ h => h

@[spec] theorem Directives.frag_cons_spec [layout : Layout] (n : Nat) (d : Directive)
    (p : Program) :
    ⦃ fun labels st => wp ((d, layout.size n) :: Layout.frag (n + 1) p) Q E labels st ⦄
      (Layout.frag n (d :: p))
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ _ h => by rw [Layout.frag_cons]; exact h

@[spec] theorem Directives.frag_append_spec [Layout] (n : Nat) (as bs : Program) :
    ⦃ fun labels st => wp (Layout.frag n as ++ Layout.frag (n + as.length) bs) Q E labels st ⦄
      (Layout.frag n (as ++ bs))
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ _ h => by rw [Layout.frag_append]; exact h

/-- The sequential-composition rule, the analogue of the `Bind.bind` spec: the
precondition is the wp of the first piece, continuing into the wp of the
second, with the jump postcondition passed through. -/
@[spec] theorem Directives.append_spec (as bs : List (Directive × Nat)) :
    ⦃ fun labels st => wp as (fun _ labels' st' => wp bs Q E labels' st') E labels st ⦄
      (as ++ bs)
    ⦃ Q; E ⦄ :=
  Triple.intro fun labels st h => by
    show Directives.wpE (as ++ bs) (Q () labels) E st
    rw [Directives.wpE_append]
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

/-! ### Programs

A `Program` is a directive list with no sizes. Its transformer quantifies over
every sizing a layout can give the list, so sizing invariance is the meaning of
`wp`, and a fragment's triple mentions no layout and no position. `Labels`
stays in the assertion language as the label footprint: the addresses a
fragment's jumps name are its whole interface to the host program. -/

@[simp] theorem Layout.frag_map_fst [Layout] (n : Nat) (p : Program) :
    (Layout.frag n p).map Prod.fst = p := by
  induction p generalizing n with
  | nil => rfl
  | cons d ds ih => simp [ih]

def Program.wpTrans (p : Program) :
    PredTrans (Labels → MachineState → Prop) (MachineState → Prop) Unit :=
  ⟨fun Q E labels st => ∀ ds : List (Directive × Nat),
      ds.map Prod.fst = p → @Directives.wpE labels ds (Q () labels) E st⟩

instance instWPProgram :
    WP Program Unit (Labels → MachineState → Prop) (MachineState → Prop) where
  wpTrans := Program.wpTrans
  wp_trans_monotone _ _ _ _ _ hE hQ := fun labels st h ds hds =>
    Directives.wpE_mono (fun st' => hQ () labels st') hE ds st (h ds hds)

/-- A sized list is the fragment it projects to, laid out by the sizes it
carries. -/
private theorem mapIdx_fst_eq_self {α β : Type _} :
    ∀ (f : Nat → β) (ds : List (α × β)), (∀ i (h : i < ds.length), f i = ds[i].2) →
      (ds.map Prod.fst).mapIdx (fun i a => (a, f i)) = ds
  | _, [], _ => rfl
  | f, (a, b) :: tl, h => by
    have h0 : f 0 = b := h 0 (by simp)
    simp only [List.map_cons, List.mapIdx_cons, h0]
    exact congrArg _ (mapIdx_fst_eq_self (fun i => f (i + 1)) tl fun i hi => by
      have := h (i + 1) (by simpa using Nat.succ_lt_succ hi)
      simpa using this)

/-- A triple proved for the fragment at every layout and position is a triple
for the fragment itself. This is the proof vehicle: `vcgen` walks the concrete
`Layout.frag` list, and the conversion happens once. -/
theorem Program.triple_of_frag {P : Labels → MachineState → Prop} {p : Program}
    {Q : Unit → Labels → MachineState → Prop} {E : MachineState → Prop}
    (h : ∀ (layout : Layout) (n : Nat), ⦃P⦄ Layout.frag n p ⦃Q; E⦄) :
    ⦃P⦄ p ⦃Q; E⦄ := by
  refine Triple.intro fun labels st hp => ?_
  intro ds hds
  have hfrag : @Layout.frag ⟨0, fun i => ((ds[i]?).map Prod.snd).getD 0⟩ 0 p = ds := by
    subst hds
    simp only [Layout.frag, Nat.zero_add]
    exact mapIdx_fst_eq_self _ ds fun i hi => by simp [List.getElem?_eq_getElem hi]
  have hw := (h ⟨0, fun i => ((ds[i]?).map Prod.snd).getD 0⟩ 0).le_wp labels st hp
  rw [hfrag] at hw
  exact hw

/-- A fragment's triple, placed: the fragment at position `n` under `layout`. -/
theorem Program.triple_frag [layout : Layout] {P : Labels → MachineState → Prop}
    {p : Program} {Q : Unit → Labels → MachineState → Prop} {E : MachineState → Prop}
    (h : ⦃P⦄ p ⦃Q; E⦄) (n : Nat) : ⦃P⦄ Layout.frag n p ⦃Q; E⦄ :=
  Triple.intro fun labels st hp =>
    h.le_wp labels st hp (Layout.frag n p) (Layout.frag_map_fst n p)

