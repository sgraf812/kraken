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

`Layout.frag` names a fragment as it is laid out at a position of its host
program. Extraction lemmas end in `Layout.frag` terms, and `Program.wpF_toE`
instantiates a fragment's triple at them. -/

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

@[simp] theorem Layout.frag_map_fst [Layout] (n : Nat) (p : Program) :
    (Layout.frag n p).map Prod.fst = p := by
  induction p generalizing n with
  | nil => rfl
  | cons d ds ih => simp [ih]

/-- A fragment splits where the program it lays out splits. -/
theorem Layout.frag_append [layout : Layout] (n : Nat) (as bs : Program) :
    Layout.frag n (as ++ bs) = Layout.frag n as ++ Layout.frag (n + as.length) bs := by
  simp [Layout.frag, List.mapIdx_append, Nat.add_left_comm, Nat.add_comm]

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

A `Program` is a directive list with no sizes. Its transformer runs each
directive at every instruction range a layout can give it, so sizing
invariance is the meaning of `wp`: a fragment's triple mentions no layout and
no position. The fall-through channel carries `MachineData` alone, because the
address after an instruction of unknown size is unknown; a jump exit (`E`)
names an address through `Labels`, the label footprint, and those addresses
are a fragment's whole interface to its host program. -/

def Program.wpF [Labels] : Program → (MachineData → Prop) → (MachineState → Prop) →
    MachineData → Prop
  | [], Q, _, s => Q s
  | d :: p, Q, E, s => ∀ r : Std.Rco Int64, d.wp1 r (fun s' => Program.wpF p Q E s') E s

theorem Program.wpF_mono [Labels] {Q₁ Q₂ : MachineData → Prop} {E₁ E₂ : MachineState → Prop}
    (hQ : ∀ s, Q₁ s → Q₂ s) (hE : ∀ st, E₁ st → E₂ st) :
    ∀ (p : Program) (s : MachineData), Program.wpF p Q₁ E₁ s → Program.wpF p Q₂ E₂ s
  | [], s => hQ s
  | _ :: p, _ => fun h r => Directive.wp1_mono (fun s' => wpF_mono hQ hE p s') hE (h r)

def Program.wpTrans (p : Program) :
    PredTrans (Labels → MachineData → Prop) (MachineState → Prop) Unit :=
  ⟨fun Q E labels s => @Program.wpF labels p (Q () labels) E s⟩

instance instWPProgram :
    WP Program Unit (Labels → MachineData → Prop) (MachineState → Prop) where
  wpTrans := Program.wpTrans
  wp_trans_monotone _ _ _ _ _ hE hQ := fun labels s =>
    Program.wpF_mono (fun s' => hQ () labels s') hE _ s

/-- Unfold a fragment wp into the transformer fold. -/
theorem Program.wp_eq (p : Program) (Q : Unit → Labels → MachineData → Prop)
    (E : MachineState → Prop) (labels : Labels) (s : MachineData) :
    wp p Q E labels s = @Program.wpF labels p (Q () labels) E s := rfl

/-- Sequential composition: a fall-through of `as` continues into `bs`, a jump
exits the whole fragment. -/
theorem Program.wpF_append [Labels] (as bs : Program) (Q : MachineData → Prop)
    (E : MachineState → Prop) :
    Program.wpF (as ++ bs) Q E = Program.wpF as (Program.wpF bs Q E) E := by
  induction as with
  | nil => rfl
  | cons d p ih => funext s; simp only [List.cons_append, Program.wpF, ih]

/-- A fragment's wp, instantiated at one sizing and one entry address, is the
sized fold. This is the bridge from a fragment's triple to the run of a
program that contains the fragment. -/
theorem Program.wpF_toE [Labels] {Q : MachineData → Prop} {E : MachineState → Prop} :
    ∀ {p : Program} (ds : List (Directive × Nat)), ds.map Prod.fst = p →
      ∀ (s : MachineData) (pc : Int64), Program.wpF p Q E s →
        Directives.wpE ds (fun st => Q st.1) E (s, pc)
  | _, [], rfl, _, _, hw => hw
  | _, (d, z) :: ds, rfl, _s, pc, hw =>
    Directive.wp1_mono (fun s' hs' => Program.wpF_toE ds rfl s' (pc + .ofNat z) hs')
      (fun _ h => h) (hw ⟨pc, pc + .ofNat z⟩)

/-! ### Per-instruction specs on `Program`

The same rules as the sized specs, with no size and no program counter: a
fall-through instruction's precondition is the tail's wp at the record update
it performs, and a jump's precondition sends the label's address to `E`. -/

section ProgramSpecs

variable {Q : Unit → Labels → MachineData → Prop} {E : MachineState → Prop} {p : Program}

local macro "wpF_step" : tactic =>
  `(tactic| simp only [Program.wp_eq, Program.wpF, Directive.wp1, Directive.stepFall,
      Directive.stepJump, Directive.interp, Instr.interp,
      Operation.interp, Operand.interp, RegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, Reg64s.get_low64, Reg64s.set_low64, Effects.All,
      or_false, false_or])

@[spec] theorem Program.nil_spec :
    ⦃ fun labels s => Q () labels s ⦄ ([] : Program) ⦃ Q; E ⦄ :=
  Triple.intro fun _ _ h => h

/-- The sequential-composition rule: the precondition is the wp of the first
fragment, continuing into the wp of the second, with the jump postcondition
passed through. -/
@[spec] theorem Program.append_spec (as bs : Program) :
    ⦃ fun labels s => wp as (fun _ labels' s' => wp bs Q E labels' s') E labels s ⦄
      (as ++ bs)
    ⦃ Q; E ⦄ :=
  Triple.intro fun labels s h => by
    rw [Program.wp_eq, Program.wpF_append]
    exact h

@[spec] theorem Program.label_spec (l : Label) :
    ⦃ fun labels s => wp p Q E labels s ⦄ (Directive.label l :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun _ _ h => by intro rco; wpF_step; exact h

@[spec] theorem Program.nop_spec (asz osz : Width) (n : Nat) :
    ⦃ fun labels s => wp p Q E labels s ⦄
      (Directive.instr (.regular asz osz (.nop n)) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ _ h => by intro rco; wpF_step; exact h

@[spec] theorem Program.mov_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun labels s =>
        wp p Q E labels { s with regs := s.regs.set64 r (BitVec.setWidth 64 i.toBitVec) } ⦄
      (Directive.instr (.regular asz .W64 (.mov (.reg (.low r .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ _ h => by intro rco; wpF_step; exact h

@[spec] theorem Program.sub_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun labels s =>
        let b := s.regs.get64 r
        let a := BitVec.setWidth 64 i.toBitVec
        let v := b - a
        wp p Q E labels
          { s with
              regs := s.regs.set64 r v,
              status := StatusFlags.from_result v
                { cf := v.unsigned != b.unsigned - a.unsigned,
                  af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                  of := v.signed != b.signed - a.signed } } ⦄
      (Directive.instr (.regular asz .W64 (.sub (.reg (.low r .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ _ h => by intro rco; wpF_step; exact h

@[spec] theorem Program.add_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun labels s =>
        let a := BitVec.setWidth 64 i.toBitVec
        let b := s.regs.get64 r
        let v := a + b
        wp p Q E labels
          { s with
              regs := s.regs.set64 r v,
              status := StatusFlags.from_result v
                { cf := v.unsigned != a.unsigned + b.unsigned,
                  af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                  of := v.signed != a.signed + b.signed } } ⦄
      (Directive.instr (.regular asz .W64 (.add (.reg (.low r .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ _ h => by intro rco; wpF_step; exact h

@[spec] theorem Program.adc_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun labels s =>
        let a := s.regs.get64 rs
        let b := s.regs.get64 rd
        let c := s.status.cf
        let v := a + b + BitVec.ofNat 64 c.toNat
        wp p Q E labels
          { s with
              regs := s.regs.set64 rd v,
              status := StatusFlags.from_result v
                { cf := v.unsigned != a.unsigned + b.unsigned + c,
                  af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned + c,
                  of := v.signed != a.signed + b.signed + c } } ⦄
      (Directive.instr (.regular asz .W64
          (.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ _ h => by intro rco; wpF_step; exact h

@[spec] theorem Program.mulx_reg_spec (asz : Width) (hi lo rs : Reg64) :
    ⦃ fun labels s =>
        let v := (s.regs.get64 rs).unsigned * (s.regs.get64 .rdx).unsigned
        wp p Q E labels
          { s with regs :=
              (s.regs.set64 lo (BitVec.ofInt 64 v)).set64 hi (BitVec.ofInt 64 (v >>> 64)) } ⦄
      (Directive.instr (.regular asz .W64
          (.mulx (.low hi .W64) (.low lo .W64) (.reg (.low rs .W64)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ _ h => by intro rco; wpF_step; exact h

@[spec] theorem Program.jcc_spec (asz osz : Width) (cc : CondCode) (l : Label) :
    ⦃ fun labels s =>
        (cc.interp s.status = true → E (s, labels.label l))
          ⊓ (cc.interp s.status = false → wp p Q E labels s) ⦄
      (Directive.instr (.regular asz osz (.jcc cc l)) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun labels s h => by
    intro rco
    wpF_step
    cases hc : CondCode.interp cc s.status <;>
      simp only [hc, Bool.false_eq_true, if_true, if_false, meet_prop_eq_and,
        Effects.All, or_false, false_or] at h ⊢
    · exact h.2 trivial
    · exact h.1 trivial

@[spec] theorem Program.jmp_label_spec (asz osz : Width) (l : Label) :
    ⦃ fun labels s => E (s, labels.label l) ⦄
      (Directive.instr (.regular asz osz
          (.jmp (.rel (.sub (.label l) .after_current_instruction)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun labels s h => by
    intro rco
    obtain ⟨lo, hi⟩ := rco
    wpF_step
    have hcancel : hi + (labels.label l - hi) = labels.label l := by
      apply Int64.toBitVec_inj.mp
      simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    simp only [hcancel]
    exact h

end ProgramSpecs

