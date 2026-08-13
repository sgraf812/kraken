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
directive under every label table and at every instruction range a layout can
give it, so a fragment's triple mentions no layout, no position, no program
counter, and no label table. The fall-through channel carries `MachineData`
alone. A jump exit names the target label, not an address: `E : Label →
MachineData → Prop`, and the labels a spec's `E` mentions are the fragment's
whole interface to its host program. -/

/-- The label a directive jumps to, read from the syntax. -/
def Directive.target : Directive → Option Label
  | .instr (.regular _ _ (.jcc _ l)) => some l
  | .instr (.regular _ _ (.jmp (.rel (.sub (.label l) .after_current_instruction)))) => some l
  | _ => none

def Program.wpF : Program → (MachineData → Prop) → (Label → MachineData → Prop) →
    MachineData → Prop
  | [], Q, _, s => Q s
  | d :: p, Q, E, s => ∀ (labels : Labels) (r : Std.Rco Int64),
      d.wp1 r (fun s' => Program.wpF p Q E s')
        (fun st => ∃ l, d.target = some l ∧ st.2 = labels.label l ∧ E l st.1) s

theorem Program.wpF_mono {Q₁ Q₂ : MachineData → Prop} {E₁ E₂ : Label → MachineData → Prop}
    (hQ : ∀ s, Q₁ s → Q₂ s) (hE : ∀ l s, E₁ l s → E₂ l s) :
    ∀ (p : Program) (s : MachineData), Program.wpF p Q₁ E₁ s → Program.wpF p Q₂ E₂ s
  | [], s => hQ s
  | _ :: p, _ => fun h labels r =>
    Directive.wp1_mono (fun s' => wpF_mono hQ hE p s')
      (fun _ => fun ⟨l, ht, ha, he⟩ => ⟨l, ht, ha, hE l _ he⟩) (h labels r)

/-- Sequential composition of the traversal: a fall-through of `as` continues
into `bs`, a jump exits the whole fragment. -/
theorem Program.wpF_append (as bs : Program) (Q : MachineData → Prop)
    (E : Label → MachineData → Prop) :
    Program.wpF (as ++ bs) Q E = Program.wpF as (Program.wpF bs Q E) E := by
  induction as with
  | nil => rfl
  | cons d p ih => funext s; simp only [List.cons_append, Program.wpF, ih]

/-- The traversal, instantiated at one label table and one sizing, is the
sized fold, with jump exits resolved to the table's addresses. -/
theorem Program.wpF_toE [Labels] {Q : MachineData → Prop} {E : Label → MachineData → Prop} :
    ∀ {p : Program} (ds : List (Directive × Nat)), ds.map Prod.fst = p →
      ∀ (s : MachineData) (pc : Int64), Program.wpF p Q E s →
        Directives.wpE ds (fun st => Q st.1)
          (fun st => ∃ l, st.2 = label l ∧ E l st.1) (s, pc)
  | _, [], rfl, _, _, hw => hw
  | _, (d, z) :: ds, rfl, _s, pc, hw =>
    Directive.wp1_mono (fun s' hs' => Program.wpF_toE ds rfl s' (pc + .ofNat z) hs')
      (fun _ => fun ⟨l, _, ha, he⟩ => ⟨l, ha, he⟩) (hw _ ⟨pc, pc + .ofNat z⟩)

/-! ### Runs

`wp` on `Program` is the run: a fall-through past the end of the text lands in
`Q`, and a jump exit at label `l` either surfaces in `E l` or, when `l` is a
label of the program, re-enters at that label's cell. The re-entry closure is
a least fixpoint, taken by `Eventually` inside the definition; no statement
mentions it. -/

/-- The omni-semantics judgment is monotone in its transition relation and in
its postcondition. -/
theorem Eventually.mono {State : Type} {trans₁ trans₂ : State → Post → Prop}
    {P Q : @Post State} {st : State} (h : Eventually trans₁ P st)
    (htrans : ∀ st' post, trans₁ st' post → trans₂ st' post) (hPQ : ∀ s, P s → Q s) :
    Eventually trans₂ Q st := by
  induction h with
  | done st hp => exact Eventually.done st (hPQ st hp)
  | step st mid_p ht _ ih => exact Eventually.step st mid_p (htrans st mid_p ht) ih

/-- The suffix of a program at the last cell carrying `label l`; `[]` when the
program has no such cell. Re-entry at the last occurrence keeps a suffix's
scope a restriction of its host's scope. -/
def Program.fromLabel : Program → Label → Program
  | [], _ => []
  | d :: p, l =>
      if Program.fromLabel p l = [] ∧ d = Directive.label l then d :: p
      else Program.fromLabel p l

@[simp] theorem Program.fromLabel_nil (l : Label) : Program.fromLabel [] l = [] := rfl

@[simp] theorem Program.fromLabel_cons (d : Directive) (p : Program) (l : Label) :
    Program.fromLabel (d :: p) l =
      if Program.fromLabel p l = [] ∧ d = Directive.label l then d :: p
      else Program.fromLabel p l := rfl

/-- A label present in the tail keeps its scope suffix under a cons. -/
theorem Program.fromLabel_cons_of_mem (d : Directive) {p : Program} (l : Label)
    (h : Program.fromLabel p l ≠ []) :
    Program.fromLabel (d :: p) l = Program.fromLabel p l := by
  rw [Program.fromLabel_cons, if_neg]
  rintro ⟨hnil, -⟩
  exact h hnil

theorem Program.fromLabel_suffix (p : Program) (l : Label) :
    Program.fromLabel p l <:+ p := by
  induction p with
  | nil => exact List.suffix_rfl
  | cons d p ih =>
    rw [Program.fromLabel_cons]
    split
    · exact List.suffix_rfl
    · exact ih.trans (List.suffix_cons d p)

/-- A label present in a suffix has the same scope suffix in the host. -/
theorem Program.fromLabel_of_suffix {q p : Program} (hs : q <:+ p) (l : Label)
    (h : Program.fromLabel q l ≠ []) :
    Program.fromLabel p l = Program.fromLabel q l := by
  induction p with
  | nil => rw [List.suffix_nil.mp hs]
  | cons d p ih =>
    rcases List.suffix_cons_iff.mp hs with heq | hs'
    · rw [heq]
    · have hp := ih hs'
      rw [Program.fromLabel_cons, hp, if_neg]
      rintro ⟨hnil, -⟩
      exact h (hp ▸ hnil)

/-- A label with a scope suffix is a cell of the program. -/
theorem Program.fromLabel_mem {p : Program} {l : Label}
    (h : Program.fromLabel p l ≠ []) : Directive.label l ∈ p := by
  induction p with
  | nil => exact absurd rfl h
  | cons d p ih =>
    rw [Program.fromLabel_cons] at h
    by_cases hc : Program.fromLabel p l = [] ∧ d = Directive.label l
    · rw [hc.2]
      exact List.mem_cons_self
    · rw [if_neg hc] at h
      exact List.mem_cons_of_mem d (ih h)

/-- One step of the run: traverse the scope suffix at the current label; a
fall-through ends in `Q`, a jump exit surfaces in `E` or hands an in-scope
label to the continuation. -/
def Program.runStep (p : Program) (Q : MachineData → Prop) (E : Label → MachineData → Prop)
    (st : MachineData × Label) (post : @Post (MachineData × Label)) : Prop :=
  Program.wpF (Program.fromLabel p st.2) Q
    (fun l s => E l s ∨ (Program.fromLabel p l ≠ [] ∧ post (s, l))) st.1

/-- Where a jump exit at `l` goes: it surfaces in `E`, or, in scope, the run
re-enters at `l` and the chain of re-entries ends. -/
def Program.exitsTo (p : Program) (Q : MachineData → Prop) (E : Label → MachineData → Prop)
    (l : Label) (s : MachineData) : Prop :=
  E l s ∨ (Program.fromLabel p l ≠ [] ∧
    Eventually (Program.runStep p Q E) (fun _ => False) (s, l))

def Program.wpR (p : Program) (Q : MachineData → Prop) (E : Label → MachineData → Prop)
    (s : MachineData) : Prop :=
  Program.wpF p Q (Program.exitsTo p Q E) s

/-- Lift a run chain into a host whose scope agrees on the chain's labels:
each exit either maps into the host's exit dispatch or stays a chain state. -/
theorem Program.chain_lift {q pf : Program} {Q : MachineData → Prop}
    {E₁ E₂ : Label → MachineData → Prop}
    (hsub : ∀ lx, Program.fromLabel q lx ≠ [] →
      Program.fromLabel pf lx = Program.fromLabel q lx)
    (hE : ∀ lx s, E₁ lx s → Program.exitsTo pf Q E₂ lx s) :
    ∀ st, Program.fromLabel q st.2 ≠ [] →
      Eventually (Program.runStep q Q E₁) (fun _ => False) st →
      Eventually (Program.runStep pf Q E₂) (fun _ => False) st := by
  intro st hmem h
  revert hmem
  induction h with
  | done st hp => exact fun _ => hp.elim
  | step st mid_p ht _ ih =>
    intro hmem
    refine Eventually.step st
      (fun st' => (mid_p st' ∧ Program.fromLabel q st'.2 ≠ [])
        ∨ Eventually (Program.runStep pf Q E₂) (fun _ => False) st') ?_ ?_
    · show Program.wpF (Program.fromLabel pf st.2) Q _ st.1
      rw [hsub st.2 hmem]
      refine Program.wpF_mono (fun _ h => h) (fun lx s' hx => ?_) _ _ ht
      rcases hx with hx | ⟨hmq, hmid⟩
      · rcases hE lx s' hx with he | ⟨hm, hch⟩
        · exact Or.inl he
        · exact Or.inr ⟨hm, Or.inr hch⟩
      · exact Or.inr ⟨hsub lx hmq ▸ hmq, Or.inl ⟨hmid, hmq⟩⟩
    · rintro mid (⟨hmid, hmq⟩ | hch)
      · exact ih mid hmid hmq
      · exact hch

/-- Growing the scope by one leading cell: chains re-enter the same suffixes,
and exits keep their dispatch. -/
theorem Program.exitsTo_grow {p : Program} {Q : MachineData → Prop}
    {E : Label → MachineData → Prop} (d : Directive) :
    ∀ (l : Label) (s : MachineData),
      Program.exitsTo p Q E l s → Program.exitsTo (d :: p) Q E l s := by
  intro l s hx
  rcases hx with he | ⟨hm, hch⟩
  · exact Or.inl he
  · refine Or.inr ⟨Program.fromLabel_cons_of_mem d l hm ▸ hm, ?_⟩
    exact Program.chain_lift (fun lx h' => Program.fromLabel_cons_of_mem d lx h')
      (fun _ _ he => Or.inl he) (s, l) hm hch

theorem Program.runStep_mono {p : Program} {Q₁ Q₂ : MachineData → Prop}
    {E₁ E₂ : Label → MachineData → Prop}
    (hQ : ∀ s, Q₁ s → Q₂ s) (hE : ∀ l s, E₁ l s → E₂ l s) :
    ∀ st post, Program.runStep p Q₁ E₁ st post → Program.runStep p Q₂ E₂ st post :=
  fun _ _ h => Program.wpF_mono hQ
    (fun l s hx => hx.imp (hE l s) (fun ⟨hm, hp⟩ => ⟨hm, hp⟩)) _ _ h

theorem Program.wpR_mono {Q₁ Q₂ : MachineData → Prop} {E₁ E₂ : Label → MachineData → Prop}
    (hQ : ∀ s, Q₁ s → Q₂ s) (hE : ∀ l s, E₁ l s → E₂ l s) :
    ∀ (p : Program) (s : MachineData), Program.wpR p Q₁ E₁ s → Program.wpR p Q₂ E₂ s :=
  fun p s h => Program.wpF_mono hQ
    (fun l s' hx => hx.imp (hE l s')
      (fun ⟨hm, hch⟩ => ⟨hm, hch.mono (Program.runStep_mono hQ hE) (fun _ f => f)⟩)) p s h

def Program.wpTrans (p : Program) :
    PredTrans (MachineData → Prop) (Label → MachineData → Prop) Unit :=
  ⟨fun Q E s => Program.wpR p (Q ()) E s⟩

instance instWPProgram :
    WP Program Unit (MachineData → Prop) (Label → MachineData → Prop) where
  wpTrans := Program.wpTrans
  wp_trans_monotone _ _ _ _ _ hE hQ := fun s =>
    Program.wpR_mono (fun s' => hQ () s') hE _ s

/-- Unfold the run wp into the traversal with its exit dispatch. -/
theorem Program.wp_eq (p : Program) (Q : Unit → MachineData → Prop)
    (E : Label → MachineData → Prop) (s : MachineData) :
    wp p Q E s = Program.wpR p (Q ()) E s := rfl

/-! ### Per-instruction specs

One rule per instruction shape, on the cons cell. A fall-through instruction's
precondition is the tail's wp at the record update it performs. A jump's
precondition dispatches on the target's scope: in scope, the target's suffix
runs on; out of scope, the exit surfaces in `E`. A label cell is skipped, or,
when jumps re-enter it, stepped with `Program.label_loop_spec` and a
measure-indexed invariant. -/

section ProgramSpecs

variable {Q : Unit → MachineData → Prop} {E : Label → MachineData → Prop} {p : Program}

local macro "wpF_step" : tactic =>
  `(tactic| simp only [Program.wp_eq, Program.wpR, Program.wpF, Directive.wp1,
      Directive.stepFall, Directive.stepJump, Directive.interp, Instr.interp,
      Operation.interp, Operand.interp, RegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, Reg64s.get_low64, Reg64s.set_low64, Effects.All,
      or_false, false_or])

@[spec] theorem Program.nil_spec :
    ⦃ fun s => Q () s ⦄ ([] : Program) ⦃ Q; E ⦄ :=
  Triple.intro fun _ h => h

/-- The append cases are spelling: `vcgen` walks a `++` of fragments by
rewriting it to the cons cell on top. -/
@[spec] theorem Program.nil_append_spec (bs : Program) :
    ⦃ fun s => wp bs Q E s ⦄ (([] : Program) ++ bs) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by rw [List.nil_append]; exact h

@[spec] theorem Program.cons_append_spec (a : Directive) (as bs : Program) :
    ⦃ fun s => wp (a :: (as ++ bs)) Q E s ⦄ ((a :: as) ++ bs) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by rw [List.cons_append]; exact h

@[spec] theorem Program.append_assoc_spec (as bs cs : Program) :
    ⦃ fun s => wp (as ++ (bs ++ cs)) Q E s ⦄ ((as ++ bs) ++ cs) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by rw [List.append_assoc]; exact h

@[spec] theorem Program.label_spec (l : Label) :
    ⦃ fun s => wp p Q E s ⦄ (Directive.label l :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun _ h => by
    intro labels rco
    wpF_step
    exact Program.wpF_mono (fun _ h => h) (Program.exitsTo_grow _) _ _ h

@[spec] theorem Program.nop_spec (asz osz : Width) (n : Nat) :
    ⦃ fun s => wp p Q E s ⦄
      (Directive.instr (.regular asz osz (.nop n)) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ h => by
    intro labels rco
    wpF_step
    exact Program.wpF_mono (fun _ h => h) (Program.exitsTo_grow _) _ _ h

@[spec] theorem Program.mov_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s => wp p Q E { s with regs := s.regs.set64 r (BitVec.setWidth 64 i.toBitVec) } ⦄
      (Directive.instr (.regular asz .W64 (.mov (.reg (.low r .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ h => by
    intro labels rco
    wpF_step
    exact Program.wpF_mono (fun _ h => h) (Program.exitsTo_grow _) _ _ h

@[spec] theorem Program.sub_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let b := s.regs.get64 r
        let a := BitVec.setWidth 64 i.toBitVec
        let v := b - a
        wp p Q E
          { s with
              regs := s.regs.set64 r v,
              status := StatusFlags.from_result v
                { cf := v.unsigned != b.unsigned - a.unsigned,
                  af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                  of := v.signed != b.signed - a.signed } } ⦄
      (Directive.instr (.regular asz .W64 (.sub (.reg (.low r .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ h => by
    intro labels rco
    wpF_step
    exact Program.wpF_mono (fun _ h => h) (Program.exitsTo_grow _) _ _ h

@[spec] theorem Program.add_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := BitVec.setWidth 64 i.toBitVec
        let b := s.regs.get64 r
        let v := a + b
        wp p Q E
          { s with
              regs := s.regs.set64 r v,
              status := StatusFlags.from_result v
                { cf := v.unsigned != a.unsigned + b.unsigned,
                  af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                  of := v.signed != a.signed + b.signed } } ⦄
      (Directive.instr (.regular asz .W64 (.add (.reg (.low r .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ h => by
    intro labels rco
    wpF_step
    exact Program.wpF_mono (fun _ h => h) (Program.exitsTo_grow _) _ _ h

@[spec] theorem Program.adc_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 rs
        let b := s.regs.get64 rd
        let c := s.status.cf
        let v := a + b + BitVec.ofNat 64 c.toNat
        wp p Q E
          { s with
              regs := s.regs.set64 rd v,
              status := StatusFlags.from_result v
                { cf := v.unsigned != a.unsigned + b.unsigned + c,
                  af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned + c,
                  of := v.signed != a.signed + b.signed + c } } ⦄
      (Directive.instr (.regular asz .W64
          (.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ h => by
    intro labels rco
    wpF_step
    exact Program.wpF_mono (fun _ h => h) (Program.exitsTo_grow _) _ _ h

@[spec] theorem Program.mulx_reg_spec (asz : Width) (hi lo rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rs).unsigned * (s.regs.get64 .rdx).unsigned
        wp p Q E
          { s with regs :=
              (s.regs.set64 lo (BitVec.ofInt 64 v)).set64 hi (BitVec.ofInt 64 (v >>> 64)) } ⦄
      (Directive.instr (.regular asz .W64
          (.mulx (.low hi .W64) (.low lo .W64) (.reg (.low rs .W64)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ h => by
    intro labels rco
    wpF_step
    exact Program.wpF_mono (fun _ h => h) (Program.exitsTo_grow _) _ _ h

@[spec] theorem Program.jcc_spec (asz osz : Width) (cc : CondCode) (l : Label) :
    ⦃ fun s =>
        (cc.interp s.status = true → E l s)
          ⊓ (cc.interp s.status = false → wp p Q E s) ⦄
      (Directive.instr (.regular asz osz (.jcc cc l)) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro labels rco
    wpF_step
    cases hc : CondCode.interp cc s.status <;>
      simp only [hc, Bool.false_eq_true, if_true, if_false, meet_prop_eq_and,
        Effects.All, or_false, false_or] at h ⊢
    · exact Program.wpF_mono (fun _ h => h) (Program.exitsTo_grow _) _ _ (h.2 trivial)
    · exact ⟨l, rfl, rfl, Or.inl (h.1 trivial)⟩

@[spec] theorem Program.jmp_label_spec (asz osz : Width) (l : Label) :
    ⦃ fun s => E l s ⦄
      (Directive.instr (.regular asz osz
          (.jmp (.rel (.sub (.label l) .after_current_instruction)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro labels rco
    obtain ⟨lo, hi⟩ := rco
    wpF_step
    have hcancel : hi + (labels.label l - hi) = labels.label l := by
      apply Int64.toBitVec_inj.mp
      simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    simp only [hcancel]
    exact ⟨l, rfl, rfl, Or.inl h⟩

/-- A triple from an absurd precondition. -/
theorem Program.triple_false {p : Program} {Q : Unit → MachineData → Prop}
    {E : Label → MachineData → Prop} :
    ⦃ fun _ => False ⦄ p ⦃ Q; E ⦄ :=
  Triple.intro fun _ h => h.elim

/-- The consequence rule of the run wp. -/
theorem Program.triple_conseq {P₁ P₂ : MachineData → Prop} {p : Program}
    {Q : Unit → MachineData → Prop} {E₁ E₂ : Label → MachineData → Prop}
    (h : ⦃P₁⦄ p ⦃Q; E₁⦄) (hP : ∀ s, P₂ s → P₁ s) (hE : ∀ l s, E₁ l s → E₂ l s) :
    ⦃P₂⦄ p ⦃Q; E₂⦄ :=
  Triple.intro fun s hp => Program.wpR_mono (fun _ h => h) hE p s (h.le_wp s (hP s hp))

/-- Tie the label knot. `E` is the label context of a traversal: a jump spec
sends its target's assertion there, and this rule discharges the in-scope part
of the context against the labels' own bodies, once, with a measure.

`V n l` is the assertion at label `l` with measure `n`. The entry traversal
may exit at an in-scope label with some measure, or into the residual context
`E`. Each label's body starts at the label's scope suffix and must exit at
in-scope labels with a smaller measure, or into `E`. The run then satisfies
the triple with the in-scope labels gone from the context. -/
theorem Program.tie {p : Program} {P : MachineData → Prop}
    {Q : Unit → MachineData → Prop} {E : Label → MachineData → Prop}
    (V : Nat → Label → MachineData → Prop)
    (hentry : ⦃P⦄ p
      ⦃Q; fun l s => (Program.fromLabel p l ≠ [] ∧ ∃ n, V n l s) ∨ E l s⦄)
    (hbody : ∀ n l, Program.fromLabel p l ≠ [] →
      ⦃V n l⦄ (Program.fromLabel p l)
      ⦃Q; fun l' s => (Program.fromLabel p l' ≠ [] ∧ ∃ n', n' < n ∧ V n' l' s)
                    ∨ E l' s⦄) :
    ⦃P⦄ p ⦃Q; E⦄ := by
  refine Triple.intro fun s hp => ?_
  have hmain : ∀ n l, Program.fromLabel p l ≠ [] → ∀ s', V n l s' →
      Eventually (Program.runStep p (Q ()) E) (fun _ => False) (s', l) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro l hmem s' hV
      have hmap : ∀ lx sx,
          ((Program.fromLabel p lx ≠ [] ∧ ∃ n', n' < n ∧ V n' lx sx) ∨ E lx sx) →
          Program.exitsTo p (Q ()) E lx sx := by
        rintro lx sx (⟨hm', n', hn', hV'⟩ | he)
        · exact Or.inr ⟨hm', ih n' hn' lx hm' sx hV'⟩
        · exact Or.inl he
      have hsub : ∀ lx, Program.fromLabel (Program.fromLabel p l) lx ≠ [] →
          Program.fromLabel p lx = Program.fromLabel (Program.fromLabel p l) lx :=
        fun lx h' => Program.fromLabel_of_suffix (Program.fromLabel_suffix p l) lx h'
      refine step_cps _ _ _ ?_
      show Program.wpF (Program.fromLabel p l) (Q ()) _ s'
      refine Program.wpF_mono (fun _ h => h) (fun lx sx hx => ?_) _ _
        ((hbody n l hmem).le_wp s' hV)
      rcases hx with he | ⟨hmq, hch⟩
      · exact hmap lx sx he
      · exact Or.inr ⟨hsub lx hmq ▸ hmq,
          Program.chain_lift hsub hmap (sx, lx) hmq hch⟩
  have hmapO : ∀ lx sx,
      ((Program.fromLabel p lx ≠ [] ∧ ∃ n, V n lx sx) ∨ E lx sx) →
      Program.exitsTo p (Q ()) E lx sx := by
    rintro lx sx (⟨hm', n, hV'⟩ | he)
    · exact Or.inr ⟨hm', hmain n lx hm' sx hV'⟩
    · exact Or.inl he
  refine Program.wpF_mono (fun _ h => h) (fun lx sx hx => ?_) _ _ (hentry.le_wp s hp)
  rcases hx with he | ⟨hmq, hch⟩
  · exact hmapO lx sx he
  · exact Or.inr ⟨hmq, Program.chain_lift (fun _ _ => rfl) hmapO (sx, lx) hmq hch⟩

end ProgramSpecs
