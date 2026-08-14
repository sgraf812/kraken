/-
Soundness of the segment weakest precondition against the closed straightline
judgment. `Directive.wp1_sound` transports each `wp1` disjunct into the
baseline fold with real continuations, by a per-primitive dictionary and one
case analysis over the instruction set; `straightlineStep_of_wp` then
recovers `straightlineStep` as the diagonal `Q := E` of `Directives.wpE`.
-/
import Kraken.SegmentWP
import Kraken.SegmentExtract

open Std.Internal.Do

namespace SegmentWPSound

variable {P₁ P₂ : MachineState → Prop}

private theorem load_sound {s : MachineData} {addr : BitVec 64} {w : Width}
    {r₁ r₂ : w.type → MachineData → Effects}
    (hk : ∀ v s', (r₁ v s').All P₁ → (r₂ v s').All P₂)
    (h : (s.load addr w r₁).All P₁) : (s.load addr w r₂).All P₂ := by
  unfold MachineData.load at h ⊢
  simp only [Effects.All] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm] at h ⊢
  · exact h
  · exact hk _ _ h

private theorem store_sound {s : MachineData} {addr : BitVec 64} {w : Width} {v : w.type}
    {r₁ r₂ : MachineData → Effects}
    (hk : ∀ s', (r₁ s').All P₁ → (r₂ s').All P₂)
    (h : (s.store addr v r₁).All P₁) : (s.store addr v r₂).All P₂ := by
  unfold MachineData.store at h ⊢
  simp only [Effects.All] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm] at h ⊢
  · exact h
  · exact hk _ h

private theorem loadAvx_sound {s : MachineData} {addr : BitVec 64} {w : AvxWidth}
    {r₁ r₂ : w.type → MachineData → Effects}
    (hk : ∀ v s', (r₁ v s').All P₁ → (r₂ v s').All P₂)
    (h : (s.loadAvx addr w r₁).All P₁) : (s.loadAvx addr w r₂).All P₂ := by
  unfold MachineData.loadAvx at h ⊢
  simp only [Effects.All] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm] at h ⊢
  · exact h
  · exact hk _ _ h

private theorem storeAvx_sound {s : MachineData} {addr : BitVec 64} {w : AvxWidth} {v : w.type}
    {r₁ r₂ : MachineData → Effects}
    (hk : ∀ s', (r₁ s').All P₁ → (r₂ s').All P₂)
    (h : (s.storeAvx addr v r₁).All P₁) : (s.storeAvx addr v r₂).All P₂ := by
  unfold MachineData.storeAvx at h ⊢
  simp only [Effects.All] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm] at h ⊢
  · exact h
  · exact hk _ h

private theorem regOrMem_sound [Labels] [AddressSize] {w} {o : RegOrMem w}
    {s : MachineData} {p : Std.Rco Int64} {r₁ r₂ : w.type → MachineData → Effects}
    (hk : ∀ v s', (r₁ v s').All P₁ → (r₂ v s').All P₂)
    (h : (o.interp s p r₁).All P₁) : (o.interp s p r₂).All P₂ := by
  cases o with
  | reg r => exact hk _ _ h
  | mem a => exact load_sound hk h

private theorem operand_sound [Labels] [AddressSize] {w} {o : Operand w}
    {s : MachineData} {p : Std.Rco Int64} {r₁ r₂ : w.type → MachineData → Effects}
    (hk : ∀ v s', (r₁ v s').All P₁ → (r₂ v s').All P₂)
    (h : (o.interp s p r₁).All P₁) : (o.interp s p r₂).All P₂ := by
  cases o with
  | regOrMem rm => exact regOrMem_sound hk h
  | imm v => exact hk _ _ h

private theorem relRegOrMem_sound [Labels] [AddressSize] {o : RelRegOrMem}
    {s : MachineData} {p : Std.Rco Int64} {r₁ r₂ : BitVec 64 → MachineData → Effects}
    (hk : ∀ v s', (r₁ v s').All P₁ → (r₂ v s').All P₂)
    (h : (o.interp s p r₁).All P₁) : (o.interp s p r₂).All P₂ := by
  cases o with
  | rel c => exact hk _ _ h
  | reg r => exact hk _ _ h
  | mem a => exact load_sound hk h

private theorem set_sound [Labels] [AddressSize] {w} {d : Dst w} {v : w.type}
    {s : MachineData} {p : Std.Rco Int64} {r₁ r₂ : MachineData → Effects}
    (hk : ∀ s', (r₁ s').All P₁ → (r₂ s').All P₂)
    (h : (s.set d v p r₁).All P₁) : (s.set d v p r₂).All P₂ := by
  cases d with
  | reg r => exact hk _ h
  | mem a => exact store_sound hk h

private theorem avxRegOrMem_sound [Labels] [AddressSize] {w} {o : AvxRegOrMem w}
    {s : MachineData} {p : Std.Rco Int64} {r₁ r₂ : w.type → MachineData → Effects}
    (hk : ∀ v s', (r₁ v s').All P₁ → (r₂ v s').All P₂)
    (h : (o.interp s p r₁).All P₁) : (o.interp s p r₂).All P₂ := by
  cases o with
  | avx r => exact hk _ _ h
  | mem a => exact loadAvx_sound hk h

private theorem setAvx_sound [Labels] [AddressSize] {w} {d : AvxDst w} {v : w.type}
    {s : MachineData} {p : Std.Rco Int64} {r₁ r₂ : MachineData → Effects}
    (hk : ∀ s', (r₁ s').All P₁ → (r₂ s').All P₂)
    (h : (s.setAvx d v p r₁).All P₁) : (s.setAvx d v p r₂).All P₂ := by
  cases d with
  | avx r => exact hk _ h
  | mem a => exact storeAvx_sound hk h

private theorem setAvxLegacy_sound [Labels] [AddressSize] {w} {d : AvxDst w} {v : w.type}
    {s : MachineData} {p : Std.Rco Int64} {r₁ r₂ : MachineData → Effects}
    (hk : ∀ s', (r₁ s').All P₁ → (r₂ s').All P₂)
    (h : (s.setAvxLegacy d v p r₁).All P₁) : (s.setAvxLegacy d v p r₂).All P₂ := by
  cases d with
  | avx r => exact hk _ h
  | mem a => exact storeAvx_sound hk h


private theorem undefined_sound {α} [NondetSupportingType α] {r₁ r₂ : α → Effects}
    (hk : ∀ v, (r₁ v).All P₁ → (r₂ v).All P₂)
    (h : (Effects.undefined r₁).All P₁) : (Effects.undefined r₂).All P₂ :=
  fun v => hk v (h v)


/-! ## Propositional characterizations for the AVX primitives

The AVX widths make definitional unification evaluate `2^512`-scale type
indices; these equations let the avx branch rewrite `Effects.All` into small
propositions and close by monotonicity instead. -/

theorem _root_.All_loadAvx {P : MachineState → Prop} {s : MachineData} {addr : BitVec 64} {w : AvxWidth}
    {r : w.type → MachineData → Effects} :
    (s.loadAvx addr w r).All P ↔
      ∃ i, Mem.loadInt s.dmem addr w.bytes = some i ∧ (r (.ofInt _ i) s).All P := by
  unfold MachineData.loadAvx
  simp only [Effects.All]
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp_all [Effects.All]

theorem _root_.All_storeAvx {P : MachineState → Prop} {s : MachineData} {addr : BitVec 64} {w : AvxWidth}
    {v : w.type} {r : MachineData → Effects} :
    (s.storeAvx addr v r).All P ↔
      ∃ i, Mem.loadInt s.dmem addr w.bytes = some i
        ∧ (r { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }).All P := by
  unfold MachineData.storeAvx
  simp only [Effects.All]
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp_all [Effects.All]

/-- The proposition "the AVX operand read delivers `v`, and `K v s`". -/
def _root_.AvxRegOrMem.wpRead [Labels] [AddressSize] {w} (o : AvxRegOrMem w) (s : MachineData)
    (p : Std.Rco Int64) (K : w.type → MachineData → Prop) : Prop :=
  match o with
  | .avx r => K (s.zmms.get r) s
  | .mem a => ∃ i, Mem.loadInt s.dmem ((a.interp s.regs p).zeroExtend _) w.bytes = some i
      ∧ K (.ofInt _ i) s

theorem _root_.All_avxRegOrMem [Labels] [AddressSize] {w} {o : AvxRegOrMem w} {s : MachineData}
    {p : Std.Rco Int64} {r : w.type → MachineData → Effects} {P : MachineState → Prop} :
    (o.interp s p r).All P ↔ o.wpRead s p (fun v s' => (r v s').All P) := by
  cases o <;> simp only [AvxRegOrMem.interp, AvxRegOrMem.wpRead, All_loadAvx]

theorem _root_.AvxRegOrMem.wpRead_mono [Labels] [AddressSize] {w} {o : AvxRegOrMem w} {s : MachineData}
    {p : Std.Rco Int64} {K₁ K₂ : w.type → MachineData → Prop}
    (hK : ∀ v s', K₁ v s' → K₂ v s') : o.wpRead s p K₁ → o.wpRead s p K₂ := by
  cases o with
  | avx r => exact hK _ _
  | mem a => exact fun ⟨i, hi, hk⟩ => ⟨i, hi, hK _ _ hk⟩

/-- The proposition "the AVX destination write succeeds, and `K` holds". -/
def _root_.AvxDst.wpWrite [Labels] [AddressSize] {w} (d : AvxDst w) (v : w.type) (s : MachineData)
    (p : Std.Rco Int64) (legacy : Bool) (K : MachineData → Prop) : Prop :=
  match d with
  | .avx r => K (if legacy then s.setAvxLegacyReg r v else s.setAvxReg r v)
  | .mem a => ∃ i, Mem.loadInt s.dmem ((a.interp s.regs p).zeroExtend _) w.bytes = some i
      ∧ K { s with dmem := Mem.storeInt s.dmem ((a.interp s.regs p).zeroExtend _) w.bytes v.toInt }

theorem _root_.All_setAvx [Labels] [AddressSize] {w} {d : AvxDst w} {v : w.type} {s : MachineData}
    {p : Std.Rco Int64} {r : MachineData → Effects} {P : MachineState → Prop} :
    (s.setAvx d v p r).All P ↔ d.wpWrite v s p false (fun s' => (r s').All P) := by
  cases d <;> simp only [MachineData.setAvx, AvxDst.wpWrite, All_storeAvx, if_false,
    Bool.false_eq_true]

theorem _root_.All_setAvxLegacy [Labels] [AddressSize] {w} {d : AvxDst w} {v : w.type} {s : MachineData}
    {p : Std.Rco Int64} {r : MachineData → Effects} {P : MachineState → Prop} :
    (s.setAvxLegacy d v p r).All P ↔ d.wpWrite v s p true (fun s' => (r s').All P) := by
  cases d <;> simp only [MachineData.setAvxLegacy, AvxDst.wpWrite, All_storeAvx, if_true]

theorem _root_.AvxDst.wpWrite_mono [Labels] [AddressSize] {w} {d : AvxDst w} {v : w.type}
    {s : MachineData} {p : Std.Rco Int64} {legacy : Bool} {K₁ K₂ : MachineData → Prop}
    (hK : ∀ s', K₁ s' → K₂ s') : d.wpWrite v s p legacy K₁ → d.wpWrite v s p legacy K₂ := by
  cases d with
  | avx r => exact hK _
  | mem a => exact fun ⟨i, hi, hk⟩ => ⟨i, hi, hK _ hk⟩

/- The transport lemmas below are applied by search: at each goal the tactic
tries them in turn. An attempt that does not apply must still unify the lemma's
conclusion with the goal, and with the interpreter unfolding that unification
reduces a machine step looking for a head symbol to compare. Sealing the
definitions the lemmas are keyed on makes a mismatch a comparison of two head
symbols instead. -/
set_option allowUnsafeReducibility true in
attribute [local irreducible] RegOrMem.interp Operand.interp RelRegOrMem.interp
  AvxRegOrMem.interp MachineData.set MachineData.setAvx MachineData.setAvxLegacy
  MachineData.load MachineData.store MachineData.loadAvx MachineData.storeAvx

private theorem operation_sound {w} [Labels] [AddressSize] {P : MachineState → Prop}
    {op : Operation w} {p : Std.Rco Int64} {s : MachineData}
    {next : MachineData → Prop} {jmp : MachineState → Prop}
    {k : MachineData → Effects}
    (hnext : ∀ s', next s' → (k s').All P)
    (hjmp : ∀ st, jmp st → P st)
    (h : (Operation.interp op p s (fun s' => .done (s', 0))
            (fun _ _ => .unimplemented "jump")).All (fun st => next st.1)
       ∨ (Operation.interp op p s (fun _ => .unimplemented "fallthrough")
            (fun pc' s' => .done (s', pc'))).All jmp) :
    (Operation.interp op p s k (fun pc' s' => .done (s', pc'))).All P := by
  cases op <;>
    simp only [Operation.interp, Reg.interp, Effects.All] at h ⊢ <;>
    rcases h with h | h <;>
    repeat' first
      | exact hnext _ h
      | exact hjmp _ h
      | exact h.elim
      | exact hnext _ (h v)
      | exact (h v).elim
      | exact Width.noConfusion hcond
      | refine operand_sound (fun v s' h => ?_) h
      | refine regOrMem_sound (fun v s' h => ?_) h
      | refine relRegOrMem_sound (fun v s' h => ?_) h
      | refine set_sound (fun s' h => ?_) h
      | refine load_sound (fun v s' h => ?_) h
      | refine store_sound (fun s' h => ?_) h
      | refine undefined_sound (fun v h => ?_) h
      | refine fun v => ?_
      | (split <;> rename_i hcond <;>
          simp only [hcond, Bool.false_eq_true, if_true, if_false] at h ⊢)
      | (split <;> rename_i hcond <;>
          simp only [hcond, Bool.false_eq_true, if_true, if_false] at h)
      | (split at h <;> rename_i hcond <;>
          simp only [hcond, Bool.false_eq_true, if_true, if_false])
      | simp only [Effects.All] at h ⊢
      | simp only [] at h ⊢
      | cases w

end SegmentWPSound

section WP1Sound

open SegmentWPSound

/-- Transport one directive's `wp1` into the baseline interpreter with real
continuations. -/
theorem Directive.wp1_sound [Labels] {P : MachineState → Prop}
    {d : Directive} {p : Std.Rco Int64} {s : MachineData}
    {next : MachineData → Prop} {jmp : MachineState → Prop} {k : MachineData → Effects}
    (hnext : ∀ s', next s' → (k s').All P) (hjmp : ∀ st, jmp st → P st)
    (h : d.wp1 p next jmp s) :
    (d.interp s p k (fun pc' s' => .done (s', pc'))).All P := by
  unfold Directive.wp1 Directive.stepFall Directive.stepJump at h
  cases d with
  | label l =>
    simp only [Directive.interp, Effects.All] at h ⊢
    rcases h with h | h
    · exact hnext _ h
    · exact h.elim
  | byteArray bs =>
    simp only [Directive.interp, Effects.All] at h
    rcases h with h | h <;> exact h.elim
  | instr i =>
    simp only [Directive.interp] at h ⊢
    cases i with
    | regular asz osz op =>
      simp only [Instr.interp, Effects.All] at h ⊢
      generalize (AddressSize.mk asz : AddressSize) = A at h ⊢
      exact operation_sound hnext hjmp h
    | avx asz osz aop =>
      simp only [Instr.interp, Effects.All] at h ⊢
      generalize (AddressSize.mk asz : AddressSize) = A at h ⊢
      cases aop <;>
        simp only [AvxOperation.interp, All_avxRegOrMem, All_setAvx,
          All_setAvxLegacy, Effects.All] at h ⊢ <;>
        rcases h with h | h <;>
        repeat' first
          | exact hnext _ h
          | exact h.elim
          | refine AvxRegOrMem.wpRead_mono (fun v s' h => ?_) h
          | refine AvxDst.wpWrite_mono (fun s' h => ?_) h
          | simp only [] at h ⊢

end WP1Sound

/-- Transport the segment wp into the baseline fold: `Q` and `E` both entail
the merged exit predicate. -/
theorem Directives.wpE_sound [Labels] {P : MachineState → Prop} {Q E : MachineState → Prop}
    (hQ : ∀ st, Q st → P st) (hE : ∀ st, E st → P st) :
    ∀ (ds : List (Directive × Nat)) (st : MachineState),
      Directives.wpE ds Q E st →
      (Directives.interp ds st.1 st.2 (fun pc s => .done (s, pc))).All P
  | [], st, h => hQ _ h
  | (d, sz) :: ds, st, h => by
    simp only [Directives.interp, Directives.wpE] at h ⊢
    exact Directive.wp1_sound
      (fun s' h' => wpE_sound hQ hE ds (s', st.2 + .ofNat sz) h')
      (fun st' h' => hE _ h')
      h

/-- A segment triple establishes the omni-semantics straightline judgment as
the diagonal `Q := E := post`. -/
theorem straightlineStep_of_wp [Layout] {e : Executable} {s : MachineData} {pc : Int64}
    {post : MachineState → Prop}
    (h : wp (e.directivesFromAddress pc) (fun _ _ => post) post e.labels (s, pc)) :
    straightlineStep e (s, pc) post :=
  letI := e.labels
  Directives.wpE_sound (fun _ h => h) (fun _ h => h) (e.directivesFromAddress pc) (s, pc) h

/- `straightlineStep` is the API boundary: every proof enters through
`apply straightlineStep_of_wp`. Sealing it keeps that apply fast: whenever a
goal or expected type is headed by `straightlineStep` of a concrete
executable, the elaborator's whnf otherwise partially evaluates the
interpreter, getting stuck only after seconds of symbolic
`withAddresses`/`idxOf` reduction. An equality spelling applied with `rw`
sidesteps the same reduction even without the seal, since `kabstract` matches
at reducible transparency; keep it in mind for a use site the apply rule
cannot serve. -/
set_option allowUnsafeReducibility true in
attribute [irreducible] straightlineStep

/- Same seal for the segment computation: reducing `directivesFromAddress` on
a concrete executable partially evaluates `withAddresses` and `idxOf` over a
symbolic layout. Its API is the extraction equations
(Kraken/SegmentExtract.lean), which rewrite syntactically. -/
set_option allowUnsafeReducibility true in
attribute [irreducible] Executable.directivesFromAddress

/-! ## Runs

`Program.sound` reads a run triple back as the baseline judgment: from the
entry address, the machine eventually satisfies the run's fall-through
postcondition, or sits at the address of a label whose exit assertion holds.
`Program.extract` supplies the segment at each label's address; its
side conditions are decidable, so `Program.sound` discharges them by
`decide`. -/

/-- The segment at the start of the text: a run from `layout.start` traverses
the whole program. -/
theorem Program.extract_entry [layout : Layout] (p : Program) :
    (layout p).directivesFromAddress layout.start = Layout.frag 0 p := by
  have h := Executable.directivesFromAddress_addrOf (layout p) 0 (Nat.zero_le _)
    (fun k hk => absurd hk (Nat.not_lt_zero k))
  rw [← Layout.apply_snd]
  simpa [Layout.apply_fst] using h

/-- The segment at a label's address: the label's scope suffix, laid out at
its position. The side conditions: labels are unique, and no label cell
directly follows a label cell, so the label's address differs from every
earlier cut point. -/
theorem Program.extract [layout : Layout] {p : Program}
    [hv : Executable.ValidLayout (layout p)]
    (hnd : (Program.labels p).Nodup) (hsep : Program.sepLabels p = true)
    {l : Label} (hne : Program.fromLabel p l ≠ []) :
    (layout p).directivesFromAddress ((layout p).labels.label l)
      = Layout.frag (p.length - (Program.fromLabel p l).length) (Program.fromLabel p l) := by
  obtain ⟨t, rest, hp, hfl, hfresh, hlen⟩ := Program.fromLabel_split hnd hne
  have hcell : p[t.length]? = some (Directive.label l) := by
    rw [hp, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have hlay : (layout p).2[t.length]? = some (Directive.label l, layout.size t.length) := by
    rw [Layout.apply_snd, Layout.frag_getElem?, hcell]
    simp
  have haddr : (layout p).labels.label l = (layout p).addrOf t.length := by
    apply Executable.label_addrOf
    · rw [hlay, hv.label_size _ _ _ hlay]
    · have htake : ((layout p).2).take t.length = Layout.frag 0 t := by
        rw [Layout.apply_snd, hp, Layout.frag_append]
        exact List.take_left' (Layout.frag_length 0 t)
      intro dz hdz heq
      rw [htake] at hdz
      exact hfresh (Program.mem_labels_of_cell (heq ▸ Layout.frag_mem hdz))
  have hle : t.length ≤ (layout p).2.length := by
    rw [Layout.apply_snd, Layout.frag_length, hp]
    simp
  have hinj : ∀ k, k < t.length → (layout p).addrOf k ≠ (layout p).addrOf t.length := by
    intro k hk
    have hlt : t.length - 1 < p.length := by
      rw [hp]
      simp only [List.length_append, List.length_cons]
      omega
    apply Executable.addrOf_ne_of_valid (layout p) hk
    · rw [Layout.apply_snd, Layout.frag_getElem?]
      simp [List.getElem?_eq_getElem hlt]
    · intro l' z hzeq
      rw [Layout.apply_snd, Layout.frag_getElem?] at hzeq
      have hp' : p[t.length - 1]? = some (Directive.label l') := by
        cases hpp : p[t.length - 1]? with
        | none => rw [hpp] at hzeq; cases hzeq
        | some d =>
          rw [hpp] at hzeq
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hzeq
          rw [hzeq.1]
      have hk1 : t.length - 1 + 1 = t.length := by omega
      exact Program.sepLabels_spec hsep (t.length - 1) l (hk1 ▸ hcell) l' hp'
  have hdfa := Executable.directivesFromAddress_addrOf (layout p) t.length hle hinj
  rw [haddr, hdfa, ← hlen, hfl, hp]
  with_reducible exact Layout.apply_drop t (Directive.label l :: rest)

private theorem Program.chain_sound [layout : Layout] {p : Program}
    {Q : MachineData → Prop} {E : Label → MachineData → Prop}
    (hlab : ∀ l, Program.fromLabel p l ≠ [] →
      (layout p).directivesFromAddress ((layout p).labels.label l)
        = Layout.frag (p.length - (Program.fromLabel p l).length) (Program.fromLabel p l)) :
    ∀ st, Program.fromLabel p st.2 ≠ [] →
      Eventually (Program.runStep p Q E) (fun _ => False) st →
      Eventually (straightlineStep (layout p))
        (fun mid => Q mid.1 ∨ ∃ l, mid.2 = (layout p).labels.label l ∧ E l mid.1)
        (st.1, (layout p).labels.label st.2) := by
  intro st hmem h
  revert hmem
  induction h with
  | done st hp => exact fun _ => hp.elim
  | step st mid_p ht _ ih =>
    intro hmem
    letI : Labels := (layout p).labels
    have hw := Program.wpF_toE (Layout.frag (p.length - (Program.fromLabel p st.2).length)
        (Program.fromLabel p st.2))
      (Layout.frag_map_fst _ _) st.1 ((layout p).labels.label st.2) ht
    refine Eventually.step _
      (fun mid => (Q mid.1 ∨ ∃ l, mid.2 = (layout p).labels.label l ∧ E l mid.1)
        ∨ (∃ l, mid.2 = (layout p).labels.label l
            ∧ Program.fromLabel p l ≠ [] ∧ mid_p (mid.1, l)))
      (straightlineStep_of_wp ?_) ?_
    · rw [hlab st.2 hmem]
      refine Directives.wpE_mono (fun mid hq => ?_) (fun mid hx => ?_) _ _ hw
      · exact Or.inl (Or.inl hq)
      · obtain ⟨l, ha, he⟩ := hx
        rcases he with he | ⟨hm, hmid⟩
        · exact Or.inl (Or.inr ⟨l, ha, he⟩)
        · exact Or.inr ⟨l, ha, hm, hmid⟩
    · rintro mid (hdone | ⟨l, ha, hm, hmid⟩)
      · exact Eventually.done _ hdone
      · have hb := ih (mid.1, l) hmid hm
        rw [← ha] at hb
        exact hb

/-- A run triple, read at the machine: from the entry address, the machine
eventually satisfies the fall-through postcondition, or sits at the address of
a label whose exit assertion holds. -/
theorem Program.sound [layout : Layout] {p : Program}
    [hv : Executable.ValidLayout (layout p)]
    {Q : MachineData → Prop} {E : Label → MachineData → Prop} {s : MachineData}
    (h : Program.wpR p Q E s)
    (hnd : (Program.labels p).Nodup := by decide)
    (hsep : Program.sepLabels p = true := by decide) :
    Eventually (straightlineStep (layout p))
      (fun mid => Q mid.1 ∨ ∃ l, mid.2 = (layout p).labels.label l ∧ E l mid.1)
      (s, layout.start) := by
  have hentry := Program.extract_entry (layout := layout) p
  have hlab : ∀ l, Program.fromLabel p l ≠ [] →
      (layout p).directivesFromAddress ((layout p).labels.label l)
        = Layout.frag (p.length - (Program.fromLabel p l).length) (Program.fromLabel p l) :=
    fun l hne => Program.extract hnd hsep hne
  letI : Labels := (layout p).labels
  have hw := Program.wpF_toE (Layout.frag 0 p) (Layout.frag_map_fst 0 p) s layout.start h
  refine Eventually.step _
    (fun mid => (Q mid.1 ∨ ∃ l, mid.2 = (layout p).labels.label l ∧ E l mid.1)
      ∨ (∃ l, mid.2 = (layout p).labels.label l ∧ Program.fromLabel p l ≠ []
          ∧ Eventually (Program.runStep p Q E) (fun _ => False) (mid.1, l)))
    (straightlineStep_of_wp ?_) ?_
  · rw [hentry]
    refine Directives.wpE_mono (fun mid hq => ?_) (fun mid hx => ?_) _ _ hw
    · exact Or.inl (Or.inl hq)
    · obtain ⟨l, ha, he⟩ := hx
      rcases he with he | ⟨hm, hch⟩
      · exact Or.inl (Or.inr ⟨l, ha, he⟩)
      · exact Or.inr ⟨l, ha, hm, hch⟩
  · rintro mid (hdone | ⟨l, ha, hm, hch⟩)
    · exact Eventually.done _ hdone
    · have hb := Program.chain_sound hlab (mid.1, l) hm hch
      rw [← ha] at hb
      exact hb
