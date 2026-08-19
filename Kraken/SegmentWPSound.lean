/-
Soundness of the segment weakest precondition against the closed straightline
judgment. `Directive.interp_sound` transports each `Directive.wp` disjunct
into the baseline interpreter with real continuations, by a per-primitive
dictionary and one case analysis over the instruction set;
`Program.straightlineStep_of_wp` folds it over a sized segment.
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

/-- Transport one directive's transformer disjunction into the baseline
interpreter with real continuations. -/
theorem Directive.interp_sound [Labels] {P : MachineState → Prop}
    {d : Directive} {p : Std.Rco Int64} {s : MachineData}
    {next : MachineData → Prop} {jmp : MachineState → Prop} {k : MachineData → Effects}
    (hnext : ∀ s', next s' → (k s').All P) (hjmp : ∀ st, jmp st → P st)
    (h : (d.interp s p (fun s' => .done (s', 0)) (fun _ _ => .unimplemented "jump")).All
           (fun st => next st.1)
       ∨ (d.interp s p (fun _ => .unimplemented "fallthrough")
           (fun pc' s' => .done (s', pc'))).All jmp) :
    (d.interp s p k (fun pc' s' => .done (s', pc'))).All P := by
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

/- The fold transport unifies `Directive.interp` applications of a symbolic
directive; sealing the interpreters keeps that unification a comparison of
stuck applications instead of a symbolic machine run. -/
section InterpSealed

set_option allowUnsafeReducibility true in
attribute [local irreducible] Directive.interp Directives.interp

/-- Transport the traversal wp along a sized spelling of its text into the
baseline fold: `Q` lands at the fall-through past the end, `E` at a jump out,
resolved to the ambient table's addresses. -/
theorem Program.wpOpen_sound [Labels] {P : MachineState → Prop}
    {Q : MachineData → Prop} {E : Label → MachineData → Prop}
    (hQ : ∀ s' pc', Q s' → P (s', pc'))
    (hE : ∀ st, (∃ l, st.2 = label l ∧ E l st.1) → P st) :
    ∀ (ds : List (Directive × Nat)) {q : Program}, ds.map Prod.fst = q →
      ∀ (s : MachineData) (pc : Int64), Program.wpOpen q Q E s →
        (Directives.interp ds s pc (fun pc' s' => .done (s', pc'))).All P
  | [], _, rfl, s, pc, h => by
    simp only [Directives.interp, Effects.All]
    exact hQ s pc h
  | (d, sz) :: ds, _, rfl, s, pc, h => by
    simp only [List.map_cons, Program.wpOpen, Directive.wp] at h
    simp only [Directives.interp]
    rcases h ‹Labels› ⟨pc, pc + .ofNat sz⟩ with hfall | hjump
    · exact Directive.interp_sound
        (fun s' h' => Program.wpOpen_sound hQ hE ds rfl s' (pc + .ofNat sz) h')
        (fun st' h' => hE _ h')
        (Or.inl hfall)
    · refine Directive.interp_sound
        (fun s' h' => Program.wpOpen_sound hQ hE ds rfl s' (pc + .ofNat sz) h')
        (fun st' h' => hE _ h')
        (Or.inr (Effects.All.mono ?_ _ hjump))
      rintro st ⟨l, -, ha, he⟩
      exact ⟨l, ha, he⟩

/-- The traversal wp of the segment at `pc` establishes the omni-semantics
straightline judgment. -/
theorem Program.straightlineStep_of_wp [Layout] {e : Executable} {q : Program}
    {s : MachineData} {pc : Int64} {Q : MachineData → Prop}
    {E : Label → MachineData → Prop} {post : MachineState → Prop}
    (hds : (e.directivesFromAddress pc).map Prod.fst = q)
    (hQ : ∀ s' pc', Q s' → post (s', pc'))
    (hE : ∀ st, (∃ l, st.2 = e.labels.label l ∧ E l st.1) → post st)
    (h : Program.wpOpen q Q E s) :
    straightlineStep e (s, pc) post :=
  letI := e.labels
  Program.wpOpen_sound hQ hE _ hds s pc h

end InterpSealed

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
side condition `Program.WF` is decidable, so `Program.sound` discharges it
by `decide`. -/

/-- The segment at the start of the text: a run from `layout.start` traverses
the whole program. -/
theorem Program.extract_entry [layout : Layout] (p : Program) :
    (layout p).directivesFromAddress layout.start = Layout.frag 0 p := by
  have h := Executable.directivesFromAddress_addrOf (layout p) 0 (Nat.zero_le _)
    (fun k hk => absurd hk (Nat.not_lt_zero k))
  rw [← Layout.apply_snd]
  simpa [Layout.apply_fst] using h

/-- The segment at a label's address: the label's scope suffix, preceded by
a run of label cells that share the address. Alias labels make the run
nonempty: a label cell occupies no bytes, so a label directly after a label
sits at the same address, and the segment cuts at the first of them. -/
theorem Program.extract [layout : Layout] {p : Program}
    [hv : Executable.ValidLayout (layout p)] (hwf : Program.WF p)
    {l : Label} (hne : Program.fromLabel p l ≠ []) :
    ∃ j ls, (∀ d ∈ ls, d.isLabel = true) ∧
      (layout p).directivesFromAddress ((layout p).labels.label l)
        = Layout.frag j (ls ++ Program.fromLabel p l) := by
  obtain ⟨t, rest, hp, hfl, hfresh, hlen⟩ := Program.fromLabel_split hwf.nodup hne
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
  have hplen : t.length < p.length := by
    rw [hp]
    simp only [List.length_append, List.length_cons]
    omega
  have hle : t.length ≤ (layout p).2.length := by
    rw [Layout.apply_snd, Layout.frag_length]
    omega
  obtain ⟨j, hjle, hj, hmin⟩ :=
    Nat.exists_least_le (P := fun k => (layout p).addrOf k = (layout p).addrOf t.length) rfl
  have hdfa := Executable.directivesFromAddress_addrOf_first (layout p) j t.length
    hjle hle hj hmin
  have hdropt : p.drop t.length = Program.fromLabel p l := by
    conv => lhs; rw [hp]
    rw [List.drop_left, hfl]
  refine ⟨j, (p.drop j).take (t.length - j), ?_, ?_⟩
  · intro d hd
    obtain ⟨m, hm, heq⟩ := List.getElem_of_mem hd
    have hmlt : m < t.length - j := by
      have := List.length_take_le (t.length - j) (p.drop j)
      omega
    obtain ⟨l', z, hlz⟩ := Executable.label_between_of_addrOf_eq (layout p)
      (Nat.le_add_right j m) (show j + m < t.length by omega) hle hj
    rw [Layout.apply_snd, Layout.frag_getElem?] at hlz
    have hpcell : p[j + m]? = some (Directive.label l') := by
      cases hpp : p[j + m]? with
      | none => rw [hpp] at hlz; cases hlz
      | some d0 =>
        rw [hpp] at hlz
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hlz
        rw [hlz.1]
    have hds : some d = some (Directive.label l') := by
      rw [← hpcell, ← List.getElem?_drop, ← List.getElem?_take_of_lt hmlt,
        List.getElem?_eq_getElem hm, heq]
    obtain rfl := Option.some.inj hds
    rfl
  · rw [haddr, hdfa, Layout.apply_snd, Layout.frag_drop, Nat.zero_add]
    congr 1
    conv => lhs; rw [← List.take_append_drop (t.length - j) (p.drop j)]
    congr 1
    rw [List.drop_drop, show j + (t.length - j) = t.length from by omega]
    exact hdropt

private theorem Program.chain_sound [layout : Layout] {p : Program}
    {Q : MachineData → Prop} {E : Label → MachineData → Prop}
    (hlab : ∀ l, Program.fromLabel p l ≠ [] →
      ∃ j ls, (∀ d ∈ ls, d.isLabel = true) ∧
        (layout p).directivesFromAddress ((layout p).labels.label l)
          = Layout.frag j (ls ++ Program.fromLabel p l)) :
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
    obtain ⟨j, ls, hls, hseg⟩ := hlab st.2 hmem
    refine Eventually.step _
      (fun mid => (Q mid.1 ∨ ∃ l, mid.2 = (layout p).labels.label l ∧ E l mid.1)
        ∨ (∃ l, mid.2 = (layout p).labels.label l
            ∧ Program.fromLabel p l ≠ [] ∧ mid_p (mid.1, l)))
      (Program.straightlineStep_of_wp ?_ ?_ ?_ (Program.wpOpen_label_prefix hls ht)) ?_
    · rw [hseg]
      exact Layout.frag_map_fst _ _
    · exact fun s' pc' hq => Or.inl (Or.inl hq)
    · rintro st' ⟨l, ha, he⟩
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
    (h : Program.wpClosed p Q E s)
    (hwf : Program.WF p := by decide) :
    Eventually (straightlineStep (layout p))
      (fun mid => Q mid.1 ∨ ∃ l, mid.2 = (layout p).labels.label l ∧ E l mid.1)
      (s, layout.start) := by
  have hentry := Program.extract_entry (layout := layout) p
  have hlab : ∀ l, Program.fromLabel p l ≠ [] →
      ∃ j ls, (∀ d ∈ ls, d.isLabel = true) ∧
        (layout p).directivesFromAddress ((layout p).labels.label l)
          = Layout.frag j (ls ++ Program.fromLabel p l) :=
    fun l hne => Program.extract hwf hne
  refine Eventually.step _
    (fun mid => (Q mid.1 ∨ ∃ l, mid.2 = (layout p).labels.label l ∧ E l mid.1)
      ∨ (∃ l, mid.2 = (layout p).labels.label l ∧ Program.fromLabel p l ≠ []
          ∧ Eventually (Program.runStep p Q E) (fun _ => False) (mid.1, l)))
    (Program.straightlineStep_of_wp ?_ ?_ ?_ h) ?_
  · rw [hentry]
    exact Layout.frag_map_fst 0 p
  · exact fun s' pc' hq => Or.inl (Or.inl hq)
  · rintro st' ⟨l, ha, he⟩
    rcases he with he | ⟨hm, hch⟩
    · exact Or.inl (Or.inr ⟨l, ha, he⟩)
    · exact Or.inr ⟨l, ha, hm, hch⟩
  · rintro mid (hdone | ⟨l, ha, hm, hch⟩)
    · exact Eventually.done _ hdone
    · have hb := Program.chain_sound hlab (mid.1, l) hm hch
      rw [← ha] at hb
      exact hb
