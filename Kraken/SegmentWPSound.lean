/-
Soundness of the segment weakest precondition against the closed straightline
judgment. `Directive.wp1_sound` transports each `wp1` disjunct into the
baseline fold with real continuations, by a per-primitive dictionary and one
case analysis over the instruction set; `straightlineStep_of_wp` then
recovers `straightlineStep` as the diagonal `Q := E` of `Directives.wpE`.
-/
import Kraken.SegmentWP

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

A run of a program is the omni-semantics judgment over `Program.runStep`:
`Eventually (Program.runStep prog E) Q st` says the run reaches `Q`, or leaves
the program text at a state in `E`. -/

/-- The omni-semantics judgment is monotone in its transition relation and in
its postcondition. -/
theorem Eventually.mono {State : Type} {trans₁ trans₂ : State → Post → Prop}
    {P Q : @Post State} {st : State} (h : Eventually trans₁ P st)
    (htrans : ∀ st' post, trans₁ st' post → trans₂ st' post) (hPQ : ∀ s, P s → Q s) :
    Eventually trans₂ Q st := by
  induction h with
  | done st hp => exact Eventually.done st (hPQ st hp)
  | step st mid_p ht _ ih => exact Eventually.step st mid_p (htrans st mid_p ht) ih

/-- One segment of a run. A jump whose target is a directive of `prog` keeps
the run going, so it lands back in the continuation `post`; a jump that leaves
the program text leaves through `E`. -/
def Program.runStep [layout : Layout] (prog : Program) (E : MachineState → Prop)
    (st : MachineState) (post : @Post MachineState) : Prop :=
  wp ((layout prog).directivesFromAddress st.2) (fun _ _ mid => post mid)
    (fun mid => ((layout prog).directivesFromAddress mid.2 = [] → E mid)
              ∧ ((layout prog).directivesFromAddress mid.2 ≠ [] → post mid))
    (layout prog).labels st

/-- Weakening what a jump out of the program text may conclude. -/
theorem Program.runStep_mono [Layout] {prog : Program} {E₁ E₂ : MachineState → Prop}
    {st : MachineState} {post : @Post MachineState} (hE : ∀ st', E₁ st' → E₂ st')
    (h : Program.runStep prog E₁ st post) : Program.runStep prog E₂ st post :=
  Directives.wp_mono _ _ _ (fun _ h => h)
    (fun st' h => ⟨fun hnil => hE st' (h.1 hnil), h.2⟩) h

/-- Enter the run at `pc` through the extraction lemma for that address: the
run continues from whatever the fragment there does. The fall-through
continuation holds at every address, because a sizing-invariant traversal
cannot know where it lands; a jump continues the run inside the text and
leaves through `E` outside it. `vcgen` discharges the wp obligation with the
`Program` specs. -/
theorem Eventually.enter [layout : Layout] {prog : Program} {n : Nat} {p : Program}
    {E : MachineState → Prop} {post : @Post MachineState} {s : MachineData} {pc : Int64}
    (hseg : (layout prog).directivesFromAddress pc = Layout.frag n p)
    (h : wp p (fun _ _ s' => ∀ pc', Eventually (Program.runStep prog E) post (s', pc'))
          (fun mid => ((layout prog).directivesFromAddress mid.2 = [] → E mid)
                    ∧ ((layout prog).directivesFromAddress mid.2 ≠ [] →
                        Eventually (Program.runStep prog E) post mid))
          (layout prog).labels s) :
    Eventually (Program.runStep prog E) post (s, pc) := by
  refine step_cps _ _ _ ?_
  rw [Program.runStep, hseg]
  letI : Labels := (layout prog).labels
  have hw := Program.wpF_toE (Layout.frag n p) (Layout.frag_map_fst n p) s pc h
  exact Directives.wpE_mono (fun st hq => hq st.2) (fun _ hh => hh) _ _ hw

/-- What a run says about the machine: the baseline judgment that the run
reaches the normal postcondition, or leaves the program text at the
exceptional one. Every rule about `Program.runStep` is answerable to this
reading. -/
theorem Program.run_sound [layout : Layout] {prog : Program}
    {Q : @Post MachineState} {E : MachineState → Prop} {st : MachineState}
    (h : Eventually (Program.runStep prog E) Q st) :
    Eventually (straightlineStep (layout prog)) (fun mid => Q mid ∨ E mid) st := by
  induction h with
  | done st hq => exact Eventually.done st (Or.inl hq)
  | step st mid_p hstep _ ih =>
    refine Eventually.step st _ (straightlineStep_of_wp ?_) (fun _ h => h)
    refine Directives.wp_mono _ _ _ (fun mid hq => ih mid hq) (fun mid hmid => ?_) hstep
    by_cases hnil : (layout prog).directivesFromAddress mid.2 = []
    · exact Eventually.done mid (Or.inr (hmid.1 hnil))
    · exact ih mid (hmid.2 hnil)

/-- A loop verified at its header label `l`: a run that reaches the header
with `k` iterations left reaches `post`. The back jump is not assumed
anywhere; it is what the body's jump postcondition demands.

The body is one `Program` triple, for every `k`: the body never falls off its
fragment, and each jump exit either returns to the header with one iteration
accounted for or, at zero, satisfies `Exit`. `hin` says the body's exits stay
inside the program text, so the run continues at them rather than leaving
through `E`. -/
theorem Eventually.loop [layout : Layout] {prog : Program} {l : Label} {n : Nat}
    {body : Program} {I : Nat → MachineData → Prop}
    {Exit : MachineState → Prop} {E : MachineState → Prop} {post : @Post MachineState}
    (hseg : (layout prog).directivesFromAddress ((layout prog).labels.label l)
      = Layout.frag n body)
    (hbody : ∀ k,
      ⦃ fun labels s => labels = (layout prog).labels ∧ I k s ⦄
        body
      ⦃ fun _ _ _ => False;
        fun st => (k ≠ 0 ∧ st.2 = (layout prog).labels.label l ∧ I (k - 1) st.1)
                ∨ (k = 0 ∧ Exit st) ⦄)
    (hin : ∀ st, ((st.2 = (layout prog).labels.label l) ∨ Exit st) →
      (layout prog).directivesFromAddress st.2 ≠ [])
    (hexit : ∀ st, Exit st → Eventually (Program.runStep prog E) post st) :
    ∀ k s, I k s →
      Eventually (Program.runStep prog E) post (s, (layout prog).labels.label l) := by
  have hstep : ∀ k s, I k s →
      Program.runStep prog E (s, (layout prog).labels.label l)
        (fun st => (k ≠ 0 ∧ st.2 = (layout prog).labels.label l ∧ I (k - 1) st.1)
                 ∨ (k = 0 ∧ Exit st)) := by
    intro k s hI
    rw [Program.runStep, hseg]
    letI : Labels := (layout prog).labels
    have hw := Program.wpF_toE (Layout.frag n body) (Layout.frag_map_fst n body) s
      ((layout prog).labels.label l) ((hbody k).le_wp (layout prog).labels s ⟨rfl, hI⟩)
    refine Directives.wpE_mono (fun st hq => hq.elim) (fun st hh => ⟨fun hnil => ?_, fun _ => hh⟩)
      _ _ hw
    exact absurd hnil (hin st (hh.elim (fun a => Or.inl a.2.1) (fun b => Or.inr b.2)))
  intro k
  induction k with
  | zero =>
    intro s hI
    refine Eventually.step _ _ (hstep 0 s hI) ?_
    rintro st (⟨h0, -⟩ | ⟨-, hx⟩)
    · exact absurd rfl h0
    · exact hexit st hx
  | succ m ih =>
    intro s hI
    refine Eventually.step _ _ (hstep (m + 1) s hI) ?_
    rintro ⟨d, pc⟩ (⟨-, hpc, hId⟩ | ⟨h0, -⟩)
    · simp only at hpc hId
      subst hpc
      exact ih d hId
    · exact absurd h0 (by omega)
