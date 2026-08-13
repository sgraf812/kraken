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
    -- Resolving a `match` or `if` scrutinee comes before the transport lemmas:
    -- against an unresolved scrutinee their unification reduces the interpreter
    -- to find a head symbol, and that reduction is the cost.
    repeat' first
      | exact hnext _ h
      | exact hjmp _ h
      | exact h.elim
      | exact hnext _ (h v)
      | exact (h v).elim
      | exact Width.noConfusion hcond
      | (split <;> rename_i hcond <;>
          simp only [hcond, Bool.false_eq_true, if_true, if_false] at h ⊢)
      | (split <;> rename_i hcond <;>
          simp only [hcond, Bool.false_eq_true, if_true, if_false] at h)
      | (split at h <;> rename_i hcond <;>
          simp only [hcond, Bool.false_eq_true, if_true, if_false])
      | refine operand_sound (fun v s' h => ?_) h
      | refine regOrMem_sound (fun v s' h => ?_) h
      | refine relRegOrMem_sound (fun v s' h => ?_) h
      | refine set_sound (fun s' h => ?_) h
      | refine load_sound (fun v s' h => ?_) h
      | refine store_sound (fun s' h => ?_) h
      | refine undefined_sound (fun v h => ?_) h
      | refine fun v => ?_
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

/-- Enter a segment through the lemma that extracts it: what the run from `pc`
does is what the weakest precondition of the extracted directives says. -/
theorem straightlineStep_of_seg [Layout] {e : Executable} {s : MachineData} {pc : Int64}
    {seg : List (Directive × Nat)} {post : MachineState → Prop}
    (hseg : e.directivesFromAddress pc = seg)
    (h : wp seg (fun _ _ => post) post e.labels (s, pc)) :
    straightlineStep e (s, pc) post :=
  straightlineStep_of_wp (hseg ▸ h)

/-- A segment that never falls through takes the run to its jump postcondition. -/
theorem straightlineStep_of_triple [Layout] {e : Executable} {s : MachineData} {pc : Int64}
    {seg : List (Directive × Nat)} {P : Labels → MachineState → Prop}
    {E : MachineState → Prop} (hseg : e.directivesFromAddress pc = seg)
    (h : ⦃P⦄ seg ⦃fun _ _ _ => False; E⦄) (hp : P e.labels (s, pc)) :
    straightlineStep e (s, pc) E :=
  straightlineStep_of_seg hseg
    (@Directives.wpE_mono e.labels _ _ _ _ (fun _ h => h.elim) (fun _ h => h) seg _
      (h.le_wp e.labels (s, pc) hp))

/-- A segment whose two postconditions are the run's continuation: whatever the
segment does, the run goes on from there. -/
theorem Eventually.of_triple [Layout] {e : Executable} {s : MachineData} {pc : Int64}
    {seg : List (Directive × Nat)} {P : Labels → MachineState → Prop}
    {post : @Post MachineState} (hseg : e.directivesFromAddress pc = seg)
    (h : ⦃P⦄ seg ⦃fun _ _ st => Eventually (straightlineStep e) post st;
                  fun st => Eventually (straightlineStep e) post st⦄)
    (hp : P e.labels (s, pc)) :
    Eventually (straightlineStep e) post (s, pc) :=
  step_cps _ post _ (straightlineStep_of_seg hseg (h.le_wp e.labels (s, pc) hp))

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

/-- A loop verified at its header address `e.labels.label l`: a run that reaches
the header with `k` iterations left reaches `post`. The back jump is not assumed
anywhere; it is what the body's jump postcondition demands.

The body is specified once, for every `k`: it never falls off its segment, and
each jump exit either returns to the header with one iteration accounted for or,
at zero, satisfies `Exit`. `hexit` takes the run from there. -/
theorem Eventually.loop [Layout] {e : Executable} {l : Label}
    {seg : List (Directive × Nat)} {I : Nat → MachineData → Prop}
    {Exit : MachineState → Prop} {post : @Post MachineState}
    (hseg : e.directivesFromAddress (e.labels.label l) = seg)
    (hbody : ∀ k,
      ⦃ fun labels st => labels = e.labels ∧ st.2 = e.labels.label l ∧ I k st.1 ⦄
        seg
      ⦃ fun _ _ _ => False;
        fun st => (k ≠ 0 ∧ st.2 = e.labels.label l ∧ I (k - 1) st.1) ∨ (k = 0 ∧ Exit st) ⦄)
    (hexit : ∀ st, Exit st → Eventually (straightlineStep e) post st) :
    ∀ k s, I k s → Eventually (straightlineStep e) post (s, e.labels.label l) := by
  have hstep : ∀ k s, I k s → straightlineStep e (s, e.labels.label l)
      (fun st => (k ≠ 0 ∧ st.2 = e.labels.label l ∧ I (k - 1) st.1) ∨ (k = 0 ∧ Exit st)) := by
    intro k s hI
    apply straightlineStep_of_wp
    rw [hseg]
    exact @Directives.wpE_mono e.labels _ _ _ _ (fun st h => h.elim) (fun st h => h) seg _
      ((hbody k).le_wp e.labels (s, e.labels.label l) ⟨rfl, rfl, hI⟩)
  intro k
  induction k with
  | zero =>
    intro s hI
    refine Eventually.step _ _ (hstep 0 s hI) ?_
    rintro st (⟨h0, -⟩ | ⟨-, hx⟩)
    · exact absurd rfl h0
    · exact hexit st hx
  | succ n ih =>
    intro s hI
    refine Eventually.step _ _ (hstep (n + 1) s hI) ?_
    rintro ⟨m, pc⟩ (⟨-, hpc, hIm⟩ | ⟨h0, -⟩)
    · simp only at hpc hIm
      subst hpc
      exact ih m hIm
    · exact absurd h0 (by omega)
