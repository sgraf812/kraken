/-
Weakest preconditions on the deep embedding. `Directive.wp` is the run
transformer of a single directive: a fall-through postcondition and a jump
postcondition at the address of the target label, quantified over every label
table and instruction extent, so no assertion mentions the layout.
`Program.wpOpen` folds it over the text, with every jump an open exit into
`E`; `Program.wpClosed` closes the in-text labels by re-entry
(`Program.exitsTo`). The `WP` instance on `Directive` reads a directive as
the singleton program; the instance on `Program` is `Program.wpClosed`: a
fall-through past the end of the text lands in `Q`, and a jump exit either
surfaces in `E` or re-enters at the label's cell.
`Program.cons_spec` lifts the per-instruction triples through the text, and
`Program.cfg` verifies a labeled program from one spec table and one variant.
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

/-- The target label of a jump instruction. -/
def Directive.target : Directive → Option Label
  | .instr (.regular _ _ (.jcc _ l)) => some l
  | .instr (.regular _ _ (.jmp (.rel (.sub (.label l) .after_current_instruction)))) => some l
  | _ => none

/-- The run transformer of one directive: `Q` at a fall-through, `E` at a jump
out, at the address the label table gives the target. The quantification over
label tables and instruction extents keeps every assertion free of the layout.
The disjunction is exact because `Operation.interp` decides jump-ness before
any nondeterminism: each tree calls only one of its two continuations, and the
other is poisoned by the `Effects.All = False` leaf. -/
def Directive.wp (d : Directive) (Q : MachineData → Prop)
    (E : Label → MachineData → Prop) (s : MachineData) : Prop :=
  ∀ (labels : Labels) (r : Std.Rco Int64),
      (d.interp s r (fun s' => .done (s', 0)) (fun _ _ => .unimplemented "jump")).All
        (fun st => Q st.1)
    ∨ (d.interp s r (fun _ => .unimplemented "fallthrough") (fun pc' s' => .done (s', pc'))).All
        (fun st => ∃ l, d.target = some l ∧ st.2 = labels.label l ∧ E l st.1)

theorem Directive.wp_mono {d : Directive} {s : MachineData}
    {Q₁ Q₂ : MachineData → Prop} {E₁ E₂ : Label → MachineData → Prop}
    (hQ : ∀ s', Q₁ s' → Q₂ s') (hE : ∀ l s', E₁ l s' → E₂ l s')
    (h : d.wp Q₁ E₁ s) : d.wp Q₂ E₂ s := fun labels r =>
  (h labels r).imp (Effects.All.mono (fun st => hQ st.1) _)
    (Effects.All.mono (fun _st ⟨l, ht, ha, he⟩ => ⟨l, ht, ha, hE l _ he⟩) _)

def Directive.wpTrans (d : Directive) :
    PredTrans (MachineData → Prop) (Label → MachineData → Prop) Unit :=
  ⟨fun Q E s => d.wp (Q ()) E s⟩

/-- A directive is the singleton program. -/
instance instWPDirective :
    WP Directive Unit (MachineData → Prop) (Label → MachineData → Prop) where
  wpTrans := Directive.wpTrans
  wp_trans_monotone _ _ _ _ _ hE hQ := fun _s h =>
    Directive.wp_mono (fun s' => hQ () s') hE h

/-- Unfold a directive's wp into the transformer. -/
theorem Directive.wp_eq (d : Directive) (Q : Unit → MachineData → Prop)
    (E : Label → MachineData → Prop) (s : MachineData) :
    WP.wp d Q E s = d.wp (Q ()) E s := rfl

/-! ### Fragments

`Layout.frag` names a fragment as it is laid out at a position of its host
program. Extraction lemmas end in `Layout.frag` terms, and `Program.wp_sound`
transports a fragment's wp at them. -/

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

theorem Layout.frag_getElem? [layout : Layout] (n : Nat) (p : Program) (i : Nat) :
    (Layout.frag n p)[i]? = (p[i]?).map (fun d => (d, layout.size (n + i))) := by
  induction p generalizing n i with
  | nil => simp
  | cons d ds ih =>
    cases i with
    | zero => simp
    | succ j =>
      rw [show n + (j + 1) = n + 1 + j from by omega]
      simp only [Layout.frag_cons, List.getElem?_cons_succ, ih (n + 1) j]

theorem Layout.frag_drop [Layout] (n k : Nat) (p : Program) :
    (Layout.frag n p).drop k = Layout.frag (n + k) (p.drop k) := by
  induction p generalizing n k with
  | nil => simp
  | cons d ds ih =>
    cases k with
    | zero => simp
    | succ m =>
      rw [Layout.frag_cons, List.drop_succ_cons, List.drop_succ_cons, ih (n + 1) m,
        show n + 1 + m = n + (m + 1) from by omega]

theorem Layout.frag_mem [Layout] {n : Nat} {p : Program} {dz : Directive × Nat}
    (h : dz ∈ Layout.frag n p) : dz.1 ∈ p := by
  induction p generalizing n with
  | nil => cases h
  | cons d ds ih =>
    rw [Layout.frag_cons] at h
    rcases List.mem_cons.mp h with heq | hmem
    · rw [heq]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hmem)

@[simp] theorem Layout.frag_map_fst [Layout] (n : Nat) (p : Program) :
    (Layout.frag n p).map Prod.fst = p := by
  induction p generalizing n with
  | nil => rfl
  | cons d ds ih => simp [ih]

/-- A fragment splits where the program it lays out splits. -/
theorem Layout.frag_append [layout : Layout] (n : Nat) (as bs : Program) :
    Layout.frag n (as ++ bs) = Layout.frag n as ++ Layout.frag (n + as.length) bs := by
  simp [Layout.frag, List.mapIdx_append, Nat.add_left_comm, Nat.add_comm]

/-! ### Programs

A `Program` is a directive list with no sizes. Its transformer runs each
directive under every label table and at every instruction range a layout can
give it, so a fragment's triple mentions no layout, no position, no program
counter, and no label table. The fall-through channel carries `MachineData`
alone. A jump exit names the target label, not an address: `E : Label →
MachineData → Prop`, and the labels a spec's `E` mentions are the fragment's
whole interface to its host program. -/

def Program.wpOpen : Program → (MachineData → Prop) → (Label → MachineData → Prop) →
    MachineData → Prop
  | [], Q, _, s => Q s
  | d :: p, Q, E, s => d.wp (Program.wpOpen p Q E) E s

theorem Program.wpOpen_mono {Q₁ Q₂ : MachineData → Prop} {E₁ E₂ : Label → MachineData → Prop}
    (hQ : ∀ s, Q₁ s → Q₂ s) (hE : ∀ l s, E₁ l s → E₂ l s) :
    ∀ (p : Program) (s : MachineData), Program.wpOpen p Q₁ E₁ s → Program.wpOpen p Q₂ E₂ s
  | [], s => hQ s
  | _ :: p, _ => fun h => Directive.wp_mono (fun s' => wpOpen_mono hQ hE p s') hE h

/-- Sequential composition of the traversal: a fall-through of `as` continues
into `bs`, a jump exits the whole fragment. -/
theorem Program.wpOpen_append (as bs : Program) (Q : MachineData → Prop)
    (E : Label → MachineData → Prop) :
    Program.wpOpen (as ++ bs) Q E = Program.wpOpen as (Program.wpOpen bs Q E) E := by
  induction as with
  | nil => rfl
  | cons d p ih => funext s; simp only [List.cons_append, Program.wpOpen, ih]

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

/-- An instruction cell is invisible to the scope lookup. -/
@[simp] theorem Program.fromLabel_cons_instr (i : Instr) (p : Program) (l : Label) :
    Program.fromLabel (Directive.instr i :: p) l = Program.fromLabel p l := by
  rw [Program.fromLabel_cons, if_neg (by rintro ⟨-, h⟩; cases h)]

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
  Program.wpOpen (Program.fromLabel p st.2) Q
    (fun l s => E l s ∨ (Program.fromLabel p l ≠ [] ∧ post (s, l))) st.1

/-- Where a jump exit at `l` goes: it surfaces in `E`, or, in scope, the run
re-enters at `l` and the chain of re-entries ends. -/
def Program.exitsTo (p : Program) (Q : MachineData → Prop) (E : Label → MachineData → Prop)
    (l : Label) (s : MachineData) : Prop :=
  E l s ∨ (Program.fromLabel p l ≠ [] ∧
    Eventually (Program.runStep p Q E) (fun _ => False) (s, l))

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
    · show Program.wpOpen (Program.fromLabel pf st.2) Q _ st.1
      rw [hsub st.2 hmem]
      refine Program.wpOpen_mono (fun _ h => h) (fun lx s' hx => ?_) _ _ ht
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
  fun _ _ h => Program.wpOpen_mono hQ
    (fun l s hx => hx.imp (hE l s) (fun ⟨hm, hp⟩ => ⟨hm, hp⟩)) _ _ h

theorem Program.exitsTo_mono {p : Program} {Q₁ Q₂ : MachineData → Prop}
    {E₁ E₂ : Label → MachineData → Prop}
    (hQ : ∀ s, Q₁ s → Q₂ s) (hE : ∀ l s, E₁ l s → E₂ l s) :
    ∀ l s, Program.exitsTo p Q₁ E₁ l s → Program.exitsTo p Q₂ E₂ l s :=
  fun l s hx => hx.imp (hE l s)
    (fun ⟨hm, hch⟩ => ⟨hm, hch.mono (Program.runStep_mono hQ hE) (fun _ f => f)⟩)

/-- An instruction cell puts no label in scope, so the exit dispatch of the
tail is the exit dispatch of the whole text. -/
theorem Program.exitsTo_cons_instr (i : Instr) (p : Program)
    (Q : MachineData → Prop) (E : Label → MachineData → Prop) :
    Program.exitsTo (Directive.instr i :: p) Q E = Program.exitsTo p Q E := by
  have hrs : Program.runStep (Directive.instr i :: p) Q E = Program.runStep p Q E := by
    funext st post
    simp only [Program.runStep, Program.fromLabel_cons_instr]
  funext l s
  simp only [Program.exitsTo, Program.fromLabel_cons_instr, hrs]

/-- The run wp: the traversal, with jumps resolved through the exit dispatch.
A triple on a `Program` states this transformer. -/
def Program.wpClosed (p : Program) (Q : MachineData → Prop)
    (E : Label → MachineData → Prop) (s : MachineData) : Prop :=
  Program.wpOpen p Q (Program.exitsTo p Q E) s

/-- Open jumps strengthen closed ones: a jump that lands in `E` is one
disjunct of the dispatch. -/
theorem Program.wpClosed_of_wpOpen {p : Program} {Q : MachineData → Prop}
    {E : Label → MachineData → Prop} {s : MachineData}
    (h : Program.wpOpen p Q E s) : Program.wpClosed p Q E s :=
  Program.wpOpen_mono (fun _ h => h) (fun l s' he => Or.inl he) p s h

def Program.wpTrans (p : Program) :
    PredTrans (MachineData → Prop) (Label → MachineData → Prop) Unit :=
  ⟨fun Q E s => Program.wpClosed p (Q ()) E s⟩

namespace Program.ClosedWP

/-- A triple on a program states the run wp. -/
scoped instance instWP :
    WP Program Unit (MachineData → Prop) (Label → MachineData → Prop) where
  wpTrans := Program.wpTrans
  wp_trans_monotone _ _ _ _ _ hE hQ := fun s =>
    Program.wpOpen_mono (fun s' => hQ () s')
      (Program.exitsTo_mono (fun s' => hQ () s') hE) _ s

/-- Unfold the run wp into its transformer. -/
theorem wp_eq (p : Program) (Q : Unit → MachineData → Prop)
    (E : Label → MachineData → Prop) (s : MachineData) :
    WP.wp p Q E s = Program.wpClosed p (Q ()) E s := rfl

end Program.ClosedWP

namespace Program.OpenWP

/-- A triple on a program states the traversal: every jump lands in `E`. -/
scoped instance instWP :
    WP Program Unit (MachineData → Prop) (Label → MachineData → Prop) where
  wpTrans p := ⟨fun Q E s => Program.wpOpen p (Q ()) E s⟩
  wp_trans_monotone _ _ _ _ _ hE hQ := fun s =>
    Program.wpOpen_mono (fun s' => hQ () s') hE _ s

/-- Unfold the traversal wp into its transformer. -/
theorem wp_eq (p : Program) (Q : Unit → MachineData → Prop)
    (E : Label → MachineData → Prop) (s : MachineData) :
    WP.wp p Q E s = Program.wpOpen p (Q ()) E s := rfl

end Program.OpenWP

/-! ### Per-instruction specs

One triple per instruction shape, on the `Directive` instance: a fall-through
instruction's precondition is `Q` at the record update it performs, a jump's
precondition is `E` at the target. `Program.cons_spec` lifts them through the
text: the head's fall-through post is the tail's wp, the head's jump post is
the tail's exit dispatch. -/

section ProgramSpecs

open Program.ClosedWP

variable {Q : Unit → MachineData → Prop} {E : Label → MachineData → Prop} {p : Program}

local macro "wp_step" : tactic =>
  `(tactic| simp only [Program.ClosedWP.wp_eq, Directive.wp_eq, Program.wpOpen, Directive.wp,
      Directive.interp, Instr.interp,
      Operation.interp, Operand.interp, RegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, Reg64s.get_low64, Reg64s.set_low64, Effects.All,
      or_false, false_or])

@[spec] theorem Program.nil_spec :
    ⦃ fun s => Q () s ⦄ ([] : Program) ⦃ Q; E ⦄ :=
  Triple.intro fun _ h => h

/-- The append cases are spelling: `vcgen` walks a `++` of fragments by
rewriting it to the cons cell on top. -/
@[spec] theorem Program.nil_append_spec (bs : Program) :
    ⦃ fun s => WP.wp bs Q E s ⦄ (([] : Program) ++ bs) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by rw [List.nil_append]; exact h

@[spec] theorem Program.cons_append_spec (a : Directive) (as bs : Program) :
    ⦃ fun s => WP.wp (a :: (as ++ bs)) Q E s ⦄ ((a :: as) ++ bs) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by rw [List.cons_append]; exact h

@[spec] theorem Program.append_assoc_spec (as bs cs : Program) :
    ⦃ fun s => WP.wp (as ++ (bs ++ cs)) Q E s ⦄ ((as ++ bs) ++ cs) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by rw [List.append_assoc]; exact h

@[spec] theorem Program.label_spec (l : Label) :
    ⦃ fun s => WP.wp p Q E s ⦄ (Directive.label l :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun _ h => by
    intro labels rco
    wp_step
    exact Program.wpOpen_mono (fun _ h => h) (Program.exitsTo_grow _) _ _ h

def Directive.isLabel : Directive → Bool
  | .label _ => true
  | _ => false

/-- A leading run of label cells changes no traversal assertion. -/
theorem Program.wpOpen_label_prefix {ls : Program} (hls : ∀ d ∈ ls, d.isLabel = true)
    {p : Program} {Q : MachineData → Prop} {E : Label → MachineData → Prop} {s : MachineData}
    (h : Program.wpOpen p Q E s) : Program.wpOpen (ls ++ p) Q E s := by
  induction ls with
  | nil => exact h
  | cons d ls ih =>
    cases d with
    | label l =>
      intro labels rco
      wp_step
      exact ih fun d hd => hls d (List.mem_cons_of_mem _ hd)
    | instr i => exact absurd (hls _ List.mem_cons_self) (by simp [Directive.isLabel])
    | byteArray a => exact absurd (hls _ List.mem_cons_self) (by simp [Directive.isLabel])

/-- The run wp at an instruction cell, unfolded: the head's fall-through post
is the tail's wp, the head's jump post is the tail's exit dispatch. -/
theorem Program.wp_cons_instr (i : Instr) (p : Program) (Q : Unit → MachineData → Prop)
    (E : Label → MachineData → Prop) (s : MachineData) :
    WP.wp (Directive.instr i :: p) Q E s
      = WP.wp (Directive.instr i) (fun _ => WP.wp p Q E) (Program.exitsTo p (Q ()) E) s := by
  show Program.wpOpen (Directive.instr i :: p) (Q ())
    (Program.exitsTo (Directive.instr i :: p) (Q ()) E) s = _
  rw [Program.exitsTo_cons_instr]
  rfl

/-- The cons rule: the head instruction's triple, with the tail's wp as the
fall-through post. The jump post is `E` itself, one disjunct of the exit
dispatch `Program.wp_cons_instr` carries: a verification condition then
mentions the exit assertion directly, and a jump that re-enters the text is
the business of `Program.cfg`, not of the walk. -/
@[spec low] theorem Program.cons_spec (i : Instr) :
    ⦃ fun s => WP.wp (Directive.instr i) (fun _ => WP.wp p Q E) E s ⦄
      (Directive.instr i :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    show Program.wpOpen (Directive.instr i :: p) (Q ())
      (Program.exitsTo (Directive.instr i :: p) (Q ()) E) s
    rw [Program.exitsTo_cons_instr]
    exact Directive.wp_mono (fun _ h => h) (fun l s' he => Or.inl he) h

@[spec] theorem Directive.label_spec (l : Label) :
    ⦃ fun s => Q () s ⦄ (Directive.label l) ⦃ Q; E ⦄ :=
  Triple.intro fun _ h => by
    intro labels rco
    wp_step
    exact h

@[spec] theorem Directive.nop_spec (asz osz : Width) (n : Nat) :
    ⦃ fun s => Q () s ⦄ (Directive.instr (.regular asz osz (.nop n))) ⦃ Q; E ⦄ :=
  Triple.intro fun _ h => by
    intro labels rco
    wp_step
    exact h

@[spec] theorem Directive.mov_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 r (BitVec.setWidth 64 i.toBitVec) } ⦄
      (Directive.instr (.regular asz .W64 (.mov (.reg (.low r .W64)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ h => by
    intro labels rco
    wp_step
    exact h

@[spec] theorem Directive.sub_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let b := s.regs.get64 r
        let a := BitVec.setWidth 64 i.toBitVec
        let v := b - a
        Q () { s with
                regs := s.regs.set64 r v,
                status := StatusFlags.from_result v
                  { cf := v.unsigned != b.unsigned - a.unsigned,
                    af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                    of := v.signed != b.signed - a.signed } } ⦄
      (Directive.instr (.regular asz .W64 (.sub (.reg (.low r .W64)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ h => by
    intro labels rco
    wp_step
    exact h

@[spec] theorem Directive.add_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := BitVec.setWidth 64 i.toBitVec
        let b := s.regs.get64 r
        let v := a + b
        Q () { s with
                regs := s.regs.set64 r v,
                status := StatusFlags.from_result v
                  { cf := v.unsigned != a.unsigned + b.unsigned,
                    af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                    of := v.signed != a.signed + b.signed } } ⦄
      (Directive.instr (.regular asz .W64 (.add (.reg (.low r .W64)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ h => by
    intro labels rco
    wp_step
    exact h

@[spec] theorem Directive.adc_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 rs
        let b := s.regs.get64 rd
        let c := s.status.cf
        let v := a + b + BitVec.ofNat 64 c.toNat
        Q () { s with
                regs := s.regs.set64 rd v,
                status := StatusFlags.from_result v
                  { cf := v.unsigned != a.unsigned + b.unsigned + c,
                    af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned + c,
                    of := v.signed != a.signed + b.signed + c } } ⦄
      (Directive.instr (.regular asz .W64
          (.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ h => by
    intro labels rco
    wp_step
    exact h

@[spec] theorem Directive.mulx_reg_spec (asz : Width) (hi lo rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rs).unsigned * (s.regs.get64 .rdx).unsigned
        Q () { s with regs :=
                (s.regs.set64 lo (BitVec.ofInt 64 v)).set64 hi (BitVec.ofInt 64 (v >>> 64)) } ⦄
      (Directive.instr (.regular asz .W64
          (.mulx (.low hi .W64) (.low lo .W64) (.reg (.low rs .W64)))))
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ h => by
    intro labels rco
    wp_step
    exact h

@[spec] theorem Directive.jcc_spec (asz osz : Width) (cc : CondCode) (l : Label) :
    ⦃ fun s =>
        (cc.interp s.status = true → E l s)
          ⊓ (cc.interp s.status = false → Q () s) ⦄
      (Directive.instr (.regular asz osz (.jcc cc l)))
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro labels rco
    wp_step
    cases hc : CondCode.interp cc s.status <;>
      simp only [hc, Bool.false_eq_true, if_true, if_false, meet_prop_eq_and,
        Effects.All, or_false, false_or] at h ⊢
    · exact h.2 trivial
    · exact ⟨l, rfl, rfl, h.1 trivial⟩

@[spec] theorem Directive.jmp_label_spec (asz osz : Width) (l : Label) :
    ⦃ fun s => E l s ⦄
      (Directive.instr (.regular asz osz
          (.jmp (.rel (.sub (.label l) .after_current_instruction)))))
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro labels rco
    obtain ⟨lo, hi⟩ := rco
    wp_step
    have hcancel : hi + (labels.label l - hi) = labels.label l := by
      apply Int64.toBitVec_inj.mp
      simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    simp only [hcancel]
    exact ⟨l, rfl, rfl, h⟩

/-! ### Basic blocks and the control-flow rule

`Program.view` cuts the text at its label cells; `Program.blockAt` is the
partial map from a label to its block: the label-free body there, and the
label of the block that follows. `Program.cfg` verifies the whole program
from one spec table `T` and one variant `var`: one triple per block, where an
exit to a textually later block is free and only a back edge must decrease
the variant. -/

/-- The labels of the text, in order. -/
def Program.labels : Program → List Label
  | [] => []
  | .label l :: p => l :: Program.labels p
  | _ :: p => Program.labels p

theorem Program.labels_append (a b : Program) :
    Program.labels (a ++ b) = Program.labels a ++ Program.labels b := by
  induction a with
  | nil => rfl
  | cons d t ih =>
    cases d with
    | label l => simp only [List.cons_append, Program.labels, ih]
    | instr i => exact ih
    | byteArray a' => exact ih

theorem Program.mem_labels_of_cell {t : Program} {l : Label}
    (h : Directive.label l ∈ t) : l ∈ Program.labels t := by
  induction t with
  | nil => cases h
  | cons d t ih =>
    rcases List.mem_cons.mp h with heq | hmem
    · rw [← heq]
      exact List.mem_cons_self
    · cases d with
      | label l' => exact List.mem_cons_of_mem _ (ih hmem)
      | instr i => exact ih hmem
      | byteArray a => exact ih hmem

/-- A nonempty scope suffix starts with its own label cell. -/
theorem Program.fromLabel_head :
    ∀ (p : Program) {l : Label}, Program.fromLabel p l ≠ [] →
      ∃ rest, Program.fromLabel p l = Directive.label l :: rest := by
  intro p
  induction p with
  | nil => intro l h; exact absurd rfl h
  | cons d p ih =>
    intro l h
    rw [Program.fromLabel_cons] at h ⊢
    by_cases hc : Program.fromLabel p l = [] ∧ d = Directive.label l
    · rw [if_pos hc]
      exact ⟨p, by rw [hc.2]⟩
    · rw [if_neg hc] at h ⊢
      exact ih h

/-- On a label-free fragment the dispatch closes nothing, and the closed wp
comes back to the open one. -/
theorem Program.wpOpen_of_wpClosed {b : Program} (hb : ∀ lx, Program.fromLabel b lx = [])
    {Q : MachineData → Prop} {E : Label → MachineData → Prop} {s : MachineData}
    (h : Program.wpClosed b Q E s) : Program.wpOpen b Q E s :=
  Program.wpOpen_mono (fun _ h => h)
    (fun lx _sx hx => hx.elim id (fun ⟨hm, _⟩ => absurd (hb lx) hm)) b s h

/-- A label present in the text has a scope suffix. -/
theorem Program.fromLabel_ne_nil_of_mem {p : Program} {l : Label}
    (h : l ∈ Program.labels p) : Program.fromLabel p l ≠ [] := by
  induction p with
  | nil => cases h
  | cons d p ih =>
    cases d with
    | label l' =>
      rw [Program.fromLabel_cons]
      split
      · exact List.cons_ne_nil _ _
      · rename_i hc
        simp only [Program.labels, List.mem_cons] at h
        rcases h with rfl | h
        · by_cases hnil : Program.fromLabel p l = []
          · exact absurd ⟨hnil, rfl⟩ hc
          · exact hnil
        · exact ih h
    | instr i =>
      rw [Program.fromLabel_cons_instr]
      exact ih h
    | byteArray a =>
      rw [Program.fromLabel_cons, if_neg (fun hc => by cases hc.2)]
      exact ih h

/-- A fragment with no label cell has no scope suffix. -/
theorem Program.fromLabel_eq_nil_of_free {b : Program}
    (hb : ∀ d ∈ b, d.isLabel = false) (l : Label) : Program.fromLabel b l = [] := by
  induction b with
  | nil => rfl
  | cons d bb ih =>
    have hd := hb d List.mem_cons_self
    have ih' := ih (fun d' hd' => hb d' (List.mem_cons_of_mem _ hd'))
    cases d with
    | label l' => simp [Directive.isLabel] at hd
    | instr i =>
      rw [Program.fromLabel_cons_instr]
      exact ih'
    | byteArray a =>
      rw [Program.fromLabel_cons, if_neg (fun hc => by cases hc.2)]
      exact ih'

private theorem idxOf_eq_of_getElem? {α} [BEq α] [LawfulBEq α] {xs : List α} {a : α}
    (hnd : xs.Nodup) : ∀ {i : Nat}, xs[i]? = some a → xs.idxOf a = i := by
  induction xs with
  | nil => intro i h; simp at h
  | cons x xs ih =>
    intro i h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      have hne : (x == a) = false := by
        have hmem : a ∈ xs := List.mem_of_getElem? h
        have hxa : x ≠ a := fun heq => (List.nodup_cons.mp hnd).1 (heq ▸ hmem)
        simpa using hxa
      simp only [List.idxOf_cons, hne, cond_false]
      rw [ih (List.nodup_cons.mp hnd).2 h]

/-! ### The block view

`Program.view` parses the text once: the label-free entry segment, then one
`(label, body)` pair per label cell, with label-free bodies. The block map and
the control-flow rule read this decomposition; `Program.fromLabel_view`
connects it to the scope suffixes the run semantics traverses. -/

/-- The block decomposition of the text. -/
def Program.view : Program → Program × List (Label × Program)
  | [] => ([], [])
  | .label l :: p => ([], (l, (Program.view p).1) :: (Program.view p).2)
  | d :: p => (d :: (Program.view p).1, (Program.view p).2)

/-- The glue of one block: its label cell, then its body. -/
abbrev Program.blockCells (lb : Label × Program) : Program :=
  Directive.label lb.1 :: lb.2

/-- The text is its entry segment followed by its labeled blocks. -/
theorem Program.view_eq (p : Program) :
    p = (Program.view p).1 ++ ((Program.view p).2.flatMap Program.blockCells) := by
  induction p with
  | nil => rfl
  | cons d p ih =>
    cases d with
    | label l =>
      simp only [Program.view, List.flatMap_cons, List.nil_append, List.cons_append,
        Program.blockCells]
      exact congrArg (Directive.label l :: ·) ih
    | instr i =>
      simp only [Program.view, List.cons_append]
      exact congrArg (Directive.instr i :: ·) ih
    | byteArray a =>
      simp only [Program.view, List.cons_append]
      exact congrArg (Directive.byteArray a :: ·) ih

/-- The entry segment and every body are label-free. -/
theorem Program.view_free (p : Program) :
    (∀ d ∈ (Program.view p).1, d.isLabel = false)
    ∧ ∀ lb ∈ (Program.view p).2, ∀ d ∈ lb.2, d.isLabel = false := by
  induction p with
  | nil => exact ⟨by simp [Program.view], by simp [Program.view]⟩
  | cons d p ih =>
    cases d with
    | label l =>
      refine ⟨by simp [Program.view], fun lb hlb => ?_⟩
      rcases List.mem_cons.mp hlb with heq | hmem
      · rw [heq]
        exact ih.1
      · exact ih.2 lb hmem
    | instr i =>
      refine ⟨fun d' hd' => ?_, ih.2⟩
      rcases List.mem_cons.mp hd' with heq | hmem
      · rw [heq]; rfl
      · exact ih.1 d' hmem
    | byteArray a =>
      refine ⟨fun d' hd' => ?_, ih.2⟩
      rcases List.mem_cons.mp hd' with heq | hmem
      · rw [heq]; rfl
      · exact ih.1 d' hmem

/-- The labels are the view's block labels, in order. -/
theorem Program.labels_view (p : Program) :
    Program.labels p = (Program.view p).2.map (·.1) := by
  induction p with
  | nil => rfl
  | cons d p ih =>
    cases d with
    | label l => simp only [Program.labels, Program.view, List.map_cons, ih]
    | instr i => exact ih
    | byteArray a => exact ih

/-- The scope suffix at a label, through the view: the blocks from the
label's position. -/
theorem Program.fromLabel_view {p : Program} (hnd : (Program.labels p).Nodup) :
    ∀ {i : Nat} {l : Label} {b : Program}, (Program.view p).2[i]? = some (l, b) →
      Program.fromLabel p l
        = ((Program.view p).2.drop i).flatMap Program.blockCells := by
  induction p with
  | nil => intro i l b hi; simp [Program.view] at hi
  | cons d p ih =>
    intro i l b hi
    cases d with
    | label l' =>
      simp only [Program.view] at hi
      simp only [Program.labels] at hnd
      have hnd' := (List.nodup_cons.mp hnd).2
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        have hnil : Program.fromLabel p l' = [] := by
          by_cases hne : Program.fromLabel p l' = []
          · exact hne
          · exact absurd (Program.mem_labels_of_cell (Program.fromLabel_mem hne))
              (List.nodup_cons.mp hnd).1
        rw [Program.fromLabel_cons, if_pos ⟨hnil, rfl⟩]
        simp only [Program.view, List.drop_zero, List.flatMap_cons, Program.blockCells,
          List.cons_append]
        exact congrArg (Directive.label l' :: ·) (Program.view_eq p)
      | succ j =>
        simp only [List.getElem?_cons_succ] at hi
        have hmem : l ∈ Program.labels p := by
          rw [Program.labels_view]
          exact List.mem_map.mpr ⟨(l, b), List.mem_of_getElem? hi, rfl⟩
        have hne : Program.fromLabel p l ≠ [] := Program.fromLabel_ne_nil_of_mem hmem
        rw [Program.fromLabel_cons, if_neg (fun hc => hne hc.1)]
        simp only [Program.view, List.drop_succ_cons]
        exact ih hnd' hi
    | instr i' =>
      simp only [Program.view] at hi
      rw [Program.fromLabel_cons_instr]
      simp only [Program.view]
      exact ih hnd hi
    | byteArray a =>
      simp only [Program.view] at hi
      rw [Program.fromLabel_cons, if_neg (fun hc => by cases hc.2)]
      simp only [Program.view]
      exact ih hnd hi

/-- A basic block: its label, its straight-line body, and the label it falls
into, when one follows. -/
structure Program.Block where
  label : Label
  body : Program
  next : Option Label
  deriving DecidableEq, Repr

def Program.blockAtAux : List (Label × Program) → Label → Option Program.Block
  | [], _ => none
  | (l', b) :: bs, l =>
    if l' = l then some ⟨l, b, bs.head?.map (·.1)⟩
    else Program.blockAtAux bs l

/-- The block of the text at label `l`: the partial map the control-flow rule
reads. -/
def Program.blockAt (p : Program) (l : Label) : Option Program.Block :=
  Program.blockAtAux (Program.view p).2 l

/-- The position of a label's block in the text. -/
def Program.blockIdx (p : Program) (l : Label) : Nat :=
  (Program.labels p).idxOf l

/-- What the block map found: the label's position in the view, its body
there, and the following label. -/
theorem Program.blockAtAux_spec : ∀ {bs : List (Label × Program)} {l : Label}
    {blk : Program.Block}, Program.blockAtAux bs l = some blk →
    blk.label = l ∧ ∃ i, bs[i]? = some (l, blk.body)
      ∧ blk.next = (bs[i + 1]?).map (·.1) := by
  intro bs
  induction bs with
  | nil => intro l blk h; cases h
  | cons lb bs ih =>
    intro l blk h
    obtain ⟨l', b⟩ := lb
    simp only [Program.blockAtAux] at h
    split at h
    · rename_i hc
      obtain rfl := Option.some.inj h
      subst hc
      refine ⟨rfl, 0, rfl, ?_⟩
      cases bs <;> rfl
    · obtain ⟨hlab, i, hi, hn⟩ := ih h
      exact ⟨hlab, i + 1, hi, hn⟩

/-- Under distinct labels the block map answers at every position of the
view. -/
theorem Program.blockAtAux_of_getElem : ∀ {bs : List (Label × Program)}
    (_ : (bs.map (·.1)).Nodup) {i : Nat} {l : Label} {b : Program},
    bs[i]? = some (l, b) →
    Program.blockAtAux bs l = some ⟨l, b, (bs[i + 1]?).map (·.1)⟩ := by
  intro bs
  induction bs with
  | nil => intro _ i l b h; simp at h
  | cons lb bs ih =>
    intro hnd i l b h
    obtain ⟨l', b'⟩ := lb
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Program.blockAtAux, if_pos rfl]
      congr 1
      cases bs <;> rfl
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      have hmem : l ∈ bs.map (·.1) :=
        List.mem_map.mpr ⟨(l, b), List.mem_of_getElem? h, rfl⟩
      have hne : l' ≠ l := fun heq =>
        (List.nodup_cons.mp (by simpa using hnd)).1 (heq ▸ hmem)
      simp only [Program.blockAtAux, if_neg hne, List.getElem?_cons_succ]
      exact ih (List.nodup_cons.mp (by simpa using hnd)).2 h

/-- A mapped label is in the text. -/
theorem Program.blockAt_mem_labels {p : Program} {l : Label} {blk : Program.Block}
    (h : Program.blockAt p l = some blk) : l ∈ Program.labels p := by
  obtain ⟨-, i, hi, -⟩ := Program.blockAtAux_spec h
  rw [Program.labels_view]
  exact List.mem_map.mpr ⟨(l, blk.body), List.mem_of_getElem? hi, rfl⟩

/-- Under distinct labels the block index is the label's position in the
view. -/
theorem Program.blockIdx_eq {p : Program} (hnd : (Program.labels p).Nodup)
    {i : Nat} {l : Label} {b : Program} (hi : (Program.view p).2[i]? = some (l, b)) :
    Program.blockIdx p l = i := by
  rw [Program.blockIdx]
  refine idxOf_eq_of_getElem? hnd ?_
  rw [Program.labels_view, List.getElem?_map, hi]
  rfl

/-- The blocks behind position `i`, glued back into text. -/
private theorem Program.drop_flatMap_cons {bs : List (Label × Program)} {i : Nat}
    {l : Label} {b : Program} (hi : bs[i]? = some (l, b)) :
    (bs.drop i).flatMap Program.blockCells
      = Directive.label l :: (b ++ (bs.drop (i + 1)).flatMap Program.blockCells) := by
  have hlt : i < bs.length := by
    by_cases h : i < bs.length
    · exact h
    · rw [List.getElem?_eq_none (by omega)] at hi; cases hi
  have hget : bs[i] = (l, b) := by
    have h1 := List.getElem?_eq_getElem hlt
    rw [hi] at h1
    exact (Option.some.inj h1.symm)
  rw [List.drop_eq_getElem_cons hlt, hget, List.flatMap_cons]
  simp only [Program.blockCells, List.cons_append]

/-- Wellformed text: the labels are unique. The condition is decidable, so
`by decide` closes `WF` for a concrete program. -/
structure Program.WF (p : Program) : Prop where
  nodup : (Program.labels p).Nodup

instance (p : Program) : Decidable (Program.WF p) :=
  decidable_of_iff ((Program.labels p).Nodup) ⟨fun h => ⟨h⟩, fun h => h.nodup⟩

/-- The split of the text at a present label: the fresh prefix, the label
cell, and the rest. -/
theorem Program.fromLabel_split {p : Program} {l : Label}
    (hnd : (Program.labels p).Nodup) (hne : Program.fromLabel p l ≠ []) :
    ∃ t rest, p = t ++ (Directive.label l :: rest)
      ∧ Program.fromLabel p l = Directive.label l :: rest
      ∧ l ∉ Program.labels t
      ∧ t.length = p.length - (Program.fromLabel p l).length := by
  obtain ⟨rest, hr⟩ := Program.fromLabel_head p hne
  obtain ⟨t, ht⟩ := Program.fromLabel_suffix p l
  refine ⟨t, rest, by rw [← ht, hr], hr, ?_, ?_⟩
  · intro hmem
    rw [← ht, Program.labels_append, hr] at hnd
    exact (List.nodup_append.mp hnd).2.2 l hmem l List.mem_cons_self rfl
  · have hlen := congrArg List.length ht
    simp only [List.length_append] at hlen
    omega

/-- The empty label context holds nowhere. -/
theorem Program.bot_elim {l : Label} {s : MachineData} {C : Prop}
    (h : (⊥ : Label → MachineData → Prop) l s) : C :=
  ((Lean.Order.bot_le (α := Label → MachineData → Prop) (fun _ _ => False)) l s h).elim

/-- The edge order of the control-flow rule, from a block entered at `l` with
the variant snapshot `n` to a jump target `l'`: the variant decreased, or it
is unchanged and the target sits later in the text. A forward edge is free
because the residual text shrinks; a back edge must decrease the variant. -/
abbrev Program.EdgeLt (p : Program) (var : Label → MachineData → Nat)
    (l : Label) (n : Nat) (l' : Label) (s : MachineData) : Prop :=
  var l' s < n ∨ (var l' s = n ∧ Program.blockIdx p l < Program.blockIdx p l')

/-- The control-flow rule: one spec table `T`, one variant `var`, one triple
per block of the map `Program.blockAt`. Each block is entered with its table
entry and the variant snapshotted; it falls into the next block with the entry
there and the variant not increased, and a jump exit lands on a mapped table
entry along `Program.EdgeLt`. The run never pauses: the label context of the
conclusion is `⊥`. The text starts with the entry label, and its labels are
distinct; both side conditions discharge themselves. -/
theorem Program.cfg {p p' : Program} {P : MachineData → Prop}
    {Q : Unit → MachineData → Prop} {l₀ : Label}
    (T : Label → MachineData → Prop) (var : Label → MachineData → Nat)
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => T l s ∧ var l s = n ⦄ blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T l' s ∧ var l' s ≤ n
         | none => Q);
        fun l' s => (Program.blockAt p l').isSome ∧ T l' s
          ∧ Program.EdgeLt p var l n l' s ⦄)
    (hp : p = Directive.label l₀ :: p' := by rfl)
    (hwf : Program.WF p := by decide)
    (hP : P = T l₀ := by rfl) :
    ⦃ P ⦄ p ⦃ Q ⦄ := by
  subst hP
  have hndl := hwf.nodup
  have hndv : ((Program.view p).2.map (·.1)).Nodup := by
    rwa [← Program.labels_view]
  have main : ∀ m : Nat, ∀ i l b, (Program.view p).2[i]? = some (l, b) → ∀ s, T l s →
      var l s * ((Program.view p).2.length + 1) + ((Program.view p).2.length - i) = m →
      Program.wpOpen (((Program.view p).2.drop i).flatMap Program.blockCells) (Q ())
        (Program.exitsTo p (Q ()) ⊥) s := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro i l b hi s hT hμ
      have hlt : i < (Program.view p).2.length := by
        by_cases h : i < (Program.view p).2.length
        · exact h
        · rw [List.getElem?_eq_none (by omega)] at hi; cases hi
      rw [Program.drop_flatMap_cons hi]
      intro labels rco
      wp_step
      rw [Program.wpOpen_append]
      have hblk : Program.blockAt p l
          = some ⟨l, b, ((Program.view p).2[i + 1]?).map (·.1)⟩ :=
        Program.blockAtAux_of_getElem hndv hi
      have hfree : ∀ d ∈ b, d.isLabel = false :=
        (Program.view_free p).2 (l, b) (List.mem_of_getElem? hi)
      have hidx : Program.blockIdx p l = i := Program.blockIdx_eq hndl hi
      have hb := Program.wpOpen_of_wpClosed
        (fun lx => Program.fromLabel_eq_nil_of_free hfree lx)
        ((hblocks l _ hblk (var l s)).le_wp s ⟨hT, rfl⟩)
      refine Program.wpOpen_mono (fun sx hq => ?_) (fun lx sx hx => ?_) _ _ hb
      · cases hnx : (Program.view p).2[i + 1]? with
        | none =>
          rw [hnx] at hq
          simp only [Option.map_none] at hq
          have hlen : (Program.view p).2.length ≤ i + 1 := by
            by_cases h : i + 1 < (Program.view p).2.length
            · rw [List.getElem?_eq_getElem h] at hnx; cases hnx
            · omega
          rw [List.drop_eq_nil_of_le hlen]
          exact hq
        | some lb' =>
          obtain ⟨l', b'⟩ := lb'
          rw [hnx] at hq
          simp only [Option.map_some] at hq
          refine ih _ ?_ (i + 1) l' b' hnx sx hq.1 rfl
          have hmul : var l' sx * ((Program.view p).2.length + 1)
              ≤ var l s * ((Program.view p).2.length + 1) :=
            Nat.mul_le_mul_right _ hq.2
          omega
      · obtain ⟨hsome, hT', hdec⟩ := hx
        obtain ⟨blk', hblk'⟩ := Option.isSome_iff_exists.mp hsome
        obtain ⟨hlab, i', hi', hnext'⟩ := Program.blockAtAux_spec hblk'
        have hlt' : i' < (Program.view p).2.length := by
          by_cases h : i' < (Program.view p).2.length
          · exact h
          · rw [List.getElem?_eq_none (by omega)] at hi'; cases hi'
        have hidx' : Program.blockIdx p lx = i' := Program.blockIdx_eq hndl hi'
        refine Or.inr ⟨?_, step_cps _ _ _ ?_⟩
        · rw [Program.fromLabel_view hndl hi', Program.drop_flatMap_cons hi']
          exact List.cons_ne_nil _ _
        · show Program.wpOpen (Program.fromLabel p lx) _ _ sx
          rw [Program.fromLabel_view hndl hi']
          refine ih _ ?_ i' lx blk'.body hi' sx hT' rfl
          rcases hdec with hv | ⟨hveq, hij⟩
          · have hmul : (var lx sx + 1) * ((Program.view p).2.length + 1)
                ≤ var l s * ((Program.view p).2.length + 1) :=
              Nat.mul_le_mul_right _ hv
            have hsucc : (var lx sx + 1) * ((Program.view p).2.length + 1)
                = var lx sx * ((Program.view p).2.length + 1)
                  + ((Program.view p).2.length + 1) := Nat.succ_mul _ _
            omega
          · rw [hidx, hidx'] at hij
            rw [hveq]
            omega
  refine Triple.intro fun s hT => ?_
  show Program.wpOpen p (Q ()) (Program.exitsTo p (Q ()) ⊥) s
  subst hp
  have h0 : (Program.view (Directive.label l₀ :: p')).2[0]?
      = some (l₀, (Program.view p').1) := rfl
  have hfl : ((Program.view (Directive.label l₀ :: p')).2.drop 0).flatMap Program.blockCells
      = Directive.label l₀ :: p' := by
    rw [List.drop_zero]
    simpa [Program.view] using (Program.view_eq (Directive.label l₀ :: p')).symm
  have h := main _ 0 l₀ _ h0 s hT rfl
  rwa [hfl] at h

set_option hygiene false in
/-- Split the control-flow obligations into one goal per block: enumerate the
labels, substitute each, and compute its block from the map. The bracket lists
the program's definitional unfoldings. -/
macro "cfg_cases" "[" ids:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    (intro l blk hblk n
     have hl := Program.blockAt_mem_labels hblk
     simp only [$ids,*, Program.labels, List.cons_append, List.nil_append,
       List.mem_cons, List.not_mem_nil, or_false] at hl
     repeat' first
       | (obtain rfl | hl := hl)
       | (obtain rfl := hl)
     all_goals
       simp only [$ids,*, Program.blockAt, Program.blockAtAux, Program.view,
         List.cons_append, List.nil_append, List.head?_cons, List.head?_nil,
         Option.map_some, Option.map_none, Option.some.injEq,
         String.reduceEq, eq_self_iff_true, and_true, true_and,
         and_false, false_and, if_true, if_false, reduceIte, reduceCtorEq] at hblk
     all_goals subst hblk
     all_goals dsimp only))

end ProgramSpecs
