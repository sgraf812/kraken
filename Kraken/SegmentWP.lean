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

`Program.blocks` cuts the text at its label cells: each block is straight-line
code up to its jumps, with the label that follows it, so every cell of the
program sits in exactly one block. `Program.cfg` verifies the whole program
from one spec table `T` and one variant `var`: one triple per block, where an
exit to a textually later label is free and only a back edge must decrease the
variant. -/

/-- The cells up to the next label. -/
def Program.blockBody : Program → Program
  | [] => []
  | .label _ :: _ => []
  | d :: p => d :: Program.blockBody p

/-- The label the block falls into, when one follows. -/
def Program.nextLabel : Program → Option Label
  | [] => none
  | .label l :: _ => some l
  | _ :: p => Program.nextLabel p

/-- A basic block: its label, its straight-line body, and the label it falls
into, when one follows. -/
structure Program.Block where
  label : Label
  body : Program
  next : Option Label
  deriving DecidableEq, Repr

/-- The labeled blocks of the text, in order. -/
def Program.blocks : Program → List Program.Block
  | [] => []
  | .label l :: p => ⟨l, Program.blockBody p, Program.nextLabel p⟩ :: Program.blocks p
  | _ :: p => Program.blocks p

/-- A block body carries no label cell. -/
theorem Program.blockBody_fromLabel (p : Program) (lx : Label) :
    Program.fromLabel (Program.blockBody p) lx = [] := by
  induction p with
  | nil => rfl
  | cons d p ih =>
    cases d <;> simp [Program.blockBody, Program.fromLabel_cons, ih]

/-- A label has a scope suffix exactly when it heads a block. -/
theorem Program.fromLabel_ne_nil_iff (p : Program) (l : Label) :
    Program.fromLabel p l ≠ [] ↔ l ∈ (Program.blocks p).map (·.label) := by
  induction p with
  | nil => simp [Program.blocks]
  | cons d p ih =>
    cases d with
    | label l₁ =>
      by_cases hl : l₁ = l
      · subst hl
        simp only [Program.blocks, List.map_cons, List.mem_cons, true_or, iff_true]
        rw [Program.fromLabel_cons]
        split
        · exact List.cons_ne_nil _ _
        · rename_i hcond
          by_cases hnil : Program.fromLabel p l₁ = []
          · exact absurd ⟨hnil, rfl⟩ hcond
          · exact hnil
      · rw [Program.fromLabel_cons, if_neg (by rintro ⟨-, h⟩; exact hl (Directive.label.inj h))]
        simp only [Program.blocks, List.map_cons, List.mem_cons]
        rw [ih]
        exact ⟨Or.inr, fun h => h.elim (fun h => absurd h.symm hl) id⟩
    | instr i =>
      rw [Program.fromLabel_cons, if_neg (by rintro ⟨-, h⟩; cases h)]
      simpa [Program.blocks] using ih
    | byteArray a =>
      rw [Program.fromLabel_cons, if_neg (by rintro ⟨-, h⟩; cases h)]
      simpa [Program.blocks] using ih

/-- A label with a scope suffix has a block. -/
theorem Program.block_of_fromLabel {p : Program} {l : Label}
    (h : Program.fromLabel p l ≠ []) :
    ∃ b next, Program.Block.mk l b next ∈ Program.blocks p := by
  obtain ⟨⟨l', b, next⟩, hmem, hfst⟩ :=
    List.mem_map.mp ((Program.fromLabel_ne_nil_iff p l).mp h)
  exact ⟨b, next, hfst ▸ hmem⟩

/-- The label a block falls into heads a block itself. -/
theorem Program.nextLabel_mem {p : Program} {l : Label}
    (h : Program.nextLabel p = some l) : l ∈ (Program.blocks p).map (·.label) := by
  induction p with
  | nil => cases h
  | cons d p ih =>
    cases d with
    | label l₁ =>
      simp only [Program.nextLabel] at h
      cases h
      simp [Program.blocks]
    | instr i => simpa [Program.blocks] using ih (by simpa [Program.nextLabel] using h)
    | byteArray a => simpa [Program.blocks] using ih (by simpa [Program.nextLabel] using h)

/-- Every block body is label-free. -/
theorem Program.blocks_body_fromLabel :
    ∀ (p : Program) {blk : Program.Block}, blk ∈ Program.blocks p →
      ∀ lx, Program.fromLabel blk.body lx = [] := by
  intro p
  induction p with
  | nil => intro _ h; cases h
  | cons d p ih =>
    intro blk hmem lx
    cases d with
    | label l₁ =>
      rcases List.mem_cons.mp hmem with heq | hmem'
      · rw [heq]
        exact Program.blockBody_fromLabel p lx
      · exact ih hmem' lx
    | instr i => exact ih hmem lx
    | byteArray a => exact ih hmem lx

/-- The label a block falls into heads a block. -/
theorem Program.blocks_next_mem :
    ∀ (p : Program) {l b l''}, Program.Block.mk l b (some l'') ∈ Program.blocks p →
      l'' ∈ (Program.blocks p).map (·.label) := by
  intro p
  induction p with
  | nil => intro _ _ _ h; cases h
  | cons d p ih =>
    intro l b l'' hmem
    cases d with
    | label l₁ =>
      rcases List.mem_cons.mp hmem with heq | hmem'
      · obtain ⟨-, -, hn⟩ :
            l = l₁ ∧ b = Program.blockBody p ∧ some l'' = Program.nextLabel p := by
          simpa [Program.Block.mk.injEq] using heq
        simp only [Program.blocks, List.map_cons, List.mem_cons]
        exact Or.inr (Program.nextLabel_mem hn.symm)
      · simp only [Program.blocks, List.map_cons, List.mem_cons]
        exact Or.inr (ih hmem')
    | instr i => exact ih hmem
    | byteArray a => exact ih hmem

/-- The text behind a block: the next label's scope suffix, or nothing. -/
def Program.tailOf (p : Program) : Option Label → Program
  | some l' => Program.fromLabel p l'
  | none => []

@[simp] theorem Program.tailOf_some (p : Program) (l' : Label) :
    Program.tailOf p (some l') = Program.fromLabel p l' := rfl

@[simp] theorem Program.tailOf_none (p : Program) :
    Program.tailOf p none = [] := rfl

/-- The text is its first block followed by the next label's scope suffix. -/
theorem Program.eq_blockBody_append :
    ∀ (p : Program), ((Program.blocks p).map (·.label)).Nodup →
      p = Program.blockBody p ++ Program.tailOf p (Program.nextLabel p) := by
  intro p
  induction p with
  | nil => intro _; rfl
  | cons d p ih =>
    intro hnd
    cases d with
    | label l₂ =>
      have hnotin : l₂ ∉ (Program.blocks p).map (·.1) := by
        simp only [Program.blocks, List.map_cons, List.nodup_cons] at hnd
        exact hnd.1
      have hnil : Program.fromLabel p l₂ = [] := by
        by_cases hne : Program.fromLabel p l₂ = []
        · exact hne
        · exact absurd ((Program.fromLabel_ne_nil_iff p l₂).mp hne) hnotin
      simp only [Program.blockBody, Program.nextLabel, List.nil_append, Program.tailOf]
      rw [Program.fromLabel_cons, if_pos ⟨hnil, rfl⟩]
    | instr i =>
      have hih := ih hnd
      simp only [Program.blockBody, Program.nextLabel, List.cons_append]
      congr 1
      cases hnl : Program.nextLabel p with
      | none => simpa [hnl, Program.tailOf] using hih
      | some l' =>
        simp only [hnl, Program.tailOf] at hih ⊢
        rw [Program.fromLabel_cons, if_neg (by rintro ⟨-, h⟩; cases h)]
        exact hih
    | byteArray a =>
      have hih := ih hnd
      simp only [Program.blockBody, Program.nextLabel, List.cons_append]
      congr 1
      cases hnl : Program.nextLabel p with
      | none => simpa [hnl, Program.tailOf] using hih
      | some l' =>
        simp only [hnl, Program.tailOf] at hih ⊢
        rw [Program.fromLabel_cons, if_neg (by rintro ⟨-, h⟩; cases h)]
        exact hih

/-- A block's scope suffix: its label cell, its body, and the next label's
scope suffix. -/
theorem Program.fromLabel_block :
    ∀ (p : Program), ((Program.blocks p).map (·.label)).Nodup →
      ∀ {l b next}, Program.Block.mk l b next ∈ Program.blocks p →
      Program.fromLabel p l = Directive.label l :: (b ++ Program.tailOf p next) := by
  intro p
  induction p with
  | nil => intro _ _ _ _ h; cases h
  | cons d p ih =>
    intro hnd l b next hmem
    cases d with
    | label l₁ =>
      have hnd' := hnd
      simp only [Program.blocks, List.map_cons, List.nodup_cons] at hnd'
      obtain ⟨hnotin, hndp⟩ := hnd'
      rcases List.mem_cons.mp hmem with heq | hmem'
      · obtain ⟨rfl, rfl, rfl⟩ :
            l = l₁ ∧ b = Program.blockBody p ∧ next = Program.nextLabel p := by
          simpa [Program.Block.mk.injEq] using heq
        have hnil : Program.fromLabel p l = [] := by
          by_cases hne : Program.fromLabel p l = []
          · exact hne
          · exact absurd ((Program.fromLabel_ne_nil_iff p l).mp hne) hnotin
        rw [Program.fromLabel_cons, if_pos ⟨hnil, rfl⟩]
        congr 1
        have hbase := Program.eq_blockBody_append p hndp
        cases hnl : Program.nextLabel p with
        | none => simpa [hnl, Program.tailOf] using hbase
        | some l' =>
          have hl' := Program.nextLabel_mem hnl
          have hne' : Program.fromLabel p l' ≠ [] :=
            (Program.fromLabel_ne_nil_iff p l').mpr hl'
          simp only [hnl, Program.tailOf] at hbase ⊢
          rw [Program.fromLabel_cons, if_neg (by rintro ⟨hn, -⟩; exact hne' hn)]
          exact hbase
      · have hlmem : l ∈ (Program.blocks p).map (·.1) := List.mem_map.mpr ⟨_, hmem', rfl⟩
        have hlne : Program.fromLabel p l ≠ [] :=
          (Program.fromLabel_ne_nil_iff p l).mpr hlmem
        rw [Program.fromLabel_cons, if_neg (by rintro ⟨hn, -⟩; exact hlne hn)]
        have hih := ih hndp hmem'
        cases hnx : next with
        | none => simpa [hnx, Program.tailOf] using hih
        | some l'' =>
          have hl'' := Program.blocks_next_mem p (hnx ▸ hmem')
          have hne'' : Program.fromLabel p l'' ≠ [] :=
            (Program.fromLabel_ne_nil_iff p l'').mpr hl''
          simp only [hnx, Program.tailOf] at hih ⊢
          rw [Program.fromLabel_cons, if_neg (by rintro ⟨hn, -⟩; exact hne'' hn)]
          exact hih
    | instr i =>
      have hih := ih hnd hmem
      rw [Program.fromLabel_cons,
        if_neg (by rintro ⟨-, h⟩; cases h)]
      cases hnx : next with
      | none => simpa [hnx, Program.tailOf] using hih
      | some l'' =>
        have hl'' := Program.blocks_next_mem p (hnx ▸ hmem)
        have hne'' : Program.fromLabel p l'' ≠ [] :=
          (Program.fromLabel_ne_nil_iff p l'').mpr hl''
        simp only [hnx, Program.tailOf] at hih ⊢
        rw [Program.fromLabel_cons, if_neg (by rintro ⟨hn, -⟩; exact hne'' hn)]
        exact hih
    | byteArray a =>
      have hih := ih hnd hmem
      rw [Program.fromLabel_cons,
        if_neg (by rintro ⟨-, h⟩; cases h)]
      cases hnx : next with
      | none => simpa [hnx, Program.tailOf] using hih
      | some l'' =>
        have hl'' := Program.blocks_next_mem p (hnx ▸ hmem)
        have hne'' : Program.fromLabel p l'' ≠ [] :=
          (Program.fromLabel_ne_nil_iff p l'').mpr hl''
        simp only [hnx, Program.tailOf] at hih ⊢
        rw [Program.fromLabel_cons, if_neg (by rintro ⟨hn, -⟩; exact hne'' hn)]
        exact hih

/-- On a label-free fragment the dispatch closes nothing, and the closed wp
comes back to the open one. -/
theorem Program.wpOpen_of_wpClosed {b : Program} (hb : ∀ lx, Program.fromLabel b lx = [])
    {Q : MachineData → Prop} {E : Label → MachineData → Prop} {s : MachineData}
    (h : Program.wpClosed b Q E s) : Program.wpOpen b Q E s :=
  Program.wpOpen_mono (fun _ h => h)
    (fun lx _sx hx => hx.elim id (fun ⟨hm, _⟩ => absurd (hb lx) hm)) b s h

/-- The block of the text at label `l`: the partial map the control-flow rule
reads. Lookup follows `Program.fromLabel`, so a re-declared label denotes its
last block. -/
def Program.blockAt (p : Program) (l : Label) : Option Program.Block :=
  match Program.fromLabel p l with
  | .label _ :: rest => some ⟨l, Program.blockBody rest, Program.nextLabel rest⟩
  | _ => none

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

/-- A label-free prefix contributes itself to the block body. -/
theorem Program.blockBody_append {b tail : Program}
    (hb : ∀ lx, Program.fromLabel b lx = [])
    (htail : tail = [] ∨ ∃ l' t, tail = Directive.label l' :: t) :
    Program.blockBody (b ++ tail) = b := by
  induction b with
  | nil => rcases htail with rfl | ⟨l', t, rfl⟩ <;> simp [Program.blockBody]
  | cons d bb ih =>
    have hb' : ∀ lx, Program.fromLabel bb lx = [] := by
      intro lx
      have h := hb lx
      rw [Program.fromLabel_cons] at h
      by_cases hc : Program.fromLabel bb lx = [] ∧ d = Directive.label lx
      · exact hc.1
      · rwa [if_neg hc] at h
    have hd : ∀ lx, d ≠ Directive.label lx := by
      intro lx hdl
      have h := hb lx
      rw [Program.fromLabel_cons, if_pos ⟨hb' lx, hdl⟩] at h
      exact absurd h (List.cons_ne_nil _ _)
    cases d with
    | label lx => exact absurd rfl (hd lx)
    | instr i => simp only [List.cons_append, Program.blockBody, ih hb']
    | byteArray a => simp only [List.cons_append, Program.blockBody, ih hb']

/-- A label-free prefix is invisible to the next label. -/
theorem Program.nextLabel_append {b tail : Program}
    (hb : ∀ lx, Program.fromLabel b lx = []) :
    Program.nextLabel (b ++ tail) = Program.nextLabel tail := by
  induction b with
  | nil => rfl
  | cons d bb ih =>
    have hb' : ∀ lx, Program.fromLabel bb lx = [] := by
      intro lx
      have h := hb lx
      rw [Program.fromLabel_cons] at h
      by_cases hc : Program.fromLabel bb lx = [] ∧ d = Directive.label lx
      · exact hc.1
      · rwa [if_neg hc] at h
    have hd : ∀ lx, d ≠ Directive.label lx := by
      intro lx hdl
      have h := hb lx
      rw [Program.fromLabel_cons, if_pos ⟨hb' lx, hdl⟩] at h
      exact absurd h (List.cons_ne_nil _ _)
    cases d with
    | label lx => exact absurd rfl (hd lx)
    | instr i => simp only [List.cons_append, Program.nextLabel, ih hb']
    | byteArray a => simp only [List.cons_append, Program.nextLabel, ih hb']

/-- The tail behind a block is empty or a label-led suffix. -/
private theorem Program.tail_shape {p : Program} :
    ∀ (next : Option Label), (∀ l', next = some l' → Program.fromLabel p l' ≠ []) →
      Program.tailOf p next = [] ∨ ∃ l' t, Program.tailOf p next = Directive.label l' :: t
  | none, _ => Or.inl rfl
  | some l', h => by
      obtain ⟨t, ht⟩ := Program.fromLabel_head p (h l' rfl)
      exact Or.inr ⟨l', t, by rw [Program.tailOf_some]; exact ht⟩

/-- The tail behind a block starts with the block's next label. -/
private theorem Program.nextLabel_tail {p : Program} :
    ∀ (next : Option Label), (∀ l', next = some l' → Program.fromLabel p l' ≠ []) →
      Program.nextLabel (Program.tailOf p next) = next
  | none, _ => rfl
  | some l', h => by
      obtain ⟨t, ht⟩ := Program.fromLabel_head p (h l' rfl)
      rw [Program.tailOf_some, ht]
      rfl

/-- The scope suffix at `l`, seen through the block map: the label cell, the
block's body, and the next label's scope suffix. -/
theorem Program.blockAt_decomp {p : Program}
    (hnd : ((Program.blocks p).map (·.label)).Nodup)
    {l : Label} {blk : Program.Block} (h : Program.blockAt p l = some blk) :
    Program.fromLabel p l = Directive.label l :: (blk.body ++ Program.tailOf p blk.next) := by
  have hne : Program.fromLabel p l ≠ [] := by
    intro hnil
    rw [Program.blockAt, hnil] at h
    cases h
  obtain ⟨b, next, hmem⟩ := Program.block_of_fromLabel hne
  have hself := Program.fromLabel_block p hnd hmem
  have hbfree := Program.blocks_body_fromLabel p hmem
  have hnexts : ∀ l', next = some l' → Program.fromLabel p l' ≠ [] := fun l' hnx =>
    (Program.fromLabel_ne_nil_iff p l').mpr (Program.blocks_next_mem p (hnx ▸ hmem))
  obtain ⟨rest, hrest⟩ := Program.fromLabel_head p hne
  have hrb : rest = b ++ Program.tailOf p next := by
    have h2 := hrest.symm.trans hself
    exact (List.cons.inj h2).2
  rw [Program.blockAt, hrest] at h
  have hblk := Option.some.inj h
  have hbody : Program.blockBody rest = b := by
    rw [hrb]
    exact Program.blockBody_append hbfree (Program.tail_shape next hnexts)
  have hnext : Program.nextLabel rest = next := by
    rw [hrb, Program.nextLabel_append hbfree]
    exact Program.nextLabel_tail next hnexts
  rw [← hblk]
  simp only [hbody, hnext]
  exact hself

/-- A scope suffix's blocks sit inside the host's blocks. -/
theorem Program.blocks_suffix : ∀ {q p : Program}, q <:+ p →
    Program.blocks q <:+ Program.blocks p := by
  intro q p h
  induction p with
  | nil =>
    rw [List.suffix_nil.mp h]
    exact List.suffix_rfl
  | cons d p ih =>
    rcases List.suffix_cons_iff.mp h with heq | h'
    · rw [heq]
      exact List.suffix_rfl
    · have hs := ih h'
      cases d with
      | label l₁ => exact hs.trans (List.suffix_cons _ _)
      | instr i => exact hs
      | byteArray a => exact hs

/-- A label has a block exactly when it is in the text. -/
theorem Program.blockAt_isSome_iff (p : Program) (l : Label) :
    (Program.blockAt p l).isSome ↔ Program.fromLabel p l ≠ [] := by
  constructor
  · intro h hnil
    rw [Program.blockAt, hnil] at h
    cases h
  · intro hne
    obtain ⟨rest, hr⟩ := Program.fromLabel_head p hne
    rw [Program.blockAt, hr]
    rfl

/-- A label in the text has a block. -/
theorem Program.blockAt_isSome {p : Program} {l : Label}
    (h : Program.fromLabel p l ≠ []) : ∃ blk, Program.blockAt p l = some blk := by
  obtain ⟨rest, hr⟩ := Program.fromLabel_head p h
  exact ⟨_, by rw [Program.blockAt, hr]⟩

/-- A label with a block is in the text. -/
theorem Program.blockAt_ne {p : Program} {l : Label} {blk : Program.Block}
    (h : Program.blockAt p l = some blk) : Program.fromLabel p l ≠ [] := by
  intro hnil
  rw [Program.blockAt, hnil] at h
  cases h

/-- A block's body is label-free. -/
theorem Program.blockAt_body_free {p : Program} {l : Label} {blk : Program.Block}
    (h : Program.blockAt p l = some blk) :
    ∀ lx, Program.fromLabel blk.body lx = [] := by
  rw [Program.blockAt] at h
  split at h
  · cases h
    exact fun lx => Program.blockBody_fromLabel _ lx
  · cases h

/-- The label a block falls into is in the text. -/
theorem Program.blockAt_next_ne {p : Program} {l : Label} {blk : Program.Block} {l' : Label}
    (h : Program.blockAt p l = some blk) (hn : blk.next = some l') :
    Program.fromLabel p l' ≠ [] := by
  rw [Program.blockAt] at h
  split at h
  · rename_i rest heq
    cases h
    simp only at hn
    have hmem := Program.nextLabel_mem hn
    have hsub : Program.blocks rest <:+ Program.blocks p := by
      refine Program.blocks_suffix ?_
      have := Program.fromLabel_suffix p l
      rw [heq] at this
      exact (List.suffix_cons _ _).trans this
    exact (Program.fromLabel_ne_nil_iff p l').mpr
      ((hsub.sublist.map (·.label)).subset hmem)
  · cases h

/-- The labels of the text, in order. -/
def Program.labels : Program → List Label
  | [] => []
  | .label l :: p => l :: Program.labels p
  | _ :: p => Program.labels p

/-- The labels are the block labels. -/
theorem Program.labels_eq_blocks (p : Program) :
    Program.labels p = (Program.blocks p).map (·.label) := by
  induction p with
  | nil => rfl
  | cons d p ih =>
    cases d with
    | label l => simp only [Program.labels, Program.blocks, List.map_cons, ih]
    | instr i => exact ih
    | byteArray a => exact ih

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
  var l' s < n ∨ (var l' s = n ∧
    (Program.fromLabel p l').length < (Program.fromLabel p l).length)

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
  have hnd := hwf.nodup
  rw [Program.labels_eq_blocks] at hnd
  have main : ∀ m : Nat, ∀ l blk, Program.blockAt p l = some blk → ∀ s, T l s →
      var l s * (p.length + 1) + (Program.fromLabel p l).length = m →
      Program.wpOpen (Program.fromLabel p l) (Q ())
        (Program.exitsTo p (Q ()) ⊥) s := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro l blk hblk s hT hμ
      have hself := Program.blockAt_decomp hnd hblk
      rw [hself]
      intro labels rco
      wp_step
      rw [Program.wpOpen_append]
      have hb := Program.wpOpen_of_wpClosed (Program.blockAt_body_free hblk)
        ((hblocks l blk hblk (var l s)).le_wp s ⟨hT, rfl⟩)
      refine Program.wpOpen_mono (fun sx hq => ?_) (fun lx sx hx => ?_) _ _ hb
      · cases hnx : blk.next with
        | some l' =>
          rw [hnx] at hq hself
          have hne' := Program.blockAt_next_ne hblk hnx
          obtain ⟨blk', hblk'⟩ := Program.blockAt_isSome hne'
          have hlt : (Program.fromLabel p l').length < (Program.fromLabel p l).length := by
            rw [hself]
            simp only [Program.tailOf, List.length_cons, List.length_append]
            omega
          have hmono : var l' sx * (p.length + 1) ≤ var l s * (p.length + 1) :=
            Nat.mul_le_mul_right _ hq.2
          refine ih _ ?_ l' blk' hblk' sx hq.1 rfl
          calc var l' sx * (p.length + 1) + (Program.fromLabel p l').length
              < var l' sx * (p.length + 1) + (Program.fromLabel p l).length :=
                Nat.add_lt_add_left hlt _
            _ ≤ var l s * (p.length + 1) + (Program.fromLabel p l).length :=
                Nat.add_le_add_right hmono _
            _ = m := hμ
        | none =>
          simp only [hnx] at hq
          exact hq
      · obtain ⟨hsome, hT', hdec⟩ := hx
        obtain ⟨blk'', hblk''⟩ := Option.isSome_iff_exists.mp hsome
        have hne' := Program.blockAt_ne hblk''
        refine Or.inr ⟨hne', step_cps _ _ _ ?_⟩
        show Program.wpOpen (Program.fromLabel p lx) _ _ sx
        refine ih _ ?_ lx blk'' hblk'' sx hT' rfl
        have hlen : (Program.fromLabel p lx).length ≤ p.length :=
          (Program.fromLabel_suffix p lx).length_le
        rcases hdec with hlt | ⟨heq, hlenlt⟩
        · have hmono : (var lx sx + 1) * (p.length + 1) ≤ var l s * (p.length + 1) :=
            Nat.mul_le_mul_right _ hlt
          calc var lx sx * (p.length + 1) + (Program.fromLabel p lx).length
              ≤ var lx sx * (p.length + 1) + p.length := Nat.add_le_add_left hlen _
            _ < (var lx sx + 1) * (p.length + 1) := by
                rw [Nat.succ_mul]
                exact Nat.add_lt_add_left (Nat.lt_succ_of_le (Nat.le_refl _)) _
            _ ≤ var l s * (p.length + 1) := hmono
            _ ≤ var l s * (p.length + 1) + (Program.fromLabel p l).length :=
                Nat.le_add_right _ _
            _ = m := hμ
        · rw [heq]
          calc var l s * (p.length + 1) + (Program.fromLabel p lx).length
              < var l s * (p.length + 1) + (Program.fromLabel p l).length :=
                Nat.add_lt_add_left hlenlt _
            _ = m := hμ
  have hnd' := hnd
  rw [hp] at hnd'
  simp only [Program.blocks, List.map_cons, List.nodup_cons] at hnd'
  have hnil₀ : Program.fromLabel p' l₀ = [] := by
    by_cases hne : Program.fromLabel p' l₀ = []
    · exact hne
    · exact absurd ((Program.fromLabel_ne_nil_iff p' l₀).mp hne) hnd'.1
  have hfl₀ : Program.fromLabel p l₀ = p := by
    rw [hp, Program.fromLabel_cons, if_pos ⟨hnil₀, rfl⟩]
  obtain ⟨blk₀, hblk₀⟩ := Program.blockAt_isSome (p := p) (l := l₀) (by rw [hfl₀, hp]; exact List.cons_ne_nil _ _)
  refine Triple.intro fun s hT => ?_
  have h := main _ l₀ blk₀ hblk₀ s hT rfl
  rwa [hfl₀] at h

set_option hygiene false in
/-- Split the control-flow obligations into one goal per block: enumerate the
labels, substitute each, and compute its block from the map. The bracket lists
the program's definitional unfoldings. -/
macro "cfg_cases" "[" ids:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    (intro l blk hblk n
     have hl := (Program.fromLabel_ne_nil_iff _ l).mp (Program.blockAt_ne hblk)
     simp only [$ids,*, Program.blocks, Program.blockBody, Program.nextLabel,
       List.cons_append, List.nil_append, List.map_cons, List.map_nil,
       List.mem_cons, List.not_mem_nil, or_false] at hl
     repeat' first
       | (obtain rfl | hl := hl)
       | (obtain rfl := hl)
     all_goals
       simp only [$ids,*, Program.blockAt, Program.fromLabel_cons,
         Program.fromLabel_nil, Program.blockBody, Program.nextLabel,
         List.cons_append, List.nil_append, Option.some.injEq,
         Directive.label.injEq, String.reduceEq, eq_self_iff_true,
         and_true, true_and, and_false, false_and, if_true, if_false,
         reduceIte, reduceCtorEq] at hblk
     all_goals subst hblk
     all_goals dsimp only))

end ProgramSpecs
