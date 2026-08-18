/-
The machine-founded weakest precondition. `Executable.wp` is defined by the
baseline interpreter: a fragment `q`, placed anywhere in the ambient code,
runs its cells and every stop lands in the fall-through postcondition at the
placement's end, or in the exit channel at the pc it stopped at. Exits are
pc values: `E : Int64 → MachineData → Prop`. A label exit is
`E (cenv.labels.label l)`; a computed exit is `E` at the value.

`CodeEnv` binds the ambient code once, together with the one wellformedness
fact the rules consume: the segment map advances cell by cell.
-/
import Kraken.SegmentExtract

open Std.Internal.Do
open Lean.Order

/-! ## The ambient code -/

/-- The ambient executable, with the placement-advance fact: behind the cell
at `pc` the segment map continues at `pc + size`. -/
class CodeEnv where
  env : Executable
  advance : ∀ (pc : Int64) (c : Directive × Nat) (t : List (Directive × Nat)),
    env.directivesFromAddress pc = c :: t →
    env.directivesFromAddress (pc + .ofNat c.2) = t

/-- The ambient code. -/
abbrev cenv [CodeEnv] : Executable := CodeEnv.env

private theorem int64_ofNat_add (a b : Nat) :
    Int64.ofNat (a + b) = Int64.ofNat a + Int64.ofNat b := by
  apply Int64.toBitVec_inj.mp
  simp

/-! ## The step relation and the wp

`instrStep` runs exactly the cell at the current pc: the machine's own
interpreter, with the fall-through and jump continuations both stopping. It
refines kraken's `straightlineStep`, which runs a whole segment burst, into
the granularity the per-instruction rules need. -/

/-- One cell of the ambient code, run from `st`. -/
def Executable.instrStep (e : Executable) (st : MachineState) (post : @Post MachineState) :
    Prop :=
  ∃ d z rest, e.directivesFromAddress st.2 = (d, z) :: rest ∧
    (@Directive.interp e.labels d st.1 (.mk st.2 (st.2 + .ofNat z))
      (fun s' => .done (s', st.2 + .ofNat z)) (fun pc' s' => .done (s', pc'))).All post

/-- The address behind the fragment `q` placed at `pc`: the entry, advanced
by the sizes the ambient code gives those cells. -/
def Executable.after (e : Executable) (pc : Int64) (q : Program) : Int64 :=
  pc + .ofNat ((((e.directivesFromAddress pc).take q.length).map Prod.snd).sum)

/-- The text at `pc` begins with `q`. -/
def Executable.sits (e : Executable) (pc : Int64) (q : Program) : Prop :=
  (((e.directivesFromAddress pc).take q.length).map Prod.fst) = q

/-- `q` sits at `pc`, and the text behind it starts at `pcEnd`. -/
def Executable.holds (e : Executable) (pc : Int64) (q : Program) (pcEnd : Int64) : Prop :=
  ∃ sized rest, e.directivesFromAddress pc = sized ++ rest
    ∧ sized.map Prod.fst = q
    ∧ pcEnd = pc + .ofNat ((sized.map Prod.snd).sum)

theorem Executable.holds_of_sits {e : Executable} {pc : Int64} {q : Program}
    (h : e.sits pc q) : e.holds pc q (e.after pc q) :=
  ⟨(e.directivesFromAddress pc).take q.length, (e.directivesFromAddress pc).drop q.length,
    (List.take_append_drop _ _).symm, h, rfl⟩

/-- The run of the fragment `q` from `s`: placed anywhere in the ambient
code, the machine eventually falls through to the placement's end with `Q`,
or stops at a pc satisfying `E`. Re-entry inside the fragment is free: the
judgment is the fixpoint `Eventually`, so a back edge simply keeps stepping. -/
def Executable.wp (e : Executable) (q : Program) (Q : MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) : Prop :=
  ∀ (pc pcEnd : Int64), e.holds pc q pcEnd →
    Eventually (e.instrStep)
      (fun st => (st.2 = pcEnd ∧ Q st.1) ∨ E st.2 st.1) (s, pc)

theorem Executable.wp_mono {e : Executable} {q : Program}
    {Q₁ Q₂ : MachineData → Prop} {E₁ E₂ : Int64 → MachineData → Prop}
    (hQ : ∀ s, Q₁ s → Q₂ s) (hE : ∀ a s, E₁ a s → E₂ a s)
    {s : MachineData} (h : e.wp q Q₁ E₁ s) : e.wp q Q₂ E₂ s := fun pc pcEnd hpl =>
  (h pc pcEnd hpl).mono (fun _ _ ht => ht)
    (fun st hst => hst.imp (fun ⟨ha, hq⟩ => ⟨ha, hQ _ hq⟩) (hE _ _))

namespace MachineWP

/-- A triple on a program is the machine-founded wp of the ambient code. -/
scoped instance instWP [CodeEnv] :
    WP Program Unit (MachineData → Prop) (Int64 → MachineData → Prop) where
  wpTrans q := ⟨fun Q E s => cenv.wp q (Q ()) E s⟩
  wp_trans_monotone _ _ _ _ _ hE hQ := fun s h =>
    Executable.wp_mono (fun s' => hQ () s') hE h

/-- Unfold a triple's wp into the machine-founded transformer. -/
theorem wp_eq [CodeEnv] (q : Program) (Q : Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) :
    WP.wp q Q E s = cenv.wp q (Q ()) E s := rfl

end MachineWP

/-! ## The rule set

One `@[spec]` triple per instruction shape, in composite form: the
precondition is the tail's wp at the record update the instruction performs,
a jump's precondition is `E` at the target's address. Proofs unfold one cell
of the interpreter and advance the placement. -/

section Specs

open MachineWP

variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
  {p : Program}

local macro "wp_step" : tactic =>
  `(tactic| simp only [Directive.interp, Instr.interp,
      Operation.interp, Operand.interp, RegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, Reg64s.get_low64, Reg64s.set_low64, Effects.All,
      or_false, false_or])

/-- Peel the head cell off a placement: the head's size, the head cell in the
segment map, and the tail's placement behind it. -/
private theorem holds_cons {d : Directive} {q : Program} {pc pcEnd : Int64}
    (hpl : cenv.holds pc (d :: q) pcEnd) :
    ∃ z rest, cenv.directivesFromAddress pc = (d, z) :: rest
      ∧ cenv.holds (pc + .ofNat z) q pcEnd := by
  obtain ⟨sized, rest, hseg, hmap, hend⟩ := hpl
  cases sized with
  | nil => cases hmap
  | cons c sized' =>
    obtain ⟨c₁, c₂⟩ := c
    simp only [List.map_cons, List.cons.injEq] at hmap
    obtain ⟨rfl, hmap'⟩ := hmap
    refine ⟨c₂, sized' ++ rest, by simpa using hseg, sized', rest, ?_, hmap', ?_⟩
    · exact CodeEnv.advance pc (c₁, c₂) (sized' ++ rest) (by simpa using hseg)
    · rw [hend]
      simp only [List.map_cons, List.sum_cons]
      rw [int64_ofNat_add, Int64.add_assoc]

private theorem holds_nil {pc pcEnd : Int64} (hpl : cenv.holds pc [] pcEnd) : pcEnd = pc := by
  obtain ⟨sized, rest, hseg, hmap, hend⟩ := hpl
  rw [List.map_eq_nil_iff.mp hmap] at hend
  simpa using hend

/-- Run one cell and continue: the rule pattern shared by every
instruction. -/
private theorem step_here {post : @Post MachineState} {s : MachineData} {pc : Int64}
    {d : Directive} {z : Nat} {rest : List (Directive × Nat)}
    (hseg : cenv.directivesFromAddress pc = (d, z) :: rest)
    (hall : (@Directive.interp cenv.labels d s (.mk pc (pc + .ofNat z))
        (fun s' => .done (s', pc + .ofNat z)) (fun pc' s' => .done (s', pc'))).All
      (fun st => Eventually cenv.instrStep post st)) :
    Eventually cenv.instrStep post (s, pc) :=
  step_cps _ _ _ ⟨d, z, rest, hseg, hall⟩

@[spec] theorem MachineWP.nil_spec :
    ⦃ fun s => Q () s ⦄ ([] : Program) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc pcEnd hpl
    exact Eventually.done _ (Or.inl ⟨(holds_nil hpl).symm, h⟩)

@[spec] theorem MachineWP.nil_append_spec (bs : Program) :
    ⦃ fun s => WP.wp bs Q E s ⦄ (([] : Program) ++ bs) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by rw [List.nil_append]; exact h

@[spec] theorem MachineWP.cons_append_spec (a : Directive) (as bs : Program) :
    ⦃ fun s => WP.wp (a :: (as ++ bs)) Q E s ⦄ ((a :: as) ++ bs) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by rw [List.cons_append]; exact h

@[spec] theorem MachineWP.append_assoc_spec (as bs cs : Program) :
    ⦃ fun s => WP.wp (as ++ (bs ++ cs)) Q E s ⦄ ((as ++ bs) ++ cs) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by rw [List.append_assoc]; exact h

@[spec] theorem MachineWP.label_spec (l : Label) :
    ⦃ fun s => WP.wp p Q E s ⦄ (Directive.label l :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc pcEnd hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := holds_cons hpl
    refine step_here hseg ?_
    wp_step
    exact h _ _ hpl'

@[spec] theorem MachineWP.nop_spec (asz osz : Width) (n : Nat) :
    ⦃ fun s => WP.wp p Q E s ⦄
      (Directive.instr (.regular asz osz (.nop n)) :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc pcEnd hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := holds_cons hpl
    refine step_here hseg ?_
    wp_step
    exact h _ _ hpl'

@[spec] theorem MachineWP.mov_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s => WP.wp p Q E { s with regs := s.regs.set64 r (BitVec.setWidth 64 i.toBitVec) } ⦄
      (Directive.instr (.regular asz .W64 (.mov (.reg (.low r .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc pcEnd hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := holds_cons hpl
    refine step_here hseg ?_
    wp_step
    exact h _ _ hpl'

@[spec] theorem MachineWP.sub_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let b := s.regs.get64 r
        let a := BitVec.setWidth 64 i.toBitVec
        let v := b - a
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r v,
              status := StatusFlags.from_result v
                { cf := v.unsigned != b.unsigned - a.unsigned,
                  af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                  of := v.signed != b.signed - a.signed } } ⦄
      (Directive.instr (.regular asz .W64 (.sub (.reg (.low r .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc pcEnd hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := holds_cons hpl
    refine step_here hseg ?_
    wp_step
    exact h _ _ hpl'

@[spec] theorem MachineWP.add_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := BitVec.setWidth 64 i.toBitVec
        let b := s.regs.get64 r
        let v := a + b
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r v,
              status := StatusFlags.from_result v
                { cf := v.unsigned != a.unsigned + b.unsigned,
                  af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                  of := v.signed != a.signed + b.signed } } ⦄
      (Directive.instr (.regular asz .W64 (.add (.reg (.low r .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc pcEnd hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := holds_cons hpl
    refine step_here hseg ?_
    wp_step
    exact h _ _ hpl'

@[spec] theorem MachineWP.adc_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 rs
        let b := s.regs.get64 rd
        let c := s.status.cf
        let v := a + b + BitVec.ofNat 64 c.toNat
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd v,
              status := StatusFlags.from_result v
                { cf := v.unsigned != a.unsigned + b.unsigned + c,
                  af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned + c,
                  of := v.signed != a.signed + b.signed + c } } ⦄
      (Directive.instr (.regular asz .W64
          (.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc pcEnd hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := holds_cons hpl
    refine step_here hseg ?_
    wp_step
    exact h _ _ hpl'

@[spec] theorem MachineWP.mulx_reg_spec (asz : Width) (hi lo rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rs).unsigned * (s.regs.get64 .rdx).unsigned
        WP.wp p Q E
          { s with regs :=
              (s.regs.set64 lo (BitVec.ofInt 64 v)).set64 hi (BitVec.ofInt 64 (v >>> 64)) } ⦄
      (Directive.instr (.regular asz .W64
          (.mulx (.low hi .W64) (.low lo .W64) (.reg (.low rs .W64)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc pcEnd hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := holds_cons hpl
    refine step_here hseg ?_
    wp_step
    exact h _ _ hpl'

@[spec] theorem MachineWP.xor_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 rd
        let b := s.regs.get64 rs
        let v := a ^^^ b
        ∀ af : Bool,
          WP.wp p Q E
            { s with
                regs := s.regs.set64 rd v,
                status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W64
          (.xor (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc pcEnd hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := holds_cons hpl
    refine step_here hseg ?_
    wp_step
    intro af
    exact h af _ _ hpl'

@[spec] theorem MachineWP.jmp_label_spec (asz osz : Width) (l : Label) :
    ⦃ fun s => E (cenv.labels.label l) s ⦄
      (Directive.instr (.regular asz osz
          (.jmp (.rel (.sub (.label l) .after_current_instruction)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc pcEnd hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := holds_cons hpl
    refine step_here hseg ?_
    wp_step
    have hcancel : pc + .ofNat z + (cenv.labels.label l - (pc + .ofNat z))
        = cenv.labels.label l := by
      apply Int64.toBitVec_inj.mp
      simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    simp only [hcancel]
    exact Eventually.done _ (Or.inr h)

@[spec] theorem MachineWP.jcc_spec (asz osz : Width) (cc : CondCode) (l : Label) :
    ⦃ fun s =>
        (cc.interp s.status = true → E (cenv.labels.label l) s)
          ⊓ (cc.interp s.status = false → WP.wp p Q E s) ⦄
      (Directive.instr (.regular asz osz (.jcc cc l)) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc pcEnd hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := holds_cons hpl
    refine step_here hseg ?_
    wp_step
    cases hc : CondCode.interp cc s.status <;>
      simp only [hc, Bool.false_eq_true, ite_true, ite_false, meet_prop_eq_and,
        Effects.All] at h ⊢
    · exact h.2 trivial _ _ hpl'
    · exact Eventually.done _ (Or.inr (h.1 trivial))

end Specs

/-! ## The general loop rule

`Eventually` is a least fixpoint, so one well-founded induction turns finitely
many local steps into one global run. `I` describes every state the run may
re-enter, and `r` orders those states. `Program.cfg` is the instance where `I`
is a finite table keyed by pc, and `r` is the lex order of variant and block
position. -/

theorem Eventually.wf_ind {State : Type} {trans : State → Post → Prop}
    {r : State → State → Prop} (hwf : WellFounded r) {I post : @Post State}
    (hstep : ∀ st, I st →
      Eventually trans (fun st' => post st' ∨ (I st' ∧ r st' st)) st) :
    ∀ st, I st → Eventually trans post st := by
  intro st
  induction st using hwf.induction with
  | _ st ih =>
    intro hI
    refine eventually_trans _ _ _ _ (hstep st hI) ?_
    rintro mid (hp | ⟨hI', hr⟩)
    · exact Eventually.done _ hp
    · exact ih mid hr hI'

/-! ## Linking fragments

`Program.link` ties finitely or infinitely many separately verified
fragments into one run. Each index `i` names a placed fragment: its text
`frag i` and the address `entry i` where it starts. The address behind it is
derived, `cenv.after`. `T i` is the invariant at that entry, and
`r` orders index-state pairs. A fragment's obligation is a Triple, so `vcgen`
proves it; `link` supplies the well-founded induction that a back edge
needs. -/

/-- Where a step out of fragment `i`, entered in state `s₀`, may land: the
global postcondition at the address it stopped at, or another fragment's
entry, with that fragment's invariant and a smaller measure. -/
def Program.Cont {ι : Type} (post : @Post MachineState) (entry : ι → Int64)
    (T : ι → MachineData → Prop) (r : ι × MachineData → ι × MachineData → Prop)
    (i : ι) (s₀ : MachineData) (a : Int64) (s : MachineData) : Prop :=
  post (s, a) ∨ ∃ j, entry j = a ∧ T j s ∧ r (j, s) (i, s₀)

open MachineWP in
theorem Program.link [CodeEnv] {ι : Type} {post : @Post MachineState}
    (frag : ι → Program) (entry : ι → Int64) (T : ι → MachineData → Prop)
    (r : ι × MachineData → ι × MachineData → Prop) (hwf : WellFounded r)
    (hplace : ∀ i, cenv.sits (entry i) (frag i))
    (hfrag : ∀ i s₀,
      ⦃ fun s => T i s ∧ s = s₀ ⦄
        frag i
      ⦃ fun _ s => Program.Cont post entry T r i s₀
          (cenv.after (entry i) (frag i)) s;
        fun a s => Program.Cont post entry T r i s₀ a s ⦄) :
    ∀ i s, T i s → Eventually cenv.instrStep post (s, entry i) := by
  suffices h : ∀ is : ι × MachineData, T is.1 is.2 →
      Eventually cenv.instrStep post (is.2, entry is.1) by
    intro i s hT
    exact h (i, s) hT
  intro is
  induction is using hwf.induction with
  | _ is ih =>
    intro hT
    have hev := ((hfrag is.1 is.2).le_wp is.2 ⟨hT, rfl⟩) (entry is.1)
      (cenv.after (entry is.1) (frag is.1)) (Executable.holds_of_sits (hplace is.1))
    refine eventually_trans _ _ _ _ hev ?_
    rintro ⟨s', a⟩ (⟨ha, hc⟩ | hc)
    · subst ha
      rcases hc with hp | ⟨j, hj, hTj, hr⟩
      · exact Eventually.done _ hp
      · rw [← hj]
        exact ih (j, s') hr hTj
    · rcases hc with hp | ⟨j, hj, hTj, hr⟩
      · exact Eventually.done _ hp
      · dsimp only at hj
        rw [← hj]
        exact ih (j, s') hr hTj

-- Smoke test: the walk steps a placed fragment through the registered specs.
set_option mvcgen.warning false in
open MachineWP in
example [CodeEnv] :
    ⦃ fun (_ : MachineData) => True ⦄
      ([Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low .rax .W64)) (.imm (.int64 1))))] : Program)
    ⦃ fun _ s => s.regs.rax.toNat = 1 ⦄ := by
  vcgen simplifying_assumptions with finish
