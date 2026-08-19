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
import Kraken.SegmentWPSound

open Std.Internal.Do
open Lean.Order

/-! ## The ambient code -/

/-- The ambient executable. -/
class CodeEnv where
  env : Executable

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

/-- The cells at an address, past the labels that share it. A label occupies
no bytes, so several cells sit at one address; the machine runs the first one
that is not a label. -/
def Executable.codeAt (e : Executable) (pc : Int64) : List (Directive × Nat) :=
  (e.directivesFromAddress pc).dropWhile (fun c => c.1.isLabel)

/-- Running the cell `(d, z)` at `st`: either every resolution falls through,
into `post` at the address behind the cell, or every resolution jumps, into
`post` at the target. Each disjunct poisons the other continuation, which is
the shape `Directive.interp_sound` consumes. -/
def Executable.stepAt (e : Executable) (d : Directive) (z : Nat) (st : MachineState)
    (post : @Post MachineState) : Prop :=
  (@Directive.interp e.labels d st.1 (.mk st.2 (st.2 + .ofNat z))
      (fun s' => .done (s', 0)) (fun _ _ => .unimplemented "jump")).All
    (fun m => post (m.1, st.2 + .ofNat z))
  ∨ (@Directive.interp e.labels d st.1 (.mk st.2 (st.2 + .ofNat z))
      (fun _ => .unimplemented "fallthrough") (fun pc' s' => .done (s', pc'))).All post

/-- One instruction of the ambient code, run from `st`. -/
def Executable.instrStep (e : Executable) (st : MachineState) (post : @Post MachineState) :
    Prop :=
  ∃ d z rest, e.codeAt st.2 = (d, z) :: rest ∧ e.stepAt d z st post

/-- The fragment `q` sits at `pc`: a label costs no address, and every other
cell is the next instruction there. -/
def Executable.sits (e : Executable) (pc : Int64) : Program → Prop
  | [] => True
  | .label _ :: q => e.sits pc q
  | d :: q => ∃ z rest, e.codeAt pc = (d, z) :: rest ∧ e.sits (pc + .ofNat z) q

/-- The address behind the fragment `q` placed at `pc`. -/
def Executable.after (e : Executable) (pc : Int64) : Program → Int64
  | [] => pc
  | .label _ :: q => e.after pc q
  | _ :: q =>
    match e.codeAt pc with
    | [] => pc
    | (_, z) :: _ => e.after (pc + .ofNat z) q

/-- The run of the fragment `q` from `s`: placed anywhere in the ambient
code, the machine eventually falls through to the placement's end with `Q`,
or stops at a pc satisfying `E`. Re-entry inside the fragment is free: the
judgment is the fixpoint `Eventually`, so a back edge simply keeps stepping. -/
def Executable.wp (e : Executable) (q : Program) (Q : MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) : Prop :=
  ∀ (pc : Int64), e.sits pc q →
    Eventually (e.instrStep)
      (fun st => (st.2 = e.after pc q ∧ Q st.1) ∨ E st.2 st.1) (s, pc)

theorem Executable.wp_mono {e : Executable} {q : Program}
    {Q₁ Q₂ : MachineData → Prop} {E₁ E₂ : Int64 → MachineData → Prop}
    (hQ : ∀ s, Q₁ s → Q₂ s) (hE : ∀ a s, E₁ a s → E₂ a s)
    {s : MachineData} (h : e.wp q Q₁ E₁ s) : e.wp q Q₂ E₂ s := fun pc hpl =>
  (h pc hpl).mono (fun _ _ ht => ht)
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
  `(tactic| simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, Operand.interp, RegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, Reg64s.get_low64, Reg64s.set_low64, Effects.All,
      or_false, false_or])

/-- Unfold the fall-through address past one instruction cell. -/
private theorem after_instr {i : Instr} {q : Program} {pc : Int64} {z : Nat}
    {rest : List (Directive × Nat)}
    (hcode : cenv.codeAt pc = (Directive.instr i, z) :: rest) :
    cenv.after pc (Directive.instr i :: q) = cenv.after (pc + .ofNat z) q := by
  simp only [Executable.after, hcode]

/-- Run one cell and continue: the rule pattern shared by every
instruction. -/
private theorem step_here {post : @Post MachineState} {s : MachineData} {pc : Int64}
    {d : Directive} {z : Nat} {rest : List (Directive × Nat)}
    (hseg : cenv.codeAt pc = (d, z) :: rest)
    (hall : cenv.stepAt d z (s, pc) (fun st => Eventually cenv.instrStep post st)) :
    Eventually cenv.instrStep post (s, pc) :=
  step_cps _ _ _ ⟨d, z, rest, hseg, hall⟩

@[spec] theorem MachineWP.nil_spec :
    ⦃ fun s => Q () s ⦄ ([] : Program) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc _
    exact Eventually.done _ (Or.inl ⟨rfl, h⟩)

@[spec] theorem MachineWP.nil_append_spec (bs : Program) :
    ⦃ fun s => WP.wp bs Q E s ⦄ (([] : Program) ++ bs) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by rw [List.nil_append]; exact h

@[spec] theorem MachineWP.cons_append_spec (a : Directive) (as bs : Program) :
    ⦃ fun s => WP.wp (a :: (as ++ bs)) Q E s ⦄ ((a :: as) ++ bs) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by rw [List.cons_append]; exact h

@[spec] theorem MachineWP.append_assoc_spec (as bs cs : Program) :
    ⦃ fun s => WP.wp (as ++ (bs ++ cs)) Q E s ⦄ ((as ++ bs) ++ cs) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by rw [List.append_assoc]; exact h

/-- A label costs no step and no address. -/
@[spec] theorem MachineWP.label_spec (l : Label) :
    ⦃ fun s => WP.wp p Q E s ⦄ (Directive.label l :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => h

@[spec] theorem MachineWP.nop_spec (asz osz : Width) (n : Nat) :
    ⦃ fun s => WP.wp p Q E s ⦄
      (Directive.instr (.regular asz osz (.nop n)) :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg ?_
    wp_step
    exact h _ hpl'

@[spec] theorem MachineWP.mov_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s => WP.wp p Q E { s with regs := s.regs.set64 r (BitVec.setWidth 64 i.toBitVec) } ⦄
      (Directive.instr (.regular asz .W64 (.mov (.reg (.low r .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg ?_
    wp_step
    exact h _ hpl'

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
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg ?_
    wp_step
    exact h _ hpl'

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
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg ?_
    wp_step
    exact h _ hpl'

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
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg ?_
    wp_step
    exact h _ hpl'

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
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg ?_
    wp_step
    exact h _ hpl'

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
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg ?_
    wp_step
    refine Or.inl ?_
    intro af
    exact h af _ hpl'

@[spec] theorem MachineWP.jmp_label_spec (asz osz : Width) (l : Label) :
    ⦃ fun s => E (cenv.labels.label l) s ⦄
      (Directive.instr (.regular asz osz
          (.jmp (.rel (.sub (.label l) .after_current_instruction)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
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
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg ?_
    wp_step
    cases hc : CondCode.interp cc s.status <;>
      simp only [hc, Bool.false_eq_true, ite_true, ite_false, meet_prop_eq_and,
        Effects.All] at h ⊢
    · exact Or.inl (h.2 trivial _ hpl')
    · exact Or.inr (Eventually.done _ (Or.inr (h.1 trivial)))

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

/-! ## The bridge to the segment judgment

`instrStep` runs one instruction; kraken's `straightlineStep` runs a whole
segment, from the pc until a jump or the end of the text. An instruction
chain therefore refines a segment chain, and the two agree when the
postcondition can hold only where the text has run out. -/

/-- What the bridge needs of the ambient code: a label occupies no bytes, and
behind an instruction cell the segment map continues with the cells behind
it. -/
structure Executable.CodeWF (e : Executable) : Prop where
  label_size : ∀ c ∈ e.2, c.1.isLabel = true → c.2 = 0
  advance : ∀ pc d z rest, e.codeAt pc = (d, z) :: rest →
    e.directivesFromAddress (pc + .ofNat z) = rest

private theorem int64_add_zero (pc : Int64) : pc + Int64.ofNat 0 = pc := by
  apply Int64.toBitVec_inj.mp
  simp

private theorem mem_takeWhile {α} {p : α → Bool} {l : List α} {a : α}
    (h : a ∈ l.takeWhile p) : p a = true := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    by_cases hp : p x
    · rw [List.takeWhile_cons, if_pos hp] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact hp
      · exact ih h'
    · rw [List.takeWhile_cons, if_neg hp] at h
      simp at h

/-- One segment burst, as a step of the omni-judgment. -/
private theorem step_burst [Layout] {e : Executable} {post : @Post MachineState}
    {st : MachineState}
    (h : (Executable.straightline e st .done).All
      (fun m => Eventually (straightlineStep e) post m)) :
    Eventually (straightlineStep e) post st := by
  refine step_cps _ _ _ ?_
  unfold straightlineStep at h ⊢
  exact h

/-- A run of label cells at the head of a segment changes nothing. -/
private theorem interp_label_prefix [Labels] :
    ∀ (ls X : List (Directive × Nat)) (s : MachineData) (pc : Int64)
      (ret : Int64 → MachineData → Effects),
      (∀ c ∈ ls, c.1.isLabel = true ∧ c.2 = 0) →
      Directives.interp (ls ++ X) s pc ret = Directives.interp X s pc ret := by
  intro ls
  induction ls with
  | nil => intro X s pc ret _; rfl
  | cons c ls ih =>
    intro X s pc ret hls
    obtain ⟨hlab, hz⟩ := hls c List.mem_cons_self
    obtain ⟨d, z⟩ := c
    cases d with
    | label l =>
      simp only at hz
      subst hz
      simp only [List.cons_append, Directives.interp, Directive.interp, int64_add_zero]
      exact ih X s pc ret (fun c hc => hls c (List.mem_cons_of_mem _ hc))
    | instr i => simp [Directive.isLabel] at hlab
    | byteArray a => simp [Directive.isLabel] at hlab

/-- One segment, cut at its first instruction: the instruction runs, and a
fall-through continues with the segment behind it. -/
theorem Executable.straightline_cons {e : Executable} (hwf : e.CodeWF)
    {pc : Int64} {s : MachineData} {d : Directive} {z : Nat}
    {rest : List (Directive × Nat)} (hcode : e.codeAt pc = (d, z) :: rest) :
    Executable.straightline e (s, pc) .done
      = @Directive.interp e.labels d s (.mk pc (pc + .ofNat z))
          (fun s' => Executable.straightline e (s', pc + .ofNat z) .done)
          (fun pc' s' => .done (s', pc')) := by
  letI := e.labels
  have hsplit : e.directivesFromAddress pc
      = (e.directivesFromAddress pc).takeWhile (fun c => c.1.isLabel) ++ (d, z) :: rest := by
    conv => lhs; rw [← List.takeWhile_append_dropWhile (p := fun c => c.1.isLabel)
      (l := e.directivesFromAddress pc)]
    rw [show (e.directivesFromAddress pc).dropWhile (fun c => c.1.isLabel)
      = (d, z) :: rest from hcode]
  have hsub : ∀ c ∈ e.directivesFromAddress pc, c ∈ e.2 := by
    intro c hc
    unfold Executable.directivesFromAddress at hc
    exact (List.drop_sublist _ _).subset hc
  have hls : ∀ c ∈ (e.directivesFromAddress pc).takeWhile (fun c => c.1.isLabel),
      c.1.isLabel = true ∧ c.2 = 0 := by
    intro c hc
    have hlab : c.1.isLabel = true :=
      mem_takeWhile (p := fun c : Directive × Nat => c.1.isLabel) hc
    have hmem : c ∈ e.directivesFromAddress pc :=
      (List.takeWhile_sublist _).subset hc
    exact ⟨hlab, hwf.label_size c (hsub c hmem) hlab⟩
  show @Directives.interp e.labels (e.directivesFromAddress pc) s pc
    (fun pc' s' => .done (s', pc')) = _
  rw [hsplit, interp_label_prefix _ _ _ _ _ hls]
  simp only [Directives.interp]
  congr 1
  funext s'
  show Directives.interp rest s' (pc + .ofNat z) _ = _
  rw [← hwf.advance pc d z rest hcode]
  rfl

/-- An instruction chain is a segment chain, when the postcondition can hold
only where the text has run out. -/
theorem Executable.bridge [Layout] {e : Executable} (hwf : e.CodeWF)
    {post : @Post MachineState}
    (hbnd : ∀ st, post st → e.directivesFromAddress st.2 = []) :
    ∀ st, Eventually e.instrStep post st → Eventually (straightlineStep e) post st := by
  have key : ∀ st, Eventually e.instrStep post st →
      (Executable.straightline e st .done).All
        (fun m => Eventually (straightlineStep e) post m) := by
    intro st h
    induction h with
    | done st hp =>
      show (@Directives.interp e.labels (e.directivesFromAddress st.2) st.1 st.2 _).All _
      rw [hbnd st hp]
      simp only [Directives.interp, Effects.All]
      exact Eventually.done _ hp
    | step st mid_p htrans _ ih =>
      obtain ⟨d, z, rest, hcode, hstep⟩ := htrans
      rw [Executable.straightline_cons hwf hcode]
      letI := e.labels
      exact Directive.interp_sound (next := fun s' => mid_p (s', st.2 + .ofNat z))
        (jmp := mid_p)
        (fun s' hmid => ih (s', st.2 + .ofNat z) hmid)
        (fun st' hmid => step_burst (ih st' hmid))
        hstep
  intro st h
  exact step_burst (key st h)

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
      (hplace is.1)
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

/-! ## The control-flow rule

`Program.cfg` instantiates `link` at the blocks of a labeled program: the
index is the label, the entry is the label's address, the fragment is the
block body, and the order is the lex order of variant and block position.
`Program.Placed` collects the placement facts that connect the program's
syntax to the ambient addresses. -/

/-- Where a label's block sits in the ambient code. -/
structure Program.Placed [CodeEnv] (p : Program) (l₀ : Label) : Prop where
  /-- Every placement of the text starts at the entry label's address. -/
  entry : ∀ pc, cenv.sits pc p → cenv.labels.label l₀ = pc
  /-- A block's body sits at its label's address. -/
  block : ∀ l blk, Program.blockAt p l = some blk →
    cenv.sits (cenv.labels.label l) blk.body
  /-- A block that falls into another ends at that block's address. -/
  next : ∀ l blk l', Program.blockAt p l = some blk → blk.next = some l' →
    cenv.after (cenv.labels.label l) blk.body = cenv.labels.label l'
  /-- The last block ends where the text ends. -/
  last : ∀ pc, cenv.sits pc p → ∀ l blk, Program.blockAt p l = some blk →
    blk.next = none → cenv.after (cenv.labels.label l) blk.body = cenv.after pc p

/-- A label-keyed table, read at an address. -/
def Table.ofLabels [CodeEnv] (tl : Label → MachineData → Prop) :
    Int64 → MachineData → Prop :=
  fun a s => ∃ l, cenv.labels.label l = a ∧ tl l s

@[grind ←] theorem Table.ofLabels_at [CodeEnv] {tl : Label → MachineData → Prop}
    {l : Label} {s : MachineData} (h : tl l s) :
    Table.ofLabels tl (cenv.labels.label l) s := ⟨l, rfl, h⟩

/-- The block a block falls into: it is mapped, and it sits one position
later in the text. -/
theorem Program.blockAt_next {p : Program} (hnd : (Program.labels p).Nodup)
    {l : Label} {blk : Program.Block} (h : Program.blockAt p l = some blk)
    {l' : Label} (hn : blk.next = some l') :
    (Program.blockAt p l').isSome ∧ Program.blockIdx p l' = Program.blockIdx p l + 1 := by
  obtain ⟨-, i, hi, hnext⟩ := Program.blockAtAux_spec h
  rw [hn] at hnext
  have hndv : ((Program.view p).2.map (·.1)).Nodup := by rwa [← Program.labels_view]
  cases hj : (Program.view p).2[i + 1]? with
  | none => rw [hj] at hnext; cases hnext
  | some lb =>
    obtain ⟨l₁, b₁⟩ := lb
    rw [hj] at hnext
    simp only [Option.map_some, Option.some.injEq] at hnext
    subst hnext
    refine ⟨?_, ?_⟩
    · show (Program.blockAtAux (Program.view p).2 l').isSome = true
      rw [Program.blockAtAux_of_getElem hndv hj]
      rfl
    · rw [Program.blockIdx_eq hnd hj, Program.blockIdx_eq hnd hi]

/-- A mapped label sits inside the block list. -/
theorem Program.blockIdx_lt {p : Program} (hnd : (Program.labels p).Nodup)
    {l : Label} {blk : Program.Block} (h : Program.blockAt p l = some blk) :
    Program.blockIdx p l < (Program.view p).2.length := by
  obtain ⟨-, i, hi, -⟩ := Program.blockAtAux_spec h
  rw [Program.blockIdx_eq hnd hi]
  by_cases hlt : i < (Program.view p).2.length
  · exact hlt
  · rw [List.getElem?_eq_none (by omega)] at hi
    cases hi

/-- The block index never exceeds the number of blocks. -/
theorem Program.blockIdx_le (p : Program) (l : Label) :
    Program.blockIdx p l ≤ (Program.view p).2.length := by
  have h := List.idxOf_le_length (a := l) (l := Program.labels p)
  have hlen : (Program.labels p).length = (Program.view p).2.length := by
    rw [Program.labels_view, List.length_map]
  rw [hlen] at h
  exact h

/-- The lex order of the control-flow rule, encoded in one number: the
variant dominates, and the block position breaks ties. -/
private def Program.cfgMeasure (p : Program) (var : Label → MachineData → Nat)
    (x : Label × MachineData) : Nat :=
  var x.1 x.2 * ((Program.view p).2.length + 1)
    + ((Program.view p).2.length - Program.blockIdx p x.1)

/-- The control-flow rule: one spec table `T`, one variant `var`, one triple
per block of the map `Program.blockAt`. Each block is entered with its table
entry and the variant snapshotted; it falls into the next block with the
entry there and the variant not increased, and a jump exit lands on a mapped
table entry along `Program.EdgeLt`. -/
theorem MachineWP.cfg [CodeEnv] {p p' : Program} {P : MachineData → Prop}
    {Q : Unit → MachineData → Prop} {l₀ : Label}
    (T : Label → MachineData → Prop) (var : Label → MachineData → Nat)
    (hpl : Program.Placed p l₀)
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => T l s ∧ var l s = n ⦄ blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T l' s ∧ var l' s ≤ n
         | none => Q);
        Table.ofLabels (fun l' s => (Program.blockAt p l').isSome ∧ T l' s
          ∧ Program.EdgeLt p var l n l' s) ⦄)
    (hp : p = Directive.label l₀ :: p' := by rfl)
    (hwf : Program.WF p := by decide)
    (hP : P = T l₀ := by rfl) :
    ⦃ P ⦄ p ⦃ Q ⦄ := by
  subst hP
  have hnd := hwf.nodup
  refine Triple.intro fun s hT => ?_
  intro pc hplace
  have hK : ∀ l, Program.blockIdx p l ≤ (Program.view p).2.length :=
    Program.blockIdx_le p
  have key := Program.link (post := fun st => st.2 = cenv.after pc p ∧ Q () st.1)
    (frag := fun l => (Program.blockAt p l).elim [] (·.body))
    (entry := fun l => cenv.labels.label l)
    (T := fun l s => (Program.blockAt p l).isSome ∧ T l s)
    (r := fun x y => Program.cfgMeasure p var x < Program.cfgMeasure p var y)
    (measure (Program.cfgMeasure p var)).wf ?_ ?_
  · have h0 : (Program.blockAt p l₀).isSome := by
      rw [hp]
      show (Program.blockAtAux (Program.view (Directive.label l₀ :: p')).2 l₀).isSome = true
      simp [Program.view, Program.blockAtAux]
    have hrun := key l₀ s ⟨h0, hT⟩
    rw [hpl.entry pc hplace] at hrun
    exact hrun.mono (fun _ _ ht => ht) (fun st hst => Or.inl hst)
  · intro l
    cases hb : Program.blockAt p l with
    | none => exact trivial
    | some blk => simpa [hb] using hpl.block l blk hb
  · intro l s₀
    cases hb : Program.blockAt p l with
    | none =>
      exact Triple.intro fun s hpre => absurd hpre.1.1 (by simp [hb])
    | some blk =>
      simp only [hb, Option.elim]
      refine Triple.intro fun s hpre => ?_
      obtain ⟨⟨-, hTl⟩, rfl⟩ := hpre
      have hidx : Program.blockIdx p l < (Program.view p).2.length :=
        Program.blockIdx_lt hnd hb
      refine Executable.wp_mono ?_ ?_ ((hblocks l blk hb (var l s)).le_wp s ⟨hTl, rfl⟩)
      · intro s' hq
        cases hnx : blk.next with
        | some l' =>
          rw [hnx] at hq
          obtain ⟨hTl', hvar⟩ := hq
          obtain ⟨hsome', hidx'⟩ := Program.blockAt_next hnd hb hnx
          refine Or.inr ⟨l', (hpl.next l blk l' hb hnx).symm, ⟨hsome', hTl'⟩, ?_⟩
          have hmul : var l' s' * ((Program.view p).2.length + 1)
              ≤ var l s * ((Program.view p).2.length + 1) :=
            Nat.mul_le_mul_right _ hvar
          simp only [Program.cfgMeasure]
          omega
        | none =>
          rw [hnx] at hq
          exact Or.inl ⟨(hpl.last pc hplace l blk hb hnx).symm ▸ rfl, hq⟩
      · rintro a s' ⟨l', hlab, hsome', hTl', hedge⟩
        refine Or.inr ⟨l', hlab, ⟨hsome', hTl'⟩, ?_⟩
        have hle' : Program.blockIdx p l' ≤ (Program.view p).2.length := hK l'
        simp only [Program.cfgMeasure]
        rcases hedge with hlt | ⟨heq, hij⟩
        · have hmul : (var l' s' + 1) * ((Program.view p).2.length + 1)
              ≤ var l s * ((Program.view p).2.length + 1) :=
            Nat.mul_le_mul_right _ hlt
          have hsucc : (var l' s' + 1) * ((Program.view p).2.length + 1)
              = var l' s' * ((Program.view p).2.length + 1)
                + ((Program.view p).2.length + 1) := Nat.succ_mul _ _
          omega
        · rw [heq]
          omega

-- Smoke test: the walk steps a placed fragment through the registered specs.
set_option mvcgen.warning false in
open MachineWP in
example [CodeEnv] :
    ⦃ fun (_ : MachineData) => True ⦄
      ([Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low .rax .W64)) (.imm (.int64 1))))] : Program)
    ⦃ fun _ s => s.regs.rax.toNat = 1 ⦄ := by
  vcgen simplifying_assumptions with finish
