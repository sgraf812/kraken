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

/-! ## The wp -/

/-- The run of the fragment `q` from `s`: placed anywhere in the ambient
code, its cells run and every stop is a fall-through at the placement's end
satisfying `Q`, or a stop at a pc satisfying `E`. -/
def Executable.wp (e : Executable) (q : Program) (Q : MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) : Prop :=
  ∀ (pc : Int64) (sized rest : List (Directive × Nat)),
    sized.map Prod.fst = q →
    e.directivesFromAddress pc = sized ++ rest →
    (@Directives.interp e.labels sized s pc (fun pc' s' => .done (s', pc'))).All
      (fun st => (st.2 = pc + .ofNat ((sized.map Prod.snd).sum) ∧ Q st.1)
        ∨ E st.2 st.1)

theorem Executable.wp_mono {e : Executable} {q : Program}
    {Q₁ Q₂ : MachineData → Prop} {E₁ E₂ : Int64 → MachineData → Prop}
    (hQ : ∀ s, Q₁ s → Q₂ s) (hE : ∀ a s, E₁ a s → E₂ a s)
    {s : MachineData} (h : e.wp q Q₁ E₁ s) : e.wp q Q₂ E₂ s := by
  intro pc sized rest hmap hseg
  exact Effects.All.mono
    (fun st hst => hst.imp (fun ⟨ha, hq⟩ => ⟨ha, hQ _ hq⟩) (hE _ _)) _
    (h pc sized rest hmap hseg)

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
  `(tactic| simp only [MachineWP.wp_eq, Executable.wp, Directives.interp,
      Directive.interp, Instr.interp,
      Operation.interp, Operand.interp, RegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, Reg64s.get_low64, Reg64s.set_low64, Effects.All,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.cons_append,
      or_false, false_or])

/-- Peel one placed cell: the tail's wp yields the tail's `All` at the
advanced placement, with the end address reassociated. -/
private theorem tail_step {q : Program} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData}
    (h : cenv.wp q Q E s) {pc : Int64} {d : Directive} {z : Nat}
    {sized rest : List (Directive × Nat)} (hmap : sized.map Prod.fst = q)
    (hseg : cenv.directivesFromAddress pc = (d, z) :: (sized ++ rest)) :
    (@Directives.interp cenv.labels sized s (pc + .ofNat z)
        (fun pc' s' => .done (s', pc'))).All
      (fun st => (st.2 = pc + .ofNat (z + (sized.map Prod.snd).sum) ∧ Q st.1)
        ∨ E st.2 st.1) := by
  have hadv := CodeEnv.advance pc (d, z) (sized ++ rest) hseg
  have hall := h (pc + .ofNat z) sized rest hmap hadv
  refine Effects.All.mono (fun st hst => hst.imp (fun ⟨ha, hq⟩ => ⟨?_, hq⟩) id) _ hall
  rw [ha, int64_ofNat_add, Int64.add_assoc]

@[spec] theorem MachineWP.nil_spec :
    ⦃ fun s => Q () s ⦄ ([] : Program) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc sized rest hmap hseg
    rw [List.map_eq_nil_iff.mp hmap]
    simp only [Directives.interp, List.map_nil, List.sum_nil, Effects.All]
    exact Or.inl ⟨by simp, h⟩

@[spec] theorem MachineWP.nil_append_spec (bs : Program) :
    ⦃ fun s => WP.wp bs Q E s ⦄ (([] : Program) ++ bs) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by rw [List.nil_append]; exact h

@[spec] theorem MachineWP.cons_append_spec (a : Directive) (as bs : Program) :
    ⦃ fun s => WP.wp (a :: (as ++ bs)) Q E s ⦄ ((a :: as) ++ bs) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by rw [List.cons_append]; exact h

@[spec] theorem MachineWP.append_assoc_spec (as bs cs : Program) :
    ⦃ fun s => WP.wp (as ++ (bs ++ cs)) Q E s ⦄ ((as ++ bs) ++ cs) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by rw [List.append_assoc]; exact h

omit [CodeEnv] in
/-- Split a cons-headed placement into the head cell and the placed tail. -/
private theorem cons_placement {d : Directive} {q : Program}
    {sized : List (Directive × Nat)} (hmap : sized.map Prod.fst = d :: q) :
    ∃ z sized', sized = (d, z) :: sized' ∧ sized'.map Prod.fst = q := by
  cases sized with
  | nil => cases hmap
  | cons c sized' =>
    obtain ⟨c₁, c₂⟩ := c
    simp only [List.map_cons, List.cons.injEq] at hmap
    exact ⟨c₂, sized', by rw [hmap.1], hmap.2⟩

@[spec] theorem MachineWP.label_spec (l : Label) :
    ⦃ fun s => WP.wp p Q E s ⦄ (Directive.label l :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc sized rest hmap hseg
    obtain ⟨z, sized', rfl, hmap'⟩ := cons_placement hmap
    wp_step
    exact tail_step h hmap' (by simpa using hseg)

@[spec] theorem MachineWP.nop_spec (asz osz : Width) (n : Nat) :
    ⦃ fun s => WP.wp p Q E s ⦄
      (Directive.instr (.regular asz osz (.nop n)) :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc sized rest hmap hseg
    obtain ⟨z, sized', rfl, hmap'⟩ := cons_placement hmap
    wp_step
    exact tail_step h hmap' (by simpa using hseg)

@[spec] theorem MachineWP.mov_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s => WP.wp p Q E { s with regs := s.regs.set64 r (BitVec.setWidth 64 i.toBitVec) } ⦄
      (Directive.instr (.regular asz .W64 (.mov (.reg (.low r .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc sized rest hmap hseg
    obtain ⟨z, sized', rfl, hmap'⟩ := cons_placement hmap
    wp_step
    exact tail_step h hmap' (by simpa using hseg)

@[spec] theorem MachineWP.jmp_label_spec (asz osz : Width) (l : Label) :
    ⦃ fun s => E (cenv.labels.label l) s ⦄
      (Directive.instr (.regular asz osz
          (.jmp (.rel (.sub (.label l) .after_current_instruction)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc sized rest hmap hseg
    obtain ⟨z, sized', rfl, hmap'⟩ := cons_placement hmap
    wp_step
    have hcancel : pc + .ofNat z + (cenv.labels.label l - (pc + .ofNat z))
        = cenv.labels.label l := by
      apply Int64.toBitVec_inj.mp
      simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    simp only [hcancel]
    exact Or.inr h

end Specs

-- Smoke test: the walk steps a placed fragment through the registered specs.
set_option mvcgen.warning false in
open MachineWP in
example [CodeEnv] :
    ⦃ fun (_ : MachineData) => True ⦄
      ([Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low .rax .W64)) (.imm (.int64 1))))] : Program)
    ⦃ fun _ s => s.regs.rax.toNat = 1 ⦄ := by
  vcgen simplifying_assumptions with finish
