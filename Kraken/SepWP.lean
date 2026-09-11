/-
The separation-logic weakest precondition. `MProp w` is the assertion type of
the separation algebra: predicates over a `w`-bit byte memory, with `∗` the
disjoint-split conjunction of Kraken/Separation.lean. An assertion of the
program logic keeps registers and flags state-passing and sends only the
memory through the algebra: `Reg64s → RegZmms → StatusFlags → MProp 64`, and
`Int64 →` that for the exit channel.

`SepWP.instWP` interprets a `Program` at this assertion language with the
frame rule internalized on both channels: a triple `⦃P⦄ p ⦃Q; E⦄` holds when
the machine-founded wp validates it under every memory frame, held across the
fall-through and across every exit. `SepWP.sep_intro` is the one door in, and
`SepWP.frames` says every program frames every memory assertion, which is
what the frame inference of `vcgen` consumes.
-/
import Kraken.MachineWP
import Kraken.SeparationTactics

open Std.WP
open Lean.Order

/-! ## The assertion type -/

/-- Assertions over a `w`-bit byte memory: the carrier of the separation
algebra. -/
def MProp (w : Nat) : Type := Mem w → Prop

namespace MProp

variable {w : Nat}

instance : CompleteLattice (MProp w) :=
  inferInstanceAs (CompleteLattice (Mem w → Prop))

instance : Std.WP.Assertion (MProp w) :=
  inferInstanceAs (Std.WP.Assertion (Mem w → Prop))

/-- Separating conjunction: the memory splits into disjoint halves. -/
def sep (P Q : MProp w) : MProp w := Std.ExtHashMap.sep P Q

@[inherit_doc sep] infixr:65 " ∗ " => MProp.sep

/-- The empty assertion: no memory is owned. -/
def emp : MProp w := Std.ExtHashMap.emp

/-- The bytes `bs` sit at `a`, and nothing else is owned. -/
def bytesAt (bs : List UInt8) (a : BitVec w) : MProp w := Eq (bs.At a)

theorem sep_assoc (P Q R : MProp w) : (P ∗ Q) ∗ R = P ∗ (Q ∗ R) :=
  Std.ExtHashMap.sep_assoc P Q R

theorem sep_comm (P Q : MProp w) : P ∗ Q = Q ∗ P :=
  Std.ExtHashMap.sep_comm P Q

theorem emp_sep (P : MProp w) : emp ∗ P = P := Std.ExtHashMap.emp_sep P

theorem sep_emp (P : MProp w) : P ∗ emp = P := Std.ExtHashMap.sep_emp P

/-- The generic sup on `MProp`, pointwise; from the lattice axioms alone. -/
theorem sup_apply (s : MProp w → Prop) (m : Mem w) :
    (CompleteLattice.sup s : MProp w) m ↔ ∃ P, s P ∧ P m := by
  constructor
  · exact fun hm => sup_le s (x := (fun m => ∃ P, s P ∧ P m : MProp w))
      (fun P hP m' hPm' => ⟨P, hP, hPm'⟩) m hm
  · rintro ⟨P, hP, hPm⟩
    exact le_sup (c := s) hP m hPm

/-- `(F ∗ ·)` preserves suprema: the split existential commutes with the
join. Its upper adjoint is the magic wand, which the frame closure takes. -/
instance (F : MProp w) : PreservesSup (MProp.sep F) where
  map_sup s := by
    funext m
    apply propext
    show (∃ m₁ m₂, m₁.union m₂ = m ∧ m₁.inter m₂ = ∅ ∧ F m₁
        ∧ (CompleteLattice.sup s : MProp w) m₂)
      ↔ (CompleteLattice.sup (fun y => ∃ x, s x ∧ y = MProp.sep F x) : MProp w) m
    rw [sup_apply (fun y => ∃ x, s x ∧ y = MProp.sep F x) m]
    constructor
    · rintro ⟨m₁, m₂, hu, hd, hF, hsup⟩
      obtain ⟨P, hP, hPm⟩ := (sup_apply s m₂).mp hsup
      exact ⟨F ∗ P, ⟨P, hP, rfl⟩, m₁, m₂, hu, hd, hF, hPm⟩
    · rintro ⟨g, ⟨P, hP, rfl⟩, m₁, m₂, hu, hd, hF, hPm⟩
      exact ⟨m₁, m₂, hu, hd, hF, (sup_apply s m₂).mpr ⟨P, hP, hPm⟩⟩

/-- The magic wand: the upper adjoint of `(P ∗ ·)`. `P -∗ Q` owns what,
joined with a disjoint `P`, yields `Q`. -/
noncomputable def wand (P Q : MProp w) : MProp w :=
  Lean.Order.PreservesSup.upperAdjoint (MProp.sep P) Q

@[inherit_doc wand] infixr:60 " -∗ " => MProp.wand

theorem wand_intro {P Q R : MProp w} (h : P ∗ Q ⊑ R) : Q ⊑ P -∗ R :=
  Lean.Order.PreservesSup.le_upperAdjoint (MProp.sep P) h

theorem sep_wand_elim (P Q : MProp w) : P ∗ (P -∗ Q) ⊑ Q :=
  Lean.Order.PreservesSup.upperAdjoint_le (MProp.sep P) Q

end MProp

/-! ## The frame operators

The frame is a pure memory assertion. It acts on an assertion of the program
logic pointwise through the state-passing layers, and on the exit channel
through one more layer; `EFrame.pointwise` composes the `PreservesSup`
instances along the way. -/

namespace SepWP

/-- Frame a memory resource onto an assertion: `∗` under the register, vector
and flag layers. -/
def frameOp : MProp 64 → (Reg64s → RegZmms → StatusFlags → MProp 64)
    → Reg64s → RegZmms → StatusFlags → MProp 64 :=
  EFrame.pointwise (EFrame.pointwise (EFrame.pointwise MProp.sep))

instance (F : MProp 64) : PreservesSup (frameOp F) :=
  inferInstanceAs (PreservesSup
    (EFrame.pointwise (EFrame.pointwise (EFrame.pointwise MProp.sep)) F))

@[simp, grind =] theorem frameOp_apply (F : MProp 64)
    (P : Reg64s → RegZmms → StatusFlags → MProp 64) (r : Reg64s) (z : RegZmms)
    (f : StatusFlags) : frameOp F P r z f = F ∗ P r z f := rfl

/-- The exit-channel companion: the same frame, at every exit address. -/
def frameOpE : MProp 64 → (Int64 → Reg64s → RegZmms → StatusFlags → MProp 64)
    → Int64 → Reg64s → RegZmms → StatusFlags → MProp 64 :=
  EFrame.pointwise frameOp

instance (F : MProp 64) : PreservesSup (frameOpE F) :=
  inferInstanceAs (PreservesSup (EFrame.pointwise frameOp F))

@[simp, grind =] theorem frameOpE_apply (F : MProp 64)
    (E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64) (a : Int64) (r : Reg64s)
    (z : RegZmms) (f : StatusFlags) : frameOpE F E a r z f = F ∗ E a r z f := rfl

/-! ## The instance -/

/-- The machine-founded wp, read at the separation assertion language: the
memory is curried out of `MachineData`. -/
private def base [CodeEnv] :
    WP Program Unit (Reg64s → RegZmms → StatusFlags → MProp 64)
      (Int64 → Reg64s → RegZmms → StatusFlags → MProp 64) where
  wpTrans q := ⟨fun Q E regs zmms flags mem =>
    cenv.wp q (fun s' => Q () s'.regs s'.zmms s'.status s'.dmem)
      (fun a s' => E a s'.regs s'.zmms s'.status s'.dmem)
      ⟨regs, zmms, flags, mem⟩⟩
  wp_trans_monotone q := by
    intro Q Q' E E' hE hQ regs zmms flags mem h
    exact Kraken.Executable.wp_mono (fun s' => hQ () s'.regs s'.zmms s'.status s'.dmem)
      (fun a s' => hE a s'.regs s'.zmms s'.status s'.dmem) h

/-- Triples of the separation examples: the frame rule internalized on both
channels over the machine-founded wp. -/
noncomputable scoped instance instWP [CodeEnv] :
    WP Program Unit (Reg64s → RegZmms → StatusFlags → MProp 64)
      (Int64 → Reg64s → RegZmms → StatusFlags → MProp 64) :=
  WP.of_frameClosure frameOp frameOpE base

/-- Prove a separation triple: the machine-founded wp validates it under an
arbitrary memory frame, held across the fall-through and across every exit. -/
theorem sep_intro [CodeEnv] {q : Program}
    {P : Reg64s → RegZmms → StatusFlags → MProp 64}
    {Q : Unit → Reg64s → RegZmms → StatusFlags → MProp 64}
    {E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64}
    (h : ∀ (F : MProp 64) (s : MachineData),
      (F ∗ P s.regs s.zmms s.status) s.dmem →
      cenv.wp q (fun s' => (F ∗ Q () s'.regs s'.zmms s'.status) s'.dmem)
        (fun a s' => (F ∗ E a s'.regs s'.zmms s'.status) s'.dmem) s) :
    ⦃ P ⦄ q ⦃ Q; E ⦄ := by
  refine ⟨WP.le_wp_of_frameClosure_eq (base := base) rfl ?_⟩
  intro F regs zmms flags mem hpre
  exact h F ⟨regs, zmms, flags, mem⟩ hpre

/-- Consume a separation triple's wp under a frame: the machine-founded wp of
the framed pre- and postconditions follows, which is how a spec's proof enters
the wp of the tail. The dual of `sep_intro`. -/
theorem sep_elim [CodeEnv] {q : Program} {F : MProp 64}
    {Q : Unit → Reg64s → RegZmms → StatusFlags → MProp 64}
    {E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64} {s : MachineData}
    (h : (F ∗ WP.wp (self := instWP) q Q E s.regs s.zmms s.status) s.dmem) :
    cenv.wp q (fun s' => (F ∗ Q () s'.regs s'.zmms s'.status) s'.dmem)
      (fun a s' => (F ∗ E a s'.regs s'.zmms s'.status) s'.dmem) s := by
  have hle : frameOp F (WP.wp (self := instWP) q Q E)
      ⊑ base.wp q (fun a => frameOp F (Q a)) (frameOpE F E) := by
    refine PartialOrder.rel_trans
      (Lean.Order.PreservesSup.map_mono (frameOp F) (iInf_le _ F)) ?_
    exact Lean.Order.PreservesSup.upperAdjoint_le (frameOp F) _
  have := hle s.regs s.zmms s.status s.dmem h
  exact this

/-- Every program frames every memory assertion, on both channels: the
interpretation is a frame closure, and `∗` composes resources by `sep_assoc`.
This is the fact the frame inference of `vcgen` discharges per spec
application. -/
theorem frames [CodeEnv] (q : Program) (F : MProp 64) :
    (WP.wpTrans (self := instWP) q).Frames frameOp frameOpE F := by
  refine WP.frames_of_frameClosure frameOp MProp.sep ?_ ?_ ⟨fun q => (base.wpTrans q), fun _ => rfl⟩
  · intro r r' a
    funext regs zmms flags
    show (r ∗ r') ∗ a regs zmms flags = r ∗ (r' ∗ a regs zmms flags)
    exact MProp.sep_assoc r r' (a regs zmms flags)
  · intro r r' E
    funext a regs zmms flags
    show (r ∗ r') ∗ E a regs zmms flags = r ∗ (r' ∗ E a regs zmms flags)
    exact MProp.sep_assoc r r' (E a regs zmms flags)

end SepWP



/-! ## Smoke tests

The instance carries real content: the frame survives a register write, and a
jump carries it into the exit channel. The machine-side obligations are
discharged at `Executable.wp` directly; the dictionary lifting has its own
sections. -/

section Smoke

open scoped SepWP

/-- The empty program preserves any memory assertion. -/
example [CodeEnv] {M : MProp 64} :
    ⦃ fun _ _ _ => M ⦄ ([] : Program)
    ⦃ fun _ _ _ _ => M; fun _ _ _ _ => (⊥ : MProp 64) ⦄ := by
  refine SepWP.sep_intro fun F s hpre => ?_
  intro pc _
  exact Eventually.done _ (Or.inl ⟨rfl, hpre⟩)

/-- A jump carries the memory assertion into the exit channel: the framed
exit is what the generalized closure buys. -/
example [CodeEnv] {M : MProp 64} :
    ⦃ fun _ _ _ => M ⦄
      ([Directive.instr (.regular .W64 .W64
          (.jmp (.rel (.sub (.label "out") .after_current_instruction))))] : Program)
    ⦃ fun _ _ _ _ => (⊥ : MProp 64);
      fun a _ _ _ => fun m => M m ∧ a = (_root_.Executable.labels cenv).label "out" ⦄ := by
  refine SepWP.sep_intro fun F s hpre => ?_
  intro pc hpl
  obtain ⟨z, rest, hseg, -⟩ := hpl
  refine step_cps _ _ _ ⟨_, _, _, hseg, Or.inr ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, Effects.All]
  have hcancel : pc + Int64.ofNat z
      + ((_root_.Executable.labels cenv).label "out" - (pc + Int64.ofNat z))
      = (_root_.Executable.labels cenv).label "out" := by
    apply Int64.toBitVec_inj.mp
    simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
    rw [BitVec.add_comm, BitVec.sub_add_cancel]
  rw [hcancel]
  refine Eventually.done _ (Or.inr ?_)
  obtain ⟨m₁, m₂, hu, hd, hF, hM⟩ := hpre
  exact ⟨m₁, m₂, hu, hd, hF, hM, rfl⟩

end Smoke
