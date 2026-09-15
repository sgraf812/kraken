/-
The separation-logic weakest precondition on the monadic encoding `X64M`.
`X64M`'s wp already sequences a program through `vcgen`'s bind rule and its
`@[spec]` dictionary; this layer frames the `dmem` component of the system
state `Sys D` by separating conjunction, so a spec owns only the memory it
touches and `vcgen`'s frame inference supplies the rest.

The instance is `WPMonad.of_frameClosure` over `X64M`'s own wp, exactly as
`HeapM` in the toolchain's `vcgenSepLogic` test is the frame closure of
`StateM Heap`. The frame acts on both channels: a jump throw carries the
system state, so memory the fragment does not touch is still owned wherever
control lands.
-/
import Kraken.X64M
import Kraken.Separation
import Kraken.SeparationMem

open Std.WP
open Lean.Order

/-- Assertions over a `w`-bit byte memory: the carrier of the separation
algebra. -/
def MProp (w : Nat) : Type := Mem w → Prop

namespace MProp
variable {w : Nat}
instance : CompleteLattice (MProp w) := inferInstanceAs (CompleteLattice (Mem w → Prop))
instance : Std.WP.Assertion (MProp w) := inferInstanceAs (Std.WP.Assertion (Mem w → Prop))
/-- Separating conjunction on memory. -/
def sep (P Q : MProp w) : MProp w := Std.ExtHashMap.sep P Q
@[inherit_doc sep] infixr:65 " ∗ " => MProp.sep
/-- The empty assertion. -/
def emp : MProp w := Std.ExtHashMap.emp
theorem sep_assoc (P Q R : MProp w) : (P ∗ Q) ∗ R = P ∗ (Q ∗ R) := Std.ExtHashMap.sep_assoc P Q R
theorem emp_sep (P : MProp w) : emp ∗ P = P := Std.ExtHashMap.emp_sep P

theorem sup_apply (s : MProp w → Prop) (m : Mem w) :
    (CompleteLattice.sup s : MProp w) m ↔ ∃ P, s P ∧ P m := by
  constructor
  · exact fun hm => sup_le s (x := (fun m => ∃ P, s P ∧ P m : MProp w))
      (fun P hP m' hPm' => ⟨P, hP, hPm'⟩) m hm
  · rintro ⟨P, hP, hPm⟩; exact le_sup (c := s) hP m hPm

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
end MProp

namespace SepM

open Kraken

/-! ## Framing the memory sub-field of the system state -/

/-- Replace the `dmem` field of a system state. -/
def setDmem {D : Type} (s : Sys D) (m : Mem 64) : Sys D :=
  { s with machine := { s.machine with dmem := m } }

@[simp] theorem dmem_setDmem {D : Type} (s : Sys D) (m : Mem 64) :
    (setDmem s m).machine.dmem = m := rfl
@[simp] theorem setDmem_setDmem {D : Type} (s : Sys D) (m m' : Mem 64) :
    setDmem (setDmem s m) m' = setDmem s m' := rfl
@[simp] theorem setDmem_dmem {D : Type} (s : Sys D) :
    setDmem s s.machine.dmem = s := rfl
@[simp] theorem regs_setDmem {D : Type} (s : Sys D) (m : Mem 64) :
    (setDmem s m).machine.regs = s.machine.regs := rfl

/-- Separate a memory resource out of an assertion on `Sys D`: the state's
`dmem` splits into the resource and the part the assertion sees. -/
def sysSep {D : Type} (F : MProp 64) (P : Sys D → Prop) : Sys D → Prop :=
  fun s => (F ∗ fun m => P (setDmem s m)) s.machine.dmem

/-- The memory sup, transported through the `dmem`-reindex. -/
private theorem sys_sup_apply {D : Type} (s : (Sys D → Prop) → Prop) (sys : Sys D) :
    (CompleteLattice.sup s : Sys D → Prop) sys ↔ ∃ P, s P ∧ P sys := by
  constructor
  · exact fun hm => sup_le s (x := (fun sys => ∃ P, s P ∧ P sys : Sys D → Prop))
      (fun P hP s' hPs' => ⟨P, hP, hPs'⟩) sys hm
  · rintro ⟨P, hP, hPs⟩; exact le_sup (c := s) hP sys hPs

instance {D : Type} (F : MProp 64) : PreservesSup (sysSep (D := D) F) where
  map_sup s := by
    funext sys
    apply propext
    show (∃ m₁ m₂, m₁.union m₂ = sys.machine.dmem ∧ m₁.inter m₂ = ∅ ∧ F m₁
        ∧ (CompleteLattice.sup s : Sys D → Prop)
            { sys with machine := { sys.machine with dmem := m₂ } })
      ↔ (CompleteLattice.sup (fun y => ∃ x, s x ∧ y = sysSep F x) : Sys D → Prop) sys
    rw [sys_sup_apply (fun y => ∃ x, s x ∧ y = sysSep F x) sys]
    constructor
    · rintro ⟨m₁, m₂, hu, hd, hF, hsup⟩
      obtain ⟨P, hP, hPs⟩ := (sys_sup_apply s _).mp hsup
      exact ⟨sysSep F P, ⟨P, hP, rfl⟩, m₁, m₂, hu, hd, hF, hPs⟩
    · rintro ⟨g, ⟨P, hP, rfl⟩, m₁, m₂, hu, hd, hF, hPs⟩
      exact ⟨m₁, m₂, hu, hd, hF, (sys_sup_apply s _).mpr ⟨P, hP, hPs⟩⟩

/-- The frame on the normal channel: `Env → Int64 → Sys D → Prop`. -/
abbrev normOp (D : Type) : MProp 64 → (Env → Int64 → Sys D → Prop)
    → Env → Int64 → Sys D → Prop :=
  EFrame.pointwise (EFrame.pointwise (sysSep (D := D)))

/-- The frame on the exception channel: `X64Exit → Sys D → Prop`. -/
abbrev exitOp (D : Type) : MProp 64 → (X64Exit → Sys D → Prop) → X64Exit → Sys D → Prop :=
  EFrame.pointwise (sysSep (D := D))

/-! ## The instance

The frame closure of `X64M`'s own wp over separating conjunction on the
`dmem` field, on both channels. `sep`'s associativity is the composition law
and `emp` its unit, lifted through the pointwise layers. -/

theorem sysSep_assoc {D : Type} (r r' : MProp 64) (P : Sys D → Prop) :
    sysSep (r ∗ r') P = sysSep r (sysSep r' P) := by
  funext s
  show Std.ExtHashMap.sep (Std.ExtHashMap.sep r r') (fun m => P (setDmem s m)) s.machine.dmem = _
  rw [congrFun (Std.ExtHashMap.sep_assoc r r' (fun m => P (setDmem s m))) s.machine.dmem]
  rfl

theorem sysSep_emp {D : Type} (P : Sys D → Prop) : sysSep MProp.emp P = P := by
  funext s
  show Std.ExtHashMap.sep Std.ExtHashMap.emp (fun m => P (setDmem s m)) s.machine.dmem = P s
  rw [Std.ExtHashMap.emp_sep]
  simp

/-- `X64M`'s own wp, named before the sep instance is declared so that
`inferInstance` resolves to it rather than to the scoped sep instance. -/
def baseWPM (D : Type) : WPMonad (X64M D) (Env → Int64 → Sys D → Prop)
    (X64Exit → Sys D → Prop) := inferInstance

/-- Triples of the separation examples: the frame rule internalized on both
channels over `X64M`'s wp. -/
noncomputable scoped instance instWP (D : Type) :
    WPMonad (X64M D) (Env → Int64 → Sys D → Prop) (X64Exit → Sys D → Prop) :=
  WPMonad.of_frameClosure (normOp D) (exitOp D)
    (comp := MProp.sep) (e := MProp.emp)
    (fun r r' a => by funext env rip; exact sysSep_assoc r r' (a env rip))
    (fun r r' E => by funext x; exact sysSep_assoc r r' (E x))
    (fun a => by funext env rip; exact sysSep_emp (a env rip))
    (fun E => by funext x; exact sysSep_emp (E x))
    (baseWPM D)

/-! ## The door in, and a memory atom -/

/-- The bytes `bs` sit at address `a`, and no other memory is owned. Small
footprint: it pins the whole `dmem`, and the frame supplies the rest. -/
def ptsTo {D : Type} (a : BitVec 64) (bs : List UInt8) : Env → Int64 → Sys D → Prop :=
  fun _ _ s => Eq (bs.At a) s.machine.dmem

/-- Prove a separation triple by proving the base `X64M` triple under every
memory frame, framed on both channels. The single door into the sep instance;
`vcgen` chains the specs it produces. -/
theorem triple_of_base {D : Type} {prog : X64M D Unit}
    {P : Env → Int64 → Sys D → Prop} {Q : Unit → Env → Int64 → Sys D → Prop}
    {E : X64Exit → Sys D → Prop}
    (h : ∀ F : MProp 64, normOp D F P ⊑
      WP.wp (self := (baseWPM D).toWP Unit) prog
        (fun a => normOp D F (Q a)) (exitOp D F E)) :
    Triple prog P Q E :=
  ⟨WP.le_wp_of_frameClosure_eq (op := normOp D) (opE := exitOp D)
    (base := (baseWPM D).toWP Unit) rfl h⟩

end SepM

/-! ## The store spec

Stated and chained by `vcgen` under the sep instance. The base obligation is
proved here, where `X64M`'s own wp is the ambient instance, so the base
dictionary applies without the scoped sep instance shadowing it. -/

open Kraken

/-- The base obligation of the store spec: under any memory frame, `X64M`'s
own wp of the store holds, ending with the stored bytes owned beside the
frame. -/
theorem mov_mem_imm_base {D : Type} (ae : AddrExpr) (i : Int64) (bs : List UInt8)
    (hlen : bs.length = 8) (F : MProp 64) :
    SepM.normOp D F (fun env rip s => SepM.ptsTo
        (AddrExpr.interp64 env.labels ae s.machine.regs (.mk rip (rip + Int64.ofNat env.curSize))) bs
        env rip s)
      ⊑ WP.wp (Op.mov (.mem ae) (.imm (.int64 i)) : X64M D Unit)
        (fun _ => SepM.normOp D F (fun env rip s => SepM.ptsTo
          (AddrExpr.interp64 env.labels ae s.machine.regs (.mk rip (rip + Int64.ofNat env.curSize)))
          (Int.toBytes 8 (BitVec.setWidth 64 i.toBitVec).toInt) env rip s))
        (SepM.exitOp D F (fun _ _ => False)) := by
  refine PartialOrder.rel_trans ?_
    (Op.mov_mem_imm_spec (Q := fun _ => SepM.normOp D F (fun env rip s => SepM.ptsTo
        (AddrExpr.interp64 env.labels ae s.machine.regs (.mk rip (rip + Int64.ofNat env.curSize)))
        (Int.toBytes 8 (BitVec.setWidth 64 i.toBitVec).toInt) env rip s))
      (E := SepM.exitOp D F (fun _ _ => False)) ae i (Int.ofBytes bs)).le_wp
  intro env rip s hpre
  simp only [SepM.normOp, EFrame.pointwise, Function.comp, SepM.sysSep, SepM.ptsTo,
    SepM.dmem_setDmem, SepM.regs_setDmem, MProp.sep] at hpre ⊢
  generalize ha : AddrExpr.interp64 env.labels ae s.machine.regs
    (.mk rip (rip + Int64.ofNat env.curSize)) = a at hpre ⊢
  have hsplit : (Std.ExtHashMap.sep (Eq (bs.At a)) F) s.machine.dmem :=
    (congrFun (Std.ExtHashMap.sep_comm F (Eq (bs.At a))) s.machine.dmem) ▸ hpre
  rw [meet_prop_eq_and]
  refine ⟨Mem.loadInt_sep bs a 8 F s.machine.dmem hsplit hlen (by decide), ?_⟩
  have hstore := Mem.storeInt_sep a 8 bs F s.machine.dmem ⟨hsplit, hlen⟩
    (BitVec.setWidth 64 i.toBitVec).toInt
  exact (congrFun (Std.ExtHashMap.sep_comm
    (Eq ((Int.toBytes 8 (BitVec.setWidth 64 i.toBitVec).toInt).At a)) F) _) ▸ hstore

@[spec] theorem SepM.mov_mem_imm_spec {D : Type} (ae : AddrExpr) (i : Int64) (bs : List UInt8)
    (hlen : bs.length = 8) :
    Triple (Op.mov (.mem ae) (.imm (.int64 i)) : X64M D Unit)
      (fun env rip s => SepM.ptsTo
        (AddrExpr.interp64 env.labels ae s.machine.regs (.mk rip (rip + Int64.ofNat env.curSize))) bs
        env rip s)
      (fun _ env rip s => SepM.ptsTo
        (AddrExpr.interp64 env.labels ae s.machine.regs (.mk rip (rip + Int64.ofNat env.curSize)))
        (Int.toBytes 8 (BitVec.setWidth 64 i.toBitVec).toInt) env rip s)
      (fun _ _ => False) := by
  exact SepM.triple_of_base fun F => mov_mem_imm_base ae i bs hlen F
