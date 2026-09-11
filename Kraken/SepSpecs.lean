/-
The instruction dictionary of the separation-logic wp. Each spec keeps the
composite shape of the machine dictionary, with the memory footprint split
off by `∗` and the slot update carried to the tail by the wand: a store's
precondition owns the old bytes and, under the new bytes, the wp of the rest.

Every proof runs the same route: `SepWP.sep_intro` opens the triple under an
ambient frame, the `Mem.*_sep` lemmas of Kraken/SeparationMem.lean step the
machine memory under that frame, and `SepWP.sep_elim` enters the tail.
-/
import Kraken.SepWP
import Kraken.SeparationMem

open Std.WP
open Lean.Order
open scoped SepWP

/-! ## Assertion-level plumbing -/

theorem MProp.sep_mono_right {w : Nat} (P : MProp w) {Q Q' : MProp w} (h : Q ⊑ Q') :
    P ∗ Q ⊑ P ∗ Q' :=
  PreservesSup.map_mono (MProp.sep P) h

/-- Rotate the middle assertion out: `P ∗ (Q ∗ R) = Q ∗ (P ∗ R)`. -/
theorem MProp.sep_left_comm {w : Nat} (P Q R : MProp w) :
    P ∗ (Q ∗ R) = Q ∗ (P ∗ R) :=
  Std.ExtHashMap.sep_comm_l P Q R

namespace SepWP

variable [CodeEnv] {p : Program}
  {Q : Unit → Reg64s → RegZmms → StatusFlags → MProp 64}
  {E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64}

/-! ## The store -/

/-- Store a 64-bit register through an address expression: the precondition
owns the old bytes at the address and, under the stored bytes, the wp of the
tail. `addr` names the address the expression computes, pinned by `ha` so the
assertion never mentions the program counter; a plain `disp(base)` form
discharges `ha` by `AddrExpr.zeroExtend_interp_base_disp`. -/
theorem mov_store_reg_spec (asz : Width) (a : AddrExpr) (rs : Reg64)
    (addr : Reg64s → BitVec 64)
    (ha : ∀ (L : Labels) (regs : Reg64s) (rng : Std.Rco Int64),
      ((AddrExpr.interp (address_size := .mk asz) (a := a) regs rng).zeroExtend 64) = addr regs)
    (bs : List UInt8) (hlen : bs.length = 8) :
    ⦃ fun r z f => MProp.bytesAt bs (addr r)
        ∗ (MProp.bytesAt (Int.toBytes 8 (r.get64 rs).toInt) (addr r)
            -∗ WP.wp p Q E r z f) ⦄
      (Directive.instr (.regular asz .W64
          (.mov (.mem a) (.regOrMem (.reg (.low rs .W64))))) :: p)
    ⦃ Q; E ⦄ := by
  refine SepWP.sep_intro fun F s hpre => ?_
  intro pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  rw [Kraken.Executable.after_cons_of_not_label rfl hseg]
  -- rotate the footprint to the outside: bs ∗ (F ∗ W)
  rw [show (F ∗ (MProp.bytesAt bs (addr s.regs)
        ∗ (MProp.bytesAt (Int.toBytes 8 (s.regs.get64 rs).toInt) (addr s.regs)
            -∗ WP.wp p Q E s.regs s.zmms s.status)))
      = MProp.bytesAt bs (addr s.regs)
          ∗ (F ∗ (MProp.bytesAt (Int.toBytes 8 (s.regs.get64 rs).toInt) (addr s.regs)
              -∗ WP.wp p Q E s.regs s.zmms s.status))
    from MProp.sep_left_comm ..] at hpre
  -- the machine step: the slot is mapped, and the store rewrites it
  have hload : Mem.loadInt s.dmem (addr s.regs) 8 = some (Int.ofBytes bs) :=
    Mem.loadInt_sep bs (addr s.regs) 8 _ s.dmem hpre hlen (by decide)
  have hstore := Mem.storeInt_sep (addr s.regs) 8 bs _ s.dmem ⟨hpre, hlen⟩
    (s.regs.get64 rs).toInt
  refine step_cps _ _ _ ⟨_, _, _, hseg, Or.inl ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store, Reg64s.get_low64,
    ha _, hload, Effects.All]
  -- enter the tail under the frame, after eliminating the wand
  refine SepWP.sep_elim (s := { s with dmem := _ }) ?_ _ hpl'
  have hstore' : (MProp.bytesAt (Int.toBytes 8 (s.regs.get64 rs).toInt) (addr s.regs)
      ∗ (F ∗ (MProp.bytesAt (Int.toBytes 8 (s.regs.get64 rs).toInt) (addr s.regs)
          -∗ WP.wp p Q E s.regs s.zmms s.status)))
      (Mem.storeInt s.dmem (addr s.regs) 8 (s.regs.get64 rs).toInt) := hstore
  rw [MProp.sep_left_comm] at hstore'
  exact MProp.sep_mono_right F
    (MProp.sep_wand_elim (MProp.bytesAt (Int.toBytes 8 (s.regs.get64 rs).toInt)
      (addr s.regs)) (WP.wp p Q E s.regs s.zmms s.status)) _ hstore'

end SepWP

/-- The address a `disp(base)` expression computes, at 64-bit address size:
the base register plus the displacement. The form every spec's `ha`
instantiates at. -/
theorem AddrExpr.zeroExtend_interp_base_disp [L : Labels] (b : Reg64) (d : Int64)
    (regs : Reg64s) (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W64)
        (a := ⟨some (.reg b), none, .int64 d⟩) regs rng).zeroExtend 64)
      = regs.get64 b + BitVec.ofInt 64 d.toInt := by
  simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize, Reg64s.get64]
  have htake : ∀ x : BitVec 64, x.take Width.W64.bits = x := by
    intro x
    simp [BitVec.take, BitVec.extractLsb']
  rw [htake]
  have hsigned : ∀ x : BitVec 64, x.signed = x.toInt := fun _ => rfl
  rw [hsigned, Int.add_zero,
    show ∀ y : BitVec Width.W64.bits, BitVec.zeroExtend 64 y = y from fun _ => rfl,
    BitVec.ofInt_add, BitVec.ofInt_toInt]

/-! ## Smoke test

The store of `alu_mem`: `movq %rax, 136(%rdx)`. The address hypothesis
discharges by `rfl`, because a `disp(base)` expression reads no label and no
program counter. -/

section Smoke

example [CodeEnv] {p : Program}
    {Q : Unit → Reg64s → RegZmms → StatusFlags → MProp 64}
    {E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64}
    (bs : List UInt8) (hlen : bs.length = 8) :
    ⦃ fun r z f => MProp.bytesAt bs (r.get64 .rdx + 136#64)
        ∗ (MProp.bytesAt (Int.toBytes 8 (r.get64 .rax).toInt) (r.get64 .rdx + 136#64)
            -∗ WP.wp p Q E r z f) ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg .rdx), none, .int64 136⟩)
            (.regOrMem (.reg (.low .rax .W64))))) :: p)
    ⦃ Q; E ⦄ := by
  refine SepWP.mov_store_reg_spec .W64 _ .rax
    (fun regs => regs.get64 .rdx + 136#64) ?_ bs hlen
  intro L regs rng
  rw [AddrExpr.zeroExtend_interp_base_disp]
  rfl

end Smoke
