module

/-
The `@[vcgen_simp]` set folds the machine state while `vcgen` steps. A write to a named register or
to a part of one rebuilds the register file as a literal, and a read of a named register from a
literal is the field. The projections of the machine record, the `UInt64` round trip and
reassociation present adjacent literals to `evalGround`, so a chain of ground arithmetic and its
flags fold. A return address read from the slot that a push wrote is the pushed value.
`vcgen … with kfinish` discharges each verification condition with `cfg_exit` and `finish`.
-/
public import Kraken.X64.Registers
public import Std.Tactic.Do.Syntax
public meta import Lean.Elab.Tactic

public section

/-- Reassociation, so a chain of additions over a symbolic start presents
adjacent literals to `evalGround`. -/
@[vcgen_simp] theorem BitVec.add_assoc_rev {w : Nat} (a b c : BitVec w) : a + (b + c) = a + b + c :=
  (BitVec.add_assoc a b c).symm

@[vcgen_simp] theorem BitVec.add_ofNat_zero {w : Nat} (x : BitVec w) : x + (0 : BitVec w) = x :=
  BitVec.add_zero x

@[vcgen_simp] theorem BitVec.ofInt_toInt_int64_zero {w : Nat} :
    BitVec.ofInt w (Int64.toInt 0) = (0 : BitVec w) := by
  simp

attribute [vcgen_simp] UInt64.toBitVec_ofBitVec Int64.toBitVec_ofNat BitVec.ofNat_eq_ofNat
  BitVec.setWidth_eq BitVec.add_zero BitVec.toNat_ofNat Nat.zero_mod Int.add_zero Int.cast_ofNat_Int
  bne_self_eq_false BitVec.xor_self Bool.toNat_false Option.map_some Option.get!_some Option.isSome_some
  BitVec.ofInt_toInt Int64.ofBitVec_toBitVec List.cons_append List.nil_append UInt64.toNat_ofBitVec

@[vcgen_simp] theorem MachineState.data_mk (d : MachineData) (pc : Int64) : (⟨d, pc⟩ : MachineState).data = d := rfl

syntax (name := cfgExit) "cfg_exit" : grind

macro_rules
  | `(grind| cfg_exit) => `(grind| skip)

syntax (name := kfinish) "kfinish" : grind

macro_rules
  | `(grind| kfinish) => `(grind| (cfg_exit; finish))
