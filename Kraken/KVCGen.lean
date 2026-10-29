module

/-
`kvcgen64 [defs] with step` is `vcgen` with the machine state folded as it
goes. A write to a named register or to a part of one rebuilds the register file as a literal,
and a read of a named register from a literal is the field. The projections
of the machine record, the `UInt64` round trip and reassociation present
adjacent literals to `evalGround`, so a chain of ground arithmetic and its
flags fold while `vcgen` steps. A return address read from the slot that a
push wrote is the pushed value. The rewrite set is the `@[vcgen_simp]` set.
The lemmas about the machine state carry the attribute globally. The generic
library lemmas carry it scoped to the namespace `KVCGen`, which `kvcgen64` opens.
-/
public import Kraken.X64.Registers
public import Std.Tactic.Do.Syntax
public meta import Lean.Elab.Tactic

public section

namespace KVCGen

/-- Reassociation, so a chain of additions over a symbolic start presents
adjacent literals to `evalGround`. -/
@[scoped vcgen_simp] theorem _root_.BitVec.add_assoc_rev {w : Nat} (a b c : BitVec w) : a + (b + c) = a + b + c :=
  (BitVec.add_assoc a b c).symm

@[scoped vcgen_simp] theorem _root_.BitVec.add_ofNat_zero {w : Nat} (x : BitVec w) : x + (0 : BitVec w) = x :=
  BitVec.add_zero x

attribute [scoped vcgen_simp] UInt64.toBitVec_ofBitVec Int64.toBitVec_ofNat BitVec.ofNat_eq_ofNat
  BitVec.setWidth_eq BitVec.add_zero BitVec.toNat_ofNat Nat.zero_mod Int.add_zero Int.cast_ofNat_Int
  bne_self_eq_false BitVec.xor_self Bool.toNat_false Option.map_some Option.get!_some Option.isSome_some

end KVCGen

@[vcgen_simp] theorem MachineState.data_mk (d : MachineData) (pc : Int64) : (⟨d, pc⟩ : MachineState).data = d := rfl

/-- `vcgen` with the register state folded. -/
syntax (name := kvcgen64) "kvcgen64" (" [" term,* "]")? (" with " vcgenDischarge)? : tactic

syntax (name := cfgExit) "cfg_exit" : grind

macro_rules
  | `(grind| cfg_exit) => `(grind| skip)

macro_rules
  | `(tactic| kvcgen64 $[[$ids,*]]? $[with $d]?) => do
    let lemmas ← (ids.map (·.getElems) |>.getD #[]).mapM fun i =>
      `(Lean.Parser.Tactic.simpLemma| $i:term)
    let d ← d.mapM fun (d₀ : Lean.TSyntax `vcgenDischarge) => match d₀ with
      | `(vcgenDischarge| $g:grind) =>
        `(vcgenDischarge| (cfg_exit; $g:grind))
      | _ => pure d₀
    `(tactic| open KVCGen in vcgen [$lemmas,*] $[with $d]?)
