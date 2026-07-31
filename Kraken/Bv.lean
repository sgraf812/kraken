/-
`Bv n`, the machine value of `n` bits, and its lemma kit.

The bit representation is reached through `toBitVec`/`ofBitVec`, so a value and
its bits are terms of different types and every crossing is a constructor or a
projection in the term. Arithmetic and comparisons are the `BitVec n` ones
transported across the wrapper; each is characterized by an equation pushing
`toBitVec` inwards.
-/
import Lean
import Std

/-- A machine value of `n` bits. -/
structure Bv (n : Nat) where
  /-- Wraps the bits of a machine value. -/
  ofBitVec ::
  /-- The bits of a machine value. -/
  toBitVec : BitVec n
  deriving DecidableEq, Repr, Hashable

namespace Bv

variable {n : Nat} {a b : Bv n} {x y : BitVec n}

instance : Inhabited (Bv n) := ⟨.ofBitVec 0⟩
instance : Add (Bv n) := ⟨fun a b => .ofBitVec (a.toBitVec + b.toBitVec)⟩
instance : Sub (Bv n) := ⟨fun a b => .ofBitVec (a.toBitVec - b.toBitVec)⟩
instance : Mul (Bv n) := ⟨fun a b => .ofBitVec (a.toBitVec * b.toBitVec)⟩
instance : Neg (Bv n) := ⟨fun a => .ofBitVec (-a.toBitVec)⟩
instance : Complement (Bv n) := ⟨fun a => .ofBitVec (~~~a.toBitVec)⟩
instance : AndOp (Bv n) := ⟨fun a b => .ofBitVec (a.toBitVec &&& b.toBitVec)⟩
instance : OrOp (Bv n) := ⟨fun a b => .ofBitVec (a.toBitVec ||| b.toBitVec)⟩
instance : XorOp (Bv n) := ⟨fun a b => .ofBitVec (a.toBitVec ^^^ b.toBitVec)⟩
instance {i : Nat} : OfNat (Bv n) i := ⟨.ofBitVec (BitVec.ofNat n i)⟩
instance : LE (Bv n) := ⟨fun a b => a.toBitVec ≤ b.toBitVec⟩
instance : LT (Bv n) := ⟨fun a b => a.toBitVec < b.toBitVec⟩

/-- The bits of a machine value are reached by coercion, so a mixed expression
elaborates with the projection in the term rather than by unfolding a type. -/
instance : CoeOut (Bv n) (BitVec n) := ⟨Bv.toBitVec⟩
attribute [coe] Bv.toBitVec

/-! ## Wrapping and unwrapping -/

@[simp] theorem toBitVec_ofBitVec : (Bv.ofBitVec x).toBitVec = x := rfl
@[simp] theorem ofBitVec_toBitVec : Bv.ofBitVec a.toBitVec = a := rfl

theorem toBitVec_eq_of_eq (h : a = b) : a.toBitVec = b.toBitVec := h ▸ rfl
theorem eq_of_toBitVec_eq (h : a.toBitVec = b.toBitVec) : a = b := by cases a; cases b; simp_all
theorem toBitVec_inj : a.toBitVec = b.toBitVec ↔ a = b := ⟨eq_of_toBitVec_eq, toBitVec_eq_of_eq⟩

theorem eq_iff_toBitVec_eq : a = b ↔ a.toBitVec = b.toBitVec :=
  ⟨toBitVec_eq_of_eq, eq_of_toBitVec_eq⟩
theorem ne_iff_toBitVec_ne : a ≠ b ↔ a.toBitVec ≠ b.toBitVec :=
  ⟨fun h h' => h (eq_of_toBitVec_eq h'), fun h h' => h (toBitVec_eq_of_eq h')⟩

/-! ## Arithmetic

Each operation is the `BitVec` one under the wrapper, in both directions: the
`toBitVec_` equations push a projection through an operation, the `ofBitVec_`
equations pull a constructor out of one. -/

@[simp, grind =] theorem toBitVec_add : (a + b).toBitVec = a.toBitVec + b.toBitVec := rfl
@[simp, grind =] theorem toBitVec_sub : (a - b).toBitVec = a.toBitVec - b.toBitVec := rfl
@[simp, grind =] theorem toBitVec_mul : (a * b).toBitVec = a.toBitVec * b.toBitVec := rfl
@[simp, grind =] theorem toBitVec_neg : (-a).toBitVec = -a.toBitVec := rfl
@[simp, grind =] theorem toBitVec_not : (~~~a).toBitVec = ~~~a.toBitVec := rfl
@[simp, grind =] theorem toBitVec_and : (a &&& b).toBitVec = a.toBitVec &&& b.toBitVec := rfl
@[simp, grind =] theorem toBitVec_or : (a ||| b).toBitVec = a.toBitVec ||| b.toBitVec := rfl
@[simp] theorem toBitVec_xor : (a ^^^ b).toBitVec = a.toBitVec ^^^ b.toBitVec := rfl

@[simp] theorem toBitVec_ofNat {i : Nat} :
    (no_index (OfNat.ofNat i) : Bv n).toBitVec = BitVec.ofNat n i := rfl

@[grind =] theorem ofBitVec_add : Bv.ofBitVec (x + y) = .ofBitVec x + .ofBitVec y := rfl
@[grind =] theorem ofBitVec_sub : Bv.ofBitVec (x - y) = .ofBitVec x - .ofBitVec y := rfl
@[grind =] theorem ofBitVec_mul : Bv.ofBitVec (x * y) = .ofBitVec x * .ofBitVec y := rfl
@[grind =] theorem ofBitVec_neg : Bv.ofBitVec (-x) = -(.ofBitVec x) := rfl
theorem ofBitVec_ofNat {i : Nat} :
    Bv.ofBitVec (BitVec.ofNat n i) = (OfNat.ofNat i : Bv n) := rfl

/-! ## Comparisons -/

theorem le_iff_toBitVec_le : a ≤ b ↔ a.toBitVec ≤ b.toBitVec := .rfl
theorem lt_iff_toBitVec_lt : a < b ↔ a.toBitVec < b.toBitVec := .rfl

instance : BEq (Bv n) := ⟨fun a b => a.toBitVec == b.toBitVec⟩
instance : LawfulBEq (Bv n) where
  eq_of_beq h := eq_of_toBitVec_eq (eq_of_beq h)
  rfl := beq_self_eq_true' _

@[simp] theorem beq_iff_toBitVec_beq : (a == b) = (a.toBitVec == b.toBitVec) := rfl

end Bv
