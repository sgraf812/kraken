module

/-
The register read-over-write API the spec framework discharges against:
register reads over `set64` (both the indexed `get64` and the per-field
accessors), the `MachineData` record projections, and the
`StatusFlags`/`BitVec` reductions the flag and address arithmetic normalize
with.
-/
public import Kraken.X64.OmniSemantics
public import Kraken.X64.Registers
public import Kraken.GrindFold
public import Std.Tactic.Do
public import Std.WP
import Std.Tactic.BVDecide

@[expose] public section

open Std.WP

set_option mvcgen.warning false
set_option grind.warning false

/-! ## Address spelling -/

/-- The baseline address semantics at 64-bit address size, with the label table
explicit. The explicit argument keeps every subterm rewritable (`simp`'s
congruence holds an instance-implicit argument fixed, so a state equation never
reaches a label table passed as an instance), and the literal `BitVec 64`
result is the width spelling the proof engines read. -/
def AddrExpr.interp64 (labels : Labels) (a : AddrExpr) (s : Reg64s) (p : Std.Rco Int64) : BitVec 64 :=
  @AddrExpr.interp labels (.mk .W64) a s p

/-! ## `.unsigned`/`.signed` reductions -/
@[grind hom] theorem BitVec.unsigned_hom {w} (x : BitVec w) : x.unsigned = (x.toNat : Int) := rfl

@[simp, grind =] theorem StatusFlags.sf_from_result {w} (v : BitVec w)
    (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result v f).sf = v.msb := rfl

@[simp, grind =] theorem StatusFlags.of_from_result {w} (v : BitVec w)
    (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result v f).of = f.of := rfl

/-! ## Condition-code reductions, one lemma per code -/

/-! ## Reading a named register, one lemma per field -/


/-! ## Register identity as a number

The state-simplification pass reduces ground terms of the builtin types, so a
read-over-write condition is stated between register indices: the index of a
named register is a numeral, and the pass decides the comparison and takes the
branch. -/

def Reg64.idx : Reg64 → Nat
  | .rax => 0  | .rbx => 1  | .rcx => 2  | .rdx => 3
  | .rsi => 4  | .rdi => 5  | .rsp => 6  | .rbp => 7
  | .r8  => 8  | .r9  => 9  | .r10 => 10 | .r11 => 11
  | .r12 => 12 | .r13 => 13 | .r14 => 14 | .r15 => 15

theorem Reg64.eq_eq_idx_eq (r r' : Reg64) : (r = r') = (r.idx = r'.idx) := by
  cases r <;> cases r' <;> simp [Reg64.idx]

/-! ## Register read-over-write API

Register reads are characterized by rewriting, so discharging queries only the
registers the postcondition mentions and a state literal's register file is
never unfolded. -/

attribute [grind =] Width.bytes

@[simp, grind =] theorem Width.bytesv_W64 {n : Nat} :
    (Width.W64).bytesv (n := n) = BitVec.ofNat n 8 := rfl

@[simp, grind =] theorem Reg64s.set64_set64 (s : Reg64s) (r : Reg64) (v w : BitVec 64) :
    (s.set64 r v).set64 r w = s.set64 r w := by
  cases r <;> simp [Reg64s.set64]

@[simp, grind =] theorem Reg64s.set64_get64 (s : Reg64s) (r : Reg64) :
    s.set64 r (s.get64 r) = s := by
  cases r <;> simp [Reg64s.set64, Reg64s.get64]

@[simp, grind =] theorem Reg64s.get64_set64 (s : Reg64s) (r r' : Reg64) (v : BitVec 64) :
    (s.set64 r v).get64 r' = if r' = r then v else s.get64 r' := by
  cases r <;> cases r' <;> simp [Reg64s.set64, Reg64s.get64]

@[simp, grind =] theorem Reg64s.get_low64 (s : Reg64s) (r : Reg64) :
    s.get (.low r .W64) = s.get64 r := by
  simp [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop]

/-- A 32-bit read is the low half of the 64-bit register. A `grind` rule only,
so the simp normal form of a 32-bit read is unchanged. -/
@[grind =] theorem Reg64s.get_low32 (s : Reg64s) (r : Reg64) :
    s.get (.low r .W32) = (s.get64 r).setWidth 32 := by
  simp only [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth]

@[simp, grind =] theorem Reg64s.set_low64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    Reg64s.set s (.low r .W64) v = s.set64 r v := rfl

/-- An 8-bit read is the low byte of the 64-bit register. A `grind` rule only,
like `get_low32`. -/
@[grind =] theorem Reg64s.get_low8 (s : Reg64s) (r : Reg64) :
    s.get (.low r .W8) = (s.get64 r).setWidth 8 := by
  simp only [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth]

/-- A 32-bit write zero-extends into the 64-bit register. -/
@[simp, grind =] theorem Reg64s.set_low32 (s : Reg64s) (r : Reg64) (v : BitVec 32) :
    Reg64s.set s (.low r .W32) v = s.set64 r (v.setWidth 64) := rfl

/-- An 8-bit write replaces the low byte and keeps the rest. -/
@[simp, grind =] theorem Reg64s.set_low8 (s : Reg64s) (r : Reg64) (v : BitVec 8) :
    Reg64s.set s (.low r .W8) v = s.set64 r ((s.get64 r).replaceLow v) := rfl

/-- The low byte after an 8-bit write is the byte written. -/
@[grind =] theorem BitVec.toNat_replaceLow8_mod (old : BitVec 64) (new : BitVec 8) :
    (old.replaceLow new).toNat % 256 = new.toNat := by
  have h : (old.replaceLow new).setWidth 8 = new := by
    simp only [BitVec.replaceLow, BitVec.drop]
    bv_decide
  have := congrArg BitVec.toNat h
  simpa [BitVec.toNat_setWidth] using this

/-- The high bytes after an 8-bit write are the old ones. -/
@[grind =] theorem BitVec.toNat_replaceLow8_div (old : BitVec 64) (new : BitVec 8) :
    (old.replaceLow new).toNat / 256 = old.toNat / 256 := by
  have h : (old.replaceLow new) >>> 8 = old >>> 8 := by
    simp only [BitVec.replaceLow, BitVec.drop]
    bv_decide
  have := congrArg BitVec.toNat h
  simpa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using this

/-- An 8-bit read after an 8-bit write is the byte written. -/
@[simp, grind =] theorem BitVec.setWidth_replaceLow8 (old : BitVec 64) (new : BitVec 8) :
    (old.replaceLow new).setWidth 8 = new := by
  simp only [BitVec.replaceLow, BitVec.drop]
  bv_decide

/-! A value stored as `n` bytes and loaded back is the value, at the width of
the register it goes into. Instances of `BitVec.ofInt_ofBytes_toBytes_eq` at
the widths the instruction rules produce, so `grind` sees through
store-then-load without being told the width. -/

@[grind =] theorem BitVec.ofInt8_ofBytes_toBytes1 (v : Int) :
    BitVec.ofInt 8 (Int.ofBytes (Int.toBytes 1 v)) = BitVec.ofInt 8 v :=
  BitVec.ofInt_ofBytes_toBytes_eq 8 1 rfl v
@[grind =] theorem BitVec.ofInt32_ofBytes_toBytes4 (v : Int) :
    BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 v)) = BitVec.ofInt 32 v :=
  BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl v
@[grind =] theorem BitVec.ofInt64_ofBytes_toBytes8 (v : Int) :
    BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 v)) = BitVec.ofInt 64 v :=
  BitVec.ofInt_ofBytes_toBytes_eq 64 8 rfl v

attribute [grind =] BitVec.ofInt_toInt BitVec.toNat_setWidth

/-! `and al, 1` and the byte it leaves: a compiler's way of making a `bool`
well-formed. The low bit of a byte, as a natural number and as the integer
a store of the byte writes; and an integer that came from a natural number,
read back as a byte. -/

@[grind =] theorem BitVec.toNat_and_one (x : BitVec 8) : (x &&& 1#8).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and]; exact Nat.and_one_is_mod _

@[grind =] theorem BitVec.toInt_setWidth8_and_one (x : BitVec 64) :
    ((x.setWidth 8 &&& 1#8).toInt) = ((x.toNat % 2 : Nat) : Int) := by
  have h := BitVec.toNat_and_one (x.setWidth 8)
  rw [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd _ (by decide)] at h
  rw [BitVec.toInt_eq_toNat_of_msb, h]
  rw [BitVec.msb_eq_decide, decide_eq_false_iff_not, Nat.not_le]
  omega

/-- As an integer equation on any `v`: `grind` normalises casts inward
(`↑((n + 1) % 2)` becomes `(↑n + 1) % 2`), so a statement keyed on
`BitVec.ofInt 8 ↑k` would not be found. -/
@[grind =] theorem BitVec.natCast_toNat_ofInt8 (v : Int) :
    ((BitVec.ofInt 8 v).toNat : Int) = v % 256 := by
  rw [BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))]
  rfl

@[simp, grind =] theorem MachineData.regs_setReg (s : MachineData) {w} (r : Reg w) (v : w.type) :
    (s.setReg r v).regs = s.regs.set r v := rfl
@[simp, grind =] theorem MachineData.status_setReg (s : MachineData) {w} (r : Reg w) (v : w.type) :
    (s.setReg r v).status = s.status := rfl
@[simp, grind =] theorem MachineData.dmem_setReg (s : MachineData) {w} (r : Reg w) (v : w.type) :
    (s.setReg r v).dmem = s.dmem := rfl
@[simp, grind =] theorem MachineData.zmms_setReg (s : MachineData) {w} (r : Reg w) (v : w.type) :
    (s.setReg r v).zmms = s.zmms := rfl


/-! ## Machine words in `grind`'s arithmetic

A register holds a `UInt64` whose payload is a `BitVec 64`, and the instruction
semantics moves between the two spellings and back through `Nat`. Each equation
below is one crossing that `grind` cannot take on its own: the three reductions
a wrapping subtraction and a double-width product need once the result is known
to fit. -/

@[grind =] theorem BitVec.toNat_sub_le {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)

@[grind =] theorem BitVec.toNat_ofInt_mul {a b : BitVec 64}
    (h : a.toNat * b.toNat < 2 ^ 64) :
    (BitVec.ofInt 64 ((a.toNat : Int) * (b.toNat : Int))).toNat = a.toNat * b.toNat := by
  rw [← Int.natCast_mul, BitVec.ofInt_natCast]
  simp [Nat.mod_eq_of_lt h]

@[grind =] theorem BitVec.ofInt_mul_shiftRight {a b : BitVec 64}
    (h : a.toNat * b.toNat < 2 ^ 64) :
    BitVec.ofInt 64 (((a.toNat : Int) * (b.toNat : Int)) >>> 64) = 0#64 := by
  rw [← Int.natCast_mul, ← Int.natCast_shiftRight, Nat.shiftRight_eq_div_pow,
    Nat.div_eq_of_lt h]
  simp

@[grind =] theorem Int64.ofNat_lit (n : Nat) : (OfNat.ofNat n : Int64) = Int64.ofNat n := rfl
@[grind =] theorem Int64.toBitVec_lit (n : Nat) :
    (OfNat.ofNat n : Int64).toBitVec = BitVec.ofNat 64 n := rfl
@[grind =] theorem BitVec.setWidth_64_64 (x : BitVec 64) :
    BitVec.setWidth 64 x = x := BitVec.setWidth_eq x
@[simp, grind =] theorem BitVec.ofInt_toInt_int64 (c : Int64) :
    BitVec.ofInt 64 c.toInt = c.toBitVec := by
  rw [show c.toInt = c.toBitVec.toInt from rfl, BitVec.ofInt_toInt]

/-- An immediate reaches `grind` as the payload of an `Int64` literal. This
rule rewrites the payload to a `BitVec` literal, so that shift counts,
displacements and masks are numerals to the arithmetic (`no_index` lets it
match the numeral). `MachineWP` registers it with `grind`'s normalizer. -/
theorem Int64.toBitVec_ofNat_norm (n : Nat) :
    (no_index (OfNat.ofNat n : Int64)).toBitVec = BitVec.ofNat 64 n := rfl

/-- A negative immediate, likewise: the parser writes it as the negation of a
literal. -/
theorem Int64.toBitVec_neg_ofNat_norm (n : Nat) :
    (-(no_index (OfNat.ofNat n : Int64))).toBitVec
      = BitVec.ofNat 64 (2 ^ 64 - n % 2 ^ 64) := by
  rw [Int64.toBitVec_neg, Int64.toBitVec_ofNat_norm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_neg, BitVec.toNat_ofNat]

/-! ## Per-register field reads over `set64`, one lemma per field -/

@[simp, grind =] theorem Reg64s.rax_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).rax = if r = .rax then .ofBitVec v else s.rax := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rbx_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).rbx = if r = .rbx then .ofBitVec v else s.rbx := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rcx_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).rcx = if r = .rcx then .ofBitVec v else s.rcx := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rdx_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).rdx = if r = .rdx then .ofBitVec v else s.rdx := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rsi_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).rsi = if r = .rsi then .ofBitVec v else s.rsi := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rdi_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).rdi = if r = .rdi then .ofBitVec v else s.rdi := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rsp_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).rsp = if r = .rsp then .ofBitVec v else s.rsp := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rbp_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).rbp = if r = .rbp then .ofBitVec v else s.rbp := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r8_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).r8 = if r = .r8 then .ofBitVec v else s.r8 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r9_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).r9 = if r = .r9 then .ofBitVec v else s.r9 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r10_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).r10 = if r = .r10 then .ofBitVec v else s.r10 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r11_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).r11 = if r = .r11 then .ofBitVec v else s.r11 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r12_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).r12 = if r = .r12 then .ofBitVec v else s.r12 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r13_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).r13 = if r = .r13 then .ofBitVec v else s.r13 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r14_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).r14 = if r = .r14 then .ofBitVec v else s.r14 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r15_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).r15 = if r = .r15 then .ofBitVec v else s.r15 := by cases r <;> simp [Reg64s.set64]
