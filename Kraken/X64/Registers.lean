module

/-
Register reads and writes at named registers. A read of a named register is
the field, a `.low r .W64` access is the 64-bit access, and a write to a
named register is a structure update. `vcgen` folds the register state with
the write equations, so a read after a block of writes is a projection of
one register literal.
-/
public import Kraken.X64.Semantics

public section

/-! ## Reading a named register, one lemma per field -/

@[simp, grind norm] theorem Reg64s.get64_rax (s : Reg64s) : s.get64 .rax = s.rax.toBitVec := rfl
@[simp, grind norm] theorem Reg64s.get64_rbx (s : Reg64s) : s.get64 .rbx = s.rbx.toBitVec := rfl
@[simp, grind norm] theorem Reg64s.get64_rcx (s : Reg64s) : s.get64 .rcx = s.rcx.toBitVec := rfl
@[simp, grind norm] theorem Reg64s.get64_rdx (s : Reg64s) : s.get64 .rdx = s.rdx.toBitVec := rfl
@[simp, grind norm] theorem Reg64s.get64_rsi (s : Reg64s) : s.get64 .rsi = s.rsi.toBitVec := rfl
@[simp, grind norm] theorem Reg64s.get64_rdi (s : Reg64s) : s.get64 .rdi = s.rdi.toBitVec := rfl
@[simp, grind norm] theorem Reg64s.get64_rsp (s : Reg64s) : s.get64 .rsp = s.rsp.toBitVec := rfl
@[simp, grind norm] theorem Reg64s.get64_rbp (s : Reg64s) : s.get64 .rbp = s.rbp.toBitVec := rfl
@[simp, grind norm] theorem Reg64s.get64_r8 (s : Reg64s) : s.get64 .r8 = s.r8.toBitVec := rfl
@[simp, grind norm] theorem Reg64s.get64_r9 (s : Reg64s) : s.get64 .r9 = s.r9.toBitVec := rfl
@[simp, grind norm] theorem Reg64s.get64_r10 (s : Reg64s) : s.get64 .r10 = s.r10.toBitVec := rfl
@[simp, grind norm] theorem Reg64s.get64_r11 (s : Reg64s) : s.get64 .r11 = s.r11.toBitVec := rfl
@[simp, grind norm] theorem Reg64s.get64_r12 (s : Reg64s) : s.get64 .r12 = s.r12.toBitVec := rfl
@[simp, grind norm] theorem Reg64s.get64_r13 (s : Reg64s) : s.get64 .r13 = s.r13.toBitVec := rfl
@[simp, grind norm] theorem Reg64s.get64_r14 (s : Reg64s) : s.get64 .r14 = s.r14.toBitVec := rfl
@[simp, grind norm] theorem Reg64s.get64_r15 (s : Reg64s) : s.get64 .r15 = s.r15.toBitVec := rfl

/-! ## The 64-bit access of a register -/

@[simp, grind =] theorem Reg64s.get_low_W64 (s : Reg64s) (r : Reg64) :
    s.get (.low r .W64) = s.get64 r := by
  simp [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop]

@[simp, grind =] theorem Reg64s.set_low_W64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    Reg64s.set s (.low r .W64) v = s.set64 r v := rfl

/-! ## A write to a part of a register as a 64-bit write -/

theorem Reg64s.set_low_W32 (s : Reg64s) (r : Reg64) (v : BitVec 32) :
    Reg64s.set s (.low r .W32) v = s.set64 r (v.zeroExtend 64) := rfl

theorem Reg64s.set_low_W16 (s : Reg64s) (r : Reg64) (v : BitVec 16) :
    Reg64s.set s (.low r .W16) v = s.set64 r ((s.get64 r).replaceLow v) := rfl

theorem Reg64s.set_low_W8 (s : Reg64s) (r : Reg64) (v : BitVec 8) :
    Reg64s.set s (.low r .W8) v = s.set64 r ((s.get64 r).replaceLow v) := rfl

theorem Reg64s.set_ah (s : Reg64s) (v : BitVec 8) :
    Reg64s.set s .ah v = s.set64 .rax ((s.get64 .rax).replaceLow (BitVec.append v (s.get (.low .rax .W8)))) := rfl

theorem Reg64s.set_bh (s : Reg64s) (v : BitVec 8) :
    Reg64s.set s .bh v = s.set64 .rbx ((s.get64 .rbx).replaceLow (BitVec.append v (s.get (.low .rbx .W8)))) := rfl

theorem Reg64s.set_ch (s : Reg64s) (v : BitVec 8) :
    Reg64s.set s .ch v = s.set64 .rcx ((s.get64 .rcx).replaceLow (BitVec.append v (s.get (.low .rcx .W8)))) := rfl

theorem Reg64s.set_dh (s : Reg64s) (v : BitVec 8) :
    Reg64s.set s .dh v = s.set64 .rdx ((s.get64 .rdx).replaceLow (BitVec.append v (s.get (.low .rdx .W8)))) := rfl

theorem Reg64s.get_low_W32 (s : Reg64s) (r : Reg64) :
    s.get (.low r .W32) = (s.get64 r).take 32 := by
  simp [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop]

theorem Reg64s.get_low_W16 (s : Reg64s) (r : Reg64) :
    s.get (.low r .W16) = (s.get64 r).take 16 := by
  simp [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop]

theorem Reg64s.get_low_W8 (s : Reg64s) (r : Reg64) :
    s.get (.low r .W8) = (s.get64 r).take 8 := by
  simp [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop]

private theorem BitVec.take_replaceLow {w n : Nat} (x : BitVec w) (v : BitVec n) (h : n ≤ w) :
    (x.replaceLow v).take n = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.replaceLow, BitVec.take, BitVec.getLsbD_append, hi, show i < w by omega]

theorem BitVec.take_replaceLow_8 (x : BitVec 64) (v : BitVec 8) : (x.replaceLow v).take 8 = v :=
  BitVec.take_replaceLow x v (by decide)

theorem BitVec.take_replaceLow_16 (x : BitVec 64) (v : BitVec 16) : (x.replaceLow v).take 16 = v :=
  BitVec.take_replaceLow x v (by decide)

theorem BitVec.take_zeroExtend_32 (v : BitVec 32) : (v.zeroExtend 64).take 32 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.take, hi]
  omega

/-! ## A write to a named register as a structure update

`vcgen` rewrites the register state it threads with these equations, so a
block of writes folds into one register literal and every later read is a
projection of that literal. -/

theorem Reg64s.set64_rax (s : Reg64s) (v : BitVec 64) :
    s.set64 .rax v = { s with rax := .ofBitVec v } := rfl
theorem Reg64s.set64_rbx (s : Reg64s) (v : BitVec 64) :
    s.set64 .rbx v = { s with rbx := .ofBitVec v } := rfl
theorem Reg64s.set64_rcx (s : Reg64s) (v : BitVec 64) :
    s.set64 .rcx v = { s with rcx := .ofBitVec v } := rfl
theorem Reg64s.set64_rdx (s : Reg64s) (v : BitVec 64) :
    s.set64 .rdx v = { s with rdx := .ofBitVec v } := rfl
theorem Reg64s.set64_rsi (s : Reg64s) (v : BitVec 64) :
    s.set64 .rsi v = { s with rsi := .ofBitVec v } := rfl
theorem Reg64s.set64_rdi (s : Reg64s) (v : BitVec 64) :
    s.set64 .rdi v = { s with rdi := .ofBitVec v } := rfl
theorem Reg64s.set64_rsp (s : Reg64s) (v : BitVec 64) :
    s.set64 .rsp v = { s with rsp := .ofBitVec v } := rfl
theorem Reg64s.set64_rbp (s : Reg64s) (v : BitVec 64) :
    s.set64 .rbp v = { s with rbp := .ofBitVec v } := rfl
theorem Reg64s.set64_r8 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r8 v = { s with r8 := .ofBitVec v } := rfl
theorem Reg64s.set64_r9 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r9 v = { s with r9 := .ofBitVec v } := rfl
theorem Reg64s.set64_r10 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r10 v = { s with r10 := .ofBitVec v } := rfl
theorem Reg64s.set64_r11 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r11 v = { s with r11 := .ofBitVec v } := rfl
theorem Reg64s.set64_r12 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r12 v = { s with r12 := .ofBitVec v } := rfl
theorem Reg64s.set64_r13 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r13 v = { s with r13 := .ofBitVec v } := rfl
theorem Reg64s.set64_r14 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r14 v = { s with r14 := .ofBitVec v } := rfl
theorem Reg64s.set64_r15 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r15 v = { s with r15 := .ofBitVec v } := rfl

/-! ## Register-file literals

A write to a named register rebuilds the register file as a literal
(`set64_rax` and its siblings). A read of a named register from a literal is
its field: `get64_rax` and its siblings turn the read into a projection, and
the projections of a literal reduce by the lemmas below. -/

@[simp] theorem Reg64s.rax_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).rax = a0 := rfl
@[simp] theorem Reg64s.rbx_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).rbx = a1 := rfl
@[simp] theorem Reg64s.rcx_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).rcx = a2 := rfl
@[simp] theorem Reg64s.rdx_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).rdx = a3 := rfl
@[simp] theorem Reg64s.rsi_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).rsi = a4 := rfl
@[simp] theorem Reg64s.rdi_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).rdi = a5 := rfl
@[simp] theorem Reg64s.rsp_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).rsp = a6 := rfl
@[simp] theorem Reg64s.rbp_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).rbp = a7 := rfl
@[simp] theorem Reg64s.r8_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).r8 = a8 := rfl
@[simp] theorem Reg64s.r9_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).r9 = a9 := rfl
@[simp] theorem Reg64s.r10_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).r10 = a10 := rfl
@[simp] theorem Reg64s.r11_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).r11 = a11 := rfl
@[simp] theorem Reg64s.r12_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).r12 = a12 := rfl
@[simp] theorem Reg64s.r13_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).r13 = a13 := rfl
@[simp] theorem Reg64s.r14_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).r14 = a14 := rfl
@[simp] theorem Reg64s.r15_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).r15 = a15 := rfl

/-! ## The machine record and the flags -/

@[simp] theorem MachineData.regs_mk (r z st d) : (MachineData.mk r z st d).regs = r := rfl
@[simp] theorem MachineData.dmem_mk (r z st d) : (MachineData.mk r z st d).dmem = d := rfl
@[simp] theorem MachineData.status_mk (r z st d) : (MachineData.mk r z st d).status = st := rfl
@[simp] theorem MachineData.zmms_mk (r z st d) : (MachineData.mk r z st d).zmms = z := rfl

@[simp] theorem BitVec.unsigned_eq {w} (x : BitVec w) : x.unsigned = (x.toNat : Int) := rfl

@[simp] theorem BitVec.signed_eq {w} (x : BitVec w) : x.signed = x.toInt := rfl

@[simp, grind =] theorem StatusFlags.cf_from_result {w} (v : BitVec w)
    (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result v f).cf = f.cf := rfl

@[simp] theorem StatusFlags.from_result.Remaining.cf_mk (c a o : Bool) :
    (StatusFlags.from_result.Remaining.mk c a o).cf = c := rfl

@[simp, grind =] theorem StatusFlags.zf_from_result {w} (v : BitVec w)
    (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result v f).zf = (v == BitVec.zero w) := rfl

@[simp, grind =] theorem CondCode.interp_z (s : StatusFlags) :
    CondCode.z.interp s = s.zf := rfl
@[simp, grind =] theorem CondCode.interp_nz (s : StatusFlags) :
    CondCode.nz.interp s = !s.zf := rfl
@[simp, grind =] theorem CondCode.interp_c (s : StatusFlags) :
    CondCode.c.interp s = s.cf := rfl
@[simp, grind =] theorem CondCode.interp_nc (s : StatusFlags) :
    CondCode.nc.interp s = !s.cf := rfl
@[simp, grind =] theorem CondCode.interp_a (s : StatusFlags) :
    CondCode.a.interp s = (!s.cf && !s.zf) := rfl
@[simp, grind =] theorem CondCode.interp_be (s : StatusFlags) :
    CondCode.be.interp s = (s.cf || s.zf) := rfl
@[simp] theorem CondCode.interp_l (s : StatusFlags) :
    CondCode.l.interp s = (s.sf != s.of) := rfl
@[simp] theorem CondCode.interp_le (s : StatusFlags) :
    CondCode.le.interp s = ((s.sf != s.of) || s.zf) := rfl
@[simp] theorem CondCode.interp_ge (s : StatusFlags) :
    CondCode.ge.interp s = (s.sf == s.of) := rfl
@[simp] theorem CondCode.interp_g (s : StatusFlags) :
    CondCode.g.interp s = (!s.zf && (s.sf == s.of)) := rfl

/-! ## Signed comparisons -/

@[expose] def StatusFlags.neg (s : StatusFlags) : Bool := s.sf != s.of

@[simp] theorem StatusFlags.neg_eq (s : StatusFlags) : s.neg = (s.sf != s.of) := rfl

@[grind =] theorem CondCode.interp_l_neg (s : StatusFlags) : CondCode.l.interp s = s.neg := rfl
@[grind =] theorem CondCode.interp_ge_neg (s : StatusFlags) :
    CondCode.ge.interp s = !s.neg := by
  simp only [CondCode.interp_ge, StatusFlags.neg]; cases s.sf <;> cases s.of <;> rfl
@[grind =] theorem CondCode.interp_le_neg (s : StatusFlags) :
    CondCode.le.interp s = (s.neg || s.zf) := rfl
@[grind =] theorem CondCode.interp_g_neg (s : StatusFlags) :
    CondCode.g.interp s = (!s.neg && !s.zf) := by
  simp only [CondCode.interp_g, StatusFlags.neg]
  cases s.sf <;> cases s.of <;> cases s.zf <;> rfl

theorem BitVec.toInt_lt_toInt_iff_flip (a b : BitVec 64) :
    a.toInt < b.toInt ↔ (a.toNat + 2 ^ 63) % 2 ^ 64 < (b.toNat + 2 ^ 63) % 2 ^ 64 := by
  have ha := a.isLt
  have hb := b.isLt
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  split <;> split <;> omega

theorem BitVec.toInt_neg_ofNat_of_ne (n : Nat) (hn : n % 2 ^ 64 ≠ 2 ^ 63) :
    (-(OfNat.ofNat n : BitVec 64)).toInt = -(OfNat.ofNat n : BitVec 64).toInt := by
  apply BitVec.toInt_neg_of_ne_intMin
  intro h; apply hn; rw [← BitVec.toNat_ofNat n 64, show BitVec.ofNat 64 n = OfNat.ofNat n from rfl, h]
  simp [BitVec.toNat_intMin]

/-! ## Unsigned comparisons -/

theorem BitVec.toNat_sub_cases {w} (a b : BitVec w) :
    (b.toNat ≤ a.toNat → (a - b).toNat = a.toNat - b.toNat)
    ∧ (a.toNat < b.toNat → (a - b).toNat = 2 ^ w - b.toNat + a.toNat) := by
  have ha := a.isLt
  have hb := b.isLt
  rw [BitVec.toNat_sub]
  generalize 2 ^ w = d at *
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [show d - b.toNat + a.toNat = (a.toNat - b.toNat) + d by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

/-! ## The flags an instruction leaves -/

@[expose] def StatusFlags.ofSub {w} (a b : BitVec w) : StatusFlags :=
  StatusFlags.from_result (a - b)
    { cf := (a - b).unsigned != a.unsigned - b.unsigned,
      af := ((a - b).take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
      of := (a - b).signed != a.signed - b.signed }

@[expose] def StatusFlags.ofAdd {w} (a b : BitVec w) : StatusFlags :=
  StatusFlags.from_result (a + b)
    { cf := (a + b).unsigned != a.unsigned + b.unsigned,
      af := ((a + b).take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
      of := (a + b).signed != a.signed + b.signed }

@[expose] def StatusFlags.ofDec (a : BitVec 64) (cf : Bool) : StatusFlags :=
  StatusFlags.from_result (a - 1)
    { cf, af := ((a - 1).take 4).unsigned != (a.take 4).unsigned - 1,
      of := (a - 1).signed != a.signed - 1 }

@[expose] def StatusFlags.ofLogic {w} (v : BitVec w) (af : Bool) : StatusFlags :=
  StatusFlags.from_result v { cf := false, of := false, af }

@[simp, grind =] theorem StatusFlags.zf_ofSub {w} (a b : BitVec w) :
    (StatusFlags.ofSub a b).zf = (a - b == BitVec.zero w) := rfl
@[simp, grind =] theorem StatusFlags.cf_ofSub {w} (a b : BitVec w) :
    (StatusFlags.ofSub a b).cf = ((a - b).unsigned != a.unsigned - b.unsigned) := rfl
@[simp] theorem StatusFlags.sf_ofSub {w} (a b : BitVec w) :
    (StatusFlags.ofSub a b).sf = (a - b).msb := rfl
@[simp] theorem StatusFlags.of_ofSub {w} (a b : BitVec w) :
    (StatusFlags.ofSub a b).of = ((a - b).signed != a.signed - b.signed) := rfl
theorem StatusFlags.neg_ofSub (a b : BitVec 64) :
    (StatusFlags.ofSub a b).neg
      = decide ((a.toNat + 2 ^ 63) % 2 ^ 64 < (b.toNat + 2 ^ 63) % 2 ^ 64) := by
  rw [StatusFlags.neg, StatusFlags.sf_ofSub, StatusFlags.of_ofSub]
  have : ((a - b).msb != ((a - b).signed != a.signed - b.signed))
      = decide (a.toInt < b.toInt) := by
    grind [BitVec.signed_eq]
  simp only [this, BitVec.toInt_lt_toInt_iff_flip]
@[grind =] theorem StatusFlags.neg_ofSub_of_lt (a b : BitVec 64)
    (ha : a.toNat < 2 ^ 63) (hb : b.toNat < 2 ^ 63) :
    (StatusFlags.ofSub a b).neg = decide (a.toNat < b.toNat) := by
  rw [StatusFlags.neg_ofSub, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  simp

@[grind =] theorem CondCode.interp_a_ofSub {w} (a b : BitVec w) :
    CondCode.a.interp (StatusFlags.ofSub a b) = decide (b.toNat < a.toNat) := by
  rw [CondCode.interp_a, StatusFlags.cf_ofSub, StatusFlags.zf_ofSub]
  have ⟨h₁, h₂⟩ := BitVec.toNat_sub_cases a b
  have ha := a.isLt
  have hb := b.isLt
  have hz : (a - b == BitVec.zero w) = decide (a.toNat = b.toNat) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.toNat_eq]
    simp only [BitVec.zero_eq, BitVec.toNat_ofNat, Nat.zero_mod]
    generalize 2 ^ w = d at *
    by_cases h : b.toNat ≤ a.toNat
    · rw [h₁ h]; omega
    · rw [h₂ (by omega)]; omega
  rw [hz, BitVec.unsigned_eq, BitVec.unsigned_eq, BitVec.unsigned_eq]
  generalize 2 ^ w = d at *
  by_cases h : b.toNat ≤ a.toNat
  · rw [h₁ h]
    by_cases he : a.toNat = b.toNat
    · simp [he]
    · have : b.toNat < a.toNat := by omega
      simp [he, this]
      omega
  · rw [h₂ (by omega)]
    have : ¬ b.toNat < a.toNat := by omega
    simp [this]
    omega
@[grind =] theorem CondCode.interp_be_ofSub {w} (a b : BitVec w) :
    CondCode.be.interp (StatusFlags.ofSub a b) = decide (a.toNat ≤ b.toNat) := by
  have h := CondCode.interp_a_ofSub a b
  rw [CondCode.interp_a] at h
  rw [CondCode.interp_be]
  revert h
  cases (StatusFlags.ofSub a b).cf <;> cases (StatusFlags.ofSub a b).zf <;> simp <;> omega

@[simp, grind =] theorem StatusFlags.zf_ofAdd {w} (a b : BitVec w) :
    (StatusFlags.ofAdd a b).zf = (a + b == BitVec.zero w) := rfl
@[simp, grind =] theorem StatusFlags.cf_ofAdd {w} (a b : BitVec w) :
    (StatusFlags.ofAdd a b).cf = ((a + b).unsigned != a.unsigned + b.unsigned) := rfl
@[simp] theorem StatusFlags.sf_ofAdd {w} (a b : BitVec w) :
    (StatusFlags.ofAdd a b).sf = (a + b).msb := rfl
@[simp] theorem StatusFlags.of_ofAdd {w} (a b : BitVec w) :
    (StatusFlags.ofAdd a b).of = ((a + b).signed != a.signed + b.signed) := rfl
theorem StatusFlags.neg_ofAdd (n : Nat) (b : BitVec 64) (hn : n % 2 ^ 64 ≠ 2 ^ 63) :
    (StatusFlags.ofAdd (OfNat.ofNat n) b).neg
      = decide ((b.toNat + 2 ^ 63) % 2 ^ 64 < ((2 ^ 64 - n % 2 ^ 64) % 2 ^ 64 + 2 ^ 63) % 2 ^ 64) := by
  have ha : (OfNat.ofNat n : BitVec 64).toNat = n % 2 ^ 64 := BitVec.toNat_ofNat n 64
  rw [StatusFlags.neg, StatusFlags.sf_ofAdd, StatusFlags.of_ofAdd, ← ha, ← BitVec.toNat_neg]
  have : (((OfNat.ofNat n : BitVec 64) + b).msb
        != (((OfNat.ofNat n : BitVec 64) + b).signed
          != (OfNat.ofNat n : BitVec 64).signed + b.signed))
      = decide (b.toInt < (-(OfNat.ofNat n : BitVec 64)).toInt) := by
    rw [BitVec.toInt_neg_ofNat_of_ne n hn]
    grind [BitVec.signed_eq]
  simp only [this, BitVec.toInt_lt_toInt_iff_flip]

grind_pattern StatusFlags.neg_ofAdd => StatusFlags.neg (StatusFlags.ofAdd (OfNat.ofNat n) b)

@[simp, grind =] theorem StatusFlags.zf_ofDec (a : BitVec 64) (cf : Bool) :
    (StatusFlags.ofDec a cf).zf = (a - 1 == BitVec.zero 64) := rfl
@[simp, grind =] theorem StatusFlags.cf_ofDec (a : BitVec 64) (cf : Bool) :
    (StatusFlags.ofDec a cf).cf = cf := rfl

@[simp, grind =] theorem StatusFlags.zf_ofLogic {w} (v : BitVec w) (af : Bool) :
    (StatusFlags.ofLogic v af).zf = (v == BitVec.zero w) := rfl
@[simp, grind =] theorem StatusFlags.cf_ofLogic {w} (v : BitVec w) (af : Bool) :
    (StatusFlags.ofLogic v af).cf = false := rfl
@[simp] theorem StatusFlags.sf_ofLogic {w} (v : BitVec w) (af : Bool) :
    (StatusFlags.ofLogic v af).sf = v.msb := rfl
@[simp] theorem StatusFlags.of_ofLogic {w} (v : BitVec w) (af : Bool) :
    (StatusFlags.ofLogic v af).of = false := rfl
@[grind =] theorem StatusFlags.neg_ofLogic {w} (v : BitVec w) (af : Bool) :
    (StatusFlags.ofLogic v af).neg = v.msb := by
  simp [StatusFlags.neg]

/-! ## Masks -/

theorem Nat.and_two_pow_sub_two_pow {x w k : Nat} (hk : k ≤ w) (hx : x < 2 ^ w) :
    x &&& (2 ^ w - 2 ^ k) = x / 2 ^ k * 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h1 : 2 ^ w - 2 ^ k = 2 ^ k * (2 ^ (w - k) - 1) := by
    rw [Nat.mul_sub, Nat.mul_one, ← Nat.pow_add, Nat.add_sub_cancel' hk]
  rw [h1, Nat.mul_comm (x / 2 ^ k), Nat.testBit_and, Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
  by_cases hik : k ≤ i
  · simp only [ge_iff_le, hik, decide_true, Bool.true_and, Nat.sub_add_cancel hik]
    by_cases hiw : i < w
    · simp [show i - k < w - k by omega]
    · have : x.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this]
  · simp [hik]

theorem Nat.exists_eq_two_pow_of_dvd : ∀ {w n : Nat}, n ∣ 2 ^ w → ∃ k, n = 2 ^ k
  | 0, _, h => ⟨0, Nat.dvd_one.mp h⟩
  | w + 1, n, h => by
    rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
    · obtain ⟨m, rfl⟩ := Nat.dvd_of_mod_eq_zero h2
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ w)] at h
      obtain ⟨k, hk⟩ := Nat.exists_eq_two_pow_of_dvd
        (Nat.dvd_of_mul_dvd_mul_left (show 0 < 2 by decide) h)
      exact ⟨k + 1, by rw [hk, Nat.pow_succ, Nat.mul_comm]⟩
    · have hc : Nat.Coprime n 2 := by
        show Nat.gcd n 2 = 1
        rw [Nat.gcd_comm, Nat.gcd_rec, h2]
        rfl
      rw [Nat.pow_succ] at h
      exact Nat.exists_eq_two_pow_of_dvd (hc.dvd_of_dvd_mul_right h)

theorem BitVec.toNat_ofNat_lit_of_lt {w m : Nat} (hm : m < 2 ^ w) :
    (OfNat.ofNat m : BitVec w).toNat = m := by
  show (BitVec.ofNat w m).toNat = m
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]

theorem BitVec.toNat_and_lowMask_toNat {w : Nat} (x : BitVec w) (m : Nat)
    (h : 2 ^ w % (m + 1) = 0) :
    x.toNat &&& m = x.toNat % (m + 1) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_two_pow_of_dvd (Nat.dvd_of_mod_eq_zero h)
  rw [hk, show m = 2 ^ k - 1 by omega, Nat.and_two_pow_sub_one_eq_mod]

theorem BitVec.toNat_and_highMask_toNat {w : Nat} (x : BitVec w) (m : Nat) (hm : m < 2 ^ w)
    (h : 2 ^ w % (2 ^ w - m) = 0) :
    x.toNat &&& m = x.toNat / (2 ^ w - m) * (2 ^ w - m) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_two_pow_of_dvd (Nat.dvd_of_mod_eq_zero h)
  have hkw : k ≤ w := (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp (by omega)
  rw [hk, show m = 2 ^ w - 2 ^ k by omega]
  exact Nat.and_two_pow_sub_two_pow hkw x.isLt

theorem BitVec.toNat_and_lowMask {w : Nat} (x : BitVec w) (m : Nat) (hm : m < 2 ^ w)
    (h : 2 ^ w % (m + 1) = 0) :
    (x &&& (OfNat.ofNat m : BitVec w)).toNat = x.toNat % (m + 1) := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat_lit_of_lt hm]
  exact BitVec.toNat_and_lowMask_toNat x m h

theorem BitVec.toNat_and_highMask {w : Nat} (x : BitVec w) (m : Nat) (hm : m < 2 ^ w)
    (h : 2 ^ w % (2 ^ w - m) = 0) :
    (x &&& (OfNat.ofNat m : BitVec w)).toNat = x.toNat / (2 ^ w - m) * (2 ^ w - m) := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat_lit_of_lt hm]
  exact BitVec.toNat_and_highMask_toNat x m hm h

grind_pattern BitVec.toNat_and_lowMask => x &&& (OfNat.ofNat m : BitVec w) where
  guard m < 2 ^ w
  guard 2 ^ w % (m + 1) = 0

grind_pattern BitVec.toNat_and_highMask => x &&& (OfNat.ofNat m : BitVec w) where
  guard m < 2 ^ w
  guard 2 ^ w % (2 ^ w - m) = 0

grind_pattern BitVec.toNat_and_lowMask_toNat => x.toNat &&& (OfNat.ofNat m : Nat) where
  guard 2 ^ w % (m + 1) = 0

grind_pattern BitVec.toNat_and_highMask_toNat => x.toNat &&& (OfNat.ofNat m : Nat) where
  guard m < 2 ^ w
  guard 2 ^ w % (2 ^ w - m) = 0

theorem isAligned_iff_dvd {n : Nat} {x : BitVec 64} : isAligned n x = true ↔ n ∣ x.toNat := by
  simp [isAligned, Nat.dvd_iff_mod_eq_zero]

grind_pattern isAligned_iff_dvd => isAligned n x

/-! ## Addresses -/

/-- The address a `disp(base)` expression computes, at 64-bit address size:
the base register plus the displacement. -/
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


theorem AddrExpr.zeroExtend_interp_sib1 [L : Labels] (b i : Reg64) (d : Int64)
    (regs : Reg64s) (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W64)
        (a := ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩) regs rng).zeroExtend 64)
      = regs.get64 b + regs.get64 i + BitVec.ofInt 64 d.toInt := by
  simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize, Reg64s.get64]
  have htake : ∀ x : BitVec 64, x.take Width.W64.bits = x := by
    intro x
    simp [BitVec.take, BitVec.extractLsb']
  rw [htake, htake]
  have hsigned : ∀ x : BitVec 64, x.signed = x.toInt := fun _ => rfl
  rw [hsigned, hsigned,
    show ∀ y : BitVec Width.W64.bits, BitVec.zeroExtend 64 y = y from fun _ => rfl,
    BitVec.ofInt_add, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.ofInt_toInt,
    show BitVec.ofInt Width.W64.bits (Width.W8.bytes : Int) = 1#64 from rfl, BitVec.mul_one]

/-- The address a `disp(base, index, 8)` expression computes, at 64-bit
address size: the base plus eight times the index plus the displacement. -/
theorem AddrExpr.zeroExtend_interp_sib [L : Labels] (b i : Reg64) (d : Int64)
    (regs : Reg64s) (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W64)
        (a := ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩) regs rng).zeroExtend 64)
      = regs.get64 b + regs.get64 i * 8 + BitVec.ofInt 64 d.toInt := by
  simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize, Reg64s.get64]
  have htake : ∀ x : BitVec 64, x.take Width.W64.bits = x := by
    intro x
    simp [BitVec.take, BitVec.extractLsb']
  rw [htake, htake]
  have hsigned : ∀ x : BitVec 64, x.signed = x.toInt := fun _ => rfl
  rw [hsigned, hsigned,
    show ∀ y : BitVec Width.W64.bits, BitVec.zeroExtend 64 y = y from fun _ => rfl,
    BitVec.ofInt_add, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.ofInt_toInt]
  rfl
