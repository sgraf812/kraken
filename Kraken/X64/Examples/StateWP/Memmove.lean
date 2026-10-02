module

/-
A caller that moves a byte range onto an overlapping range through a call to `memmove`, after
Erbsen et al., "Foundational Integration Verification of a Cryptographic Server" (PLDI 2024,
§2.3). `memmove_spec` proves the contract `memmoveC` of the callee on its own. The contract
allows the two ranges to overlap: its postcondition speaks about the bytes of the old memory.
`memmove_correct` proves the caller from the contract alone.
-/
public import Kraken.StateCfg
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped StateWP

set_option experimental.vcgen true

namespace State

/-- The callee: copy `rdx` bytes from `rsi` to `rdi`, forward when `rdi ≤ rsi` and backward
otherwise, so that an overlapping source is read before it is overwritten. -/
def memmove : Program := parse("
memmove:
  cmp %rsi, %rdi
  jbe fwd
  add %rdx, %rsi
  add %rdx, %rdi
bwd:
  test %rdx, %rdx
  je bdone
  dec %rsi
  dec %rdi
  movb (%rsi), %al
  movb %al, (%rdi)
  dec %rdx
  jmp bwd
bdone:
  ret
fwd:
  test %rdx, %rdx
  je fdone
  movb (%rsi), %al
  movb %al, (%rdi)
  add $1, %rsi
  add $1, %rdi
  dec %rdx
  jmp fwd
fdone:
  ret
")

/-- The caller, with the callee linked between its two blocks. -/
def memmoveProg : Program := parse("
start:
  call memmove
  jmp done
") ++ memmove ++ parse("
done:
  nop
")

/-- The byte at an address, if mapped. -/
abbrev _root_.MachineData.byte (s : MachineData) (a : BitVec 64) : Option (BitVec 8) :=
  (Mem.loadInt s.dmem a 1).map (BitVec.ofInt 8)

/-- The number of bytes, the source and the destination of a call. -/
abbrev _root_.MachineData.mmN (s : MachineData) : Nat := (s.regs.get64 .rdx).toNat
abbrev _root_.MachineData.mmSrc (s : MachineData) : BitVec 64 := s.regs.get64 .rsi
abbrev _root_.MachineData.mmDst (s : MachineData) : BitVec 64 := s.regs.get64 .rdi

/-- The arguments: `rdx` bytes from `rsi` to `rdi`. Both ranges are mapped and do not wrap,
and neither range meets the slot of the return address. -/
def MMPre (s : MachineData) : Prop :=
  s.mmSrc.toNat + s.mmN < 2 ^ 64 ∧ s.mmDst.toNat + s.mmN < 2 ^ 64
    ∧ 8 ≤ (s.regs.get64 .rsp).toNat
    ∧ (∀ i < s.mmN, (s.byte (s.mmSrc + BitVec.ofNat 64 i)).isSome)
    ∧ (∀ i < s.mmN, (s.byte (s.mmDst + BitVec.ofNat 64 i)).isSome)
    ∧ (s.mmDst.toNat + s.mmN ≤ (s.regs.get64 .rsp).toNat - 8
        ∨ (s.regs.get64 .rsp).toNat ≤ s.mmDst.toNat)
    ∧ (s.mmSrc.toNat + s.mmN ≤ (s.regs.get64 .rsp).toNat - 8
        ∨ (s.regs.get64 .rsp).toNat ≤ s.mmSrc.toNat)

/-- The destination holds the old source bytes, and `rsp` is restored. -/
abbrev MMPost (s s' : MachineData) : Prop :=
  (∀ i < s.mmN, s'.byte (s.mmDst + BitVec.ofNat 64 i) = s.byte (s.mmSrc + BitVec.ofNat 64 i))
    ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp

abbrev memmoveC : Contract := ⟨"memmove", MMPre, MMPost⟩

/-! ## The callee -/

private theorem Reg64s.set_low_W8 (r : Reg64s) (g : Reg64) (v : BitVec 8) :
    r.set (.low g .W8) v = r.set64 g ((r.get64 g).replaceLow v) := rfl

@[grind =] private theorem Reg64s.get_set_low_W8 (r : Reg64s) (g : Reg64) (v : BitVec 8) :
    (r.set (.low g .W8) v).get (.low g .W8) = v := by
  simp only [Reg64s.set_low_W8, Reg64s.get, Reg64s.get64_set64, reduceIte, Reg.base, Reg.offset,
    Width.bits, BitVec.replaceLow, BitVec.take, BitVec.drop]
  bv_decide

@[grind =] private theorem Reg64s.get64_set_low_W8 (r : Reg64s) (g g' : Reg64) (v : BitVec 8) :
    (r.set (.low g .W8) v).get64 g' = if g' = g then (r.get64 g).replaceLow v else r.get64 g' := by
  rw [Reg64s.set_low_W8, Reg64s.get64_set64]

@[grind =] private theorem Reg64s.set_al_rsi (r : Reg64s) (v : BitVec 8) :
    (r.set (.low .rax .W8) v).rsi = r.rsi := rfl
@[grind =] private theorem Reg64s.set_al_rdi (r : Reg64s) (v : BitVec 8) :
    (r.set (.low .rax .W8) v).rdi = r.rdi := rfl
@[grind =] private theorem Reg64s.set_al_rdx (r : Reg64s) (v : BitVec 8) :
    (r.set (.low .rax .W8) v).rdx = r.rdx := rfl
@[grind =] private theorem Reg64s.set_al_rsp (r : Reg64s) (v : BitVec 8) :
    (r.set (.low .rax .W8) v).rsp = r.rsp := rfl

/-- A byte loaded and stored again is the same byte. -/
@[grind =] private theorem UInt8.store_load (b : UInt8) :
    ((BitVec.ofInt 8 (b.toNat : Int)).toInt.take 8).toNat.toUInt8 = b := by
  have hb := b.toNat_lt
  have h : (BitVec.ofInt 8 (b.toNat : Int)).toInt.take 8 = b.toNat := by
    rw [Int.take, BitVec.toInt_ofInt, show ((2 : Int) ^ 8) = ((2 ^ 8 : Nat) : Int) by norm_cast,
      Int.bmod_emod]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  rw [h]
  simp

attribute [local grind =] Mem.loadInt_one Mem.get?_storeInt_one

@[grind .] private theorem mm_fwd_lt : Program.blockIdx memmove "memmove" < Program.blockIdx memmove "fwd" := by decide
@[grind .] private theorem mm_bwd_lt : Program.blockIdx memmove "bwd" < Program.blockIdx memmove "bdone" := by decide
@[grind .] private theorem mm_fwd_lt' : Program.blockIdx memmove "fwd" < Program.blockIdx memmove "fdone" := by decide
@[grind .] private theorem mm_bwd_some : (Program.blockAt memmove "bwd").isSome := by decide
@[grind .] private theorem mm_bdone_some : (Program.blockAt memmove "bdone").isSome := by decide
@[grind .] private theorem mm_fwd_some : (Program.blockAt memmove "fwd").isSome := by decide
@[grind .] private theorem mm_fdone_some : (Program.blockAt memmove "fdone").isSome := by decide

/-! ### What the loops compute -/

/-- One iteration: the byte at `src` stored at `d`. -/
def mmStep (m : DataMem) (d src : BitVec 64) : DataMem :=
  match Mem.loadInt m src 1 with
  | some i => Mem.storeInt m d 1 (BitVec.ofInt 8 i).toInt
  | none => m

/-- The forward loop after `c` iterations. -/
def fwdMem (m : DataMem) (dst src : BitVec 64) : Nat → DataMem
  | 0 => m
  | c + 1 => mmStep (fwdMem m dst src c) (dst + .ofNat 64 c) (src + .ofNat 64 c)

/-- The backward loop over `n` bytes after `k` iterations. -/
def bwdMem (m : DataMem) (dst src : BitVec 64) (n : Nat) : Nat → DataMem
  | 0 => m
  | k + 1 => mmStep (bwdMem m dst src n k) (dst + .ofNat 64 (n - 1 - k)) (src + .ofNat 64 (n - 1 - k))

theorem mmStep_get? (m : DataMem) (d src b : BitVec 64) :
    (mmStep m d src).get? b = if b = d ∧ (m.get? src).isSome then m.get? src else m.get? b := by
  unfold mmStep
  rw [Mem.loadInt_one]
  cases h : m.get? src with
  | none => simp
  | some x =>
    show (Mem.storeInt m d 1 (BitVec.ofInt 8 (x.toNat : Int)).toInt).get? b = _
    rw [Mem.get?_storeInt_one, UInt8.store_load]
    by_cases hb : b = d <;> simp [hb]

theorem addr_toNat (x : BitVec 64) (i : Nat) (h : x.toNat + i < 2 ^ 64) :
    (x + BitVec.ofNat 64 i).toNat = x.toNat + i := by
  rw [BitVec.toNat_add_of_lt] <;> rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem addr_ne {x y : BitVec 64} {i j : Nat} (hx : x.toNat + i < 2 ^ 64)
    (hy : y.toNat + j < 2 ^ 64) (h : x.toNat + i ≠ y.toNat + j) :
    x + BitVec.ofNat 64 i ≠ y + BitVec.ofNat 64 j := fun e =>
  h (by rw [← addr_toNat x i hx, ← addr_toNat y j hy, e])

theorem fwdMem_other (m : DataMem) (dst src a : BitVec 64) (c : Nat)
    (h : ∀ j < c, a ≠ dst + BitVec.ofNat 64 j) : (fwdMem m dst src c).get? a = m.get? a := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [fwdMem, mmStep_get?, ite_eq_right (fun ⟨e, _⟩ => h c (by omega) e),
      ih (fun j hj => h j (by omega))]

theorem bwdMem_other (m : DataMem) (dst src a : BitVec 64) (n k : Nat) (hk : k ≤ n)
    (h : ∀ j, n - k ≤ j → j < n → a ≠ dst + BitVec.ofNat 64 j) :
    (bwdMem m dst src n k).get? a = m.get? a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [bwdMem, mmStep_get?, ite_eq_right (fun ⟨e, _⟩ => h (n - 1 - k) (by omega) (by omega) e),
      ih (by omega) (fun j hj hjn => h j (by omega) hjn)]

theorem fwdMem_copy (m : DataMem) (dst src : BitVec 64) (n : Nat)
    (hle : dst.toNat ≤ src.toNat) (hs : src.toNat + n < 2 ^ 64) (hd : dst.toNat + n < 2 ^ 64)
    (hmap : ∀ j < n, (m.get? (src + BitVec.ofNat 64 j)).isSome) :
    ∀ c ≤ n, ∀ j < c, (fwdMem m dst src c).get? (dst + BitVec.ofNat 64 j)
      = m.get? (src + BitVec.ofNat 64 j) := by
  intro c hc
  induction c with
  | zero => intro j hj; omega
  | succ c ih =>
    intro j hj
    have hsrc : (fwdMem m dst src c).get? (src + BitVec.ofNat 64 c)
        = m.get? (src + BitVec.ofNat 64 c) :=
      fwdMem_other m dst src _ c (fun j' hj' => addr_ne (by omega) (by omega) (by omega))
    rw [fwdMem, mmStep_get?]
    by_cases hjc : j = c
    · subst hjc
      rw [ite_eq_left ⟨rfl, by rw [hsrc]; exact hmap j (by omega)⟩, hsrc]
    · rw [ite_eq_right (fun ⟨e, _⟩ => addr_ne (x := dst) (y := dst) (i := j) (j := c) (by omega)
        (by omega) (by omega) e), ih (by omega) j (by omega)]

theorem bwdMem_copy (m : DataMem) (dst src : BitVec 64) (n : Nat)
    (hlt : src.toNat < dst.toNat) (hd : dst.toNat + n < 2 ^ 64)
    (hmap : ∀ j < n, (m.get? (src + BitVec.ofNat 64 j)).isSome) :
    ∀ k ≤ n, ∀ j, n - k ≤ j → j < n → (bwdMem m dst src n k).get? (dst + BitVec.ofNat 64 j)
      = m.get? (src + BitVec.ofNat 64 j) := by
  intro k hk
  induction k with
  | zero => intro j hj hjn; omega
  | succ k ih =>
    intro j hj hjn
    have hsrc : (bwdMem m dst src n k).get? (src + BitVec.ofNat 64 (n - 1 - k))
        = m.get? (src + BitVec.ofNat 64 (n - 1 - k)) :=
      bwdMem_other m dst src _ n k (by omega)
        (fun j' hj' hj'n => addr_ne (by omega) (by omega) (by omega))
    rw [bwdMem, mmStep_get?]
    by_cases hjc : j = n - 1 - k
    · subst hjc
      rw [ite_eq_left ⟨rfl, by rw [hsrc]; exact hmap _ (by omega)⟩, hsrc]
    · rw [ite_eq_right (fun ⟨e, _⟩ => addr_ne (x := dst) (y := dst) (by omega) (by omega)
        (by omega) e), ih (by omega) j (by omega) hjn]

/-- The pushed return address stays in its slot: the written bytes miss it. -/
theorem slot_untouched (m : DataMem) (f : Nat → DataMem) (dst sp : BitVec 64) (n : Nat)
    (h8 : 8 ≤ sp.toNat) (hd : dst.toNat + n < 2 ^ 64)
    (hdisj : dst.toNat + n ≤ sp.toNat - 8 ∨ sp.toNat ≤ dst.toNat)
    (hf : ∀ a, (∀ j < n, a ≠ dst + BitVec.ofNat 64 j) → (f n).get? a = m.get? a) :
    Mem.loadInt (f n) (sp - 8#64) 8 = Mem.loadInt m (sp - 8#64) 8 := by
  have hsp : (sp - 8#64).toNat = sp.toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega),
      BitVec.toNat_ofNat]
  apply Mem.loadInt_congr
  intro i hi
  exact hf _ fun j hj => addr_ne (by omega) (by omega) (by omega)

/-- `s.pushRa` touches only the slot below `rsp`. -/
theorem get?_pushRa (s : MachineData) (ra : Int64) (a : BitVec 64)
    (h : ∀ i < 8, a ≠ s.regs.get64 .rsp - 8#64 + BitVec.ofNat 64 i) :
    (s.pushRa ra).dmem.get? a = s.dmem.get? a := by
  rw [MachineData.dmem_pushRa]
  exact Mem.get?_storeInt_of_ne _ _ _ _ _ h

theorem mmStep_of_load {m : DataMem} {d src : BitVec 64} {i : Int}
    (h : Mem.loadInt m src 1 = some i) : mmStep m d src = Mem.storeInt m d 1 (BitVec.ofInt 8 i).toInt := by
  unfold mmStep; rw [h]

theorem toNat_sub_one {r : BitVec 64} (hr : 0 < r.toNat) : (r - 1).toNat = r.toNat - 1 := by
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
  simp

theorem add_sub_one (x r : BitVec 64) (hr : 0 < r.toNat) :
    x + r - 1 = x + BitVec.ofNat 64 (r.toNat - 1) := by
  have h : BitVec.ofNat 64 (r.toNat - 1) = r - 1 := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_sub_one hr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := r.isLt; omega)]
  rw [h, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

/-! ### The facts the callee's VCs use -/

section
variable (s : MachineData) (ra : Int64) (r : BitVec 64)

private abbrev P (s : MachineData) (ra : Int64) : DataMem := (s.pushRa ra).dmem

/-- A byte of a range that misses the slot below `sp` is not in the slot. -/
theorem slot_ne {x sp : BitVec 64} {j n : Nat} (h8 : 8 ≤ sp.toNat) (hb : x.toNat + n < 2 ^ 64)
    (hdisj : x.toNat + n ≤ sp.toNat - 8 ∨ sp.toNat ≤ x.toNat) (hj : j < n) :
    ∀ i < 8, x + BitVec.ofNat 64 j ≠ sp - 8#64 + BitVec.ofNat 64 i := by
  intro i hi
  have hsp : (sp - 8#64).toNat = sp.toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]
  have := sp.isLt
  exact addr_ne (by omega) (by omega) (by omega)

/-- The source byte, read from `s` through the pushed state. -/
theorem pushRa_get?_src (h : MMPre s) (j : Nat) (hj : j < s.mmN) :
    (s.pushRa ra).dmem.get? (s.regs.get64 .rsi + BitVec.ofNat 64 j)
      = s.dmem.get? (s.regs.get64 .rsi + BitVec.ofNat 64 j) :=
  get?_pushRa s ra _ (by unfold MMPre at h; exact slot_ne h.2.2.1 h.1 h.2.2.2.2.2.2 hj)

/-- The destination byte, read from `s` through the pushed state. -/
theorem pushRa_get?_dst (h : MMPre s) (j : Nat) (hj : j < s.mmN) :
    (s.pushRa ra).dmem.get? (s.regs.get64 .rdi + BitVec.ofNat 64 j)
      = s.dmem.get? (s.regs.get64 .rdi + BitVec.ofNat 64 j) :=
  get?_pushRa s ra _ (by unfold MMPre at h; exact slot_ne h.2.2.1 h.2.1 h.2.2.2.2.2.1 hj)

theorem some_of_byte {s : MachineData} {a : BitVec 64} (h : (s.byte a).isSome) :
    (s.dmem.get? a).isSome := by
  simpa [MachineData.byte, Mem.loadInt_one] using h

end

section
variable (s : MachineData) (ra : Int64)

@[grind =] theorem fwdMem_of_zero {m : DataMem} {d src : BitVec 64} {c : Nat} (hc : c = 0) :
    fwdMem m d src c = m := by subst hc; rfl

@[grind =] theorem bwdMem_of_zero {m : DataMem} {d src : BitVec 64} {n c : Nat} (hc : c = 0) :
    bwdMem m d src n c = m := by subst hc; rfl

@[grind =] theorem mmStep_eq (m : DataMem) (d src : BitVec 64) :
    mmStep m d src = match Mem.loadInt m src 1 with
      | some i => Mem.storeInt m d 1 (BitVec.ofInt 8 i).toInt
      | none => m := rfl

@[grind =] theorem fwd_step (m : DataMem) (d src r : BitVec 64) (n : Nat) (hr : 0 < r.toNat)
    (hrn : r.toNat ≤ n) :
    fwdMem m d src (n - (r - 1).toNat)
      = mmStep (fwdMem m d src (n - r.toNat)) (d + BitVec.ofNat 64 (n - r.toNat))
          (src + BitVec.ofNat 64 (n - r.toNat)) := by
  rw [toNat_sub_one hr, show n - (r.toNat - 1) = (n - r.toNat) + 1 by omega]
  rfl

@[grind =] theorem ofNat_step (r : BitVec 64) (n : Nat) (hr : 0 < r.toNat) (hrn : r.toNat ≤ n) :
    BitVec.ofNat 64 (n - (r - 1).toNat) = BitVec.ofNat 64 (n - r.toNat) + 1 := by
  rw [toNat_sub_one hr, show n - (r.toNat - 1) = (n - r.toNat) + 1 by omega, BitVec.ofNat_add]
  rfl

@[grind =] theorem bwd_step (m : DataMem) (d src r : BitVec 64) (n : Nat) (hr : 0 < r.toNat)
    (hrn : r.toNat ≤ n) :
    bwdMem m d src n (n - (r - 1).toNat)
      = mmStep (bwdMem m d src n (n - r.toNat)) (d + r - 1) (src + r - 1) := by
  rw [toNat_sub_one hr, show n - (r.toNat - 1) = (n - r.toNat) + 1 by omega, bwdMem,
    show n - 1 - (n - r.toNat) = r.toNat - 1 by omega, add_sub_one _ _ hr, add_sub_one _ _ hr]

/-- The facts of `MMPre s`, with the registers spelled out. -/
theorem MMPre.facts {s : MachineData} (h : MMPre s) :
    (s.regs.get64 .rsi).toNat + (s.regs.get64 .rdx).toNat < 2 ^ 64
    ∧ (s.regs.get64 .rdi).toNat + (s.regs.get64 .rdx).toNat < 2 ^ 64
    ∧ 8 ≤ (s.regs.get64 .rsp).toNat
    ∧ (∀ i < (s.regs.get64 .rdx).toNat,
        (s.dmem.get? (s.regs.get64 .rsi + BitVec.ofNat 64 i)).isSome)
    ∧ (∀ i < (s.regs.get64 .rdx).toNat,
        (s.dmem.get? (s.regs.get64 .rdi + BitVec.ofNat 64 i)).isSome)
    ∧ ((s.regs.get64 .rdi).toNat + (s.regs.get64 .rdx).toNat ≤ (s.regs.get64 .rsp).toNat - 8
        ∨ (s.regs.get64 .rsp).toNat ≤ (s.regs.get64 .rdi).toNat) := by
  unfold MMPre at h
  exact ⟨h.1, h.2.1, h.2.2.1, fun i hi => some_of_byte (h.2.2.2.1 i hi),
    fun i hi => some_of_byte (h.2.2.2.2.1 i hi), h.2.2.2.2.2.1⟩

variable (r : BitVec 64)

@[grind =] theorem fwd_load (h : MMPre s)
    (hle : (s.regs.get64 .rdi).toNat ≤ (s.regs.get64 .rsi).toNat)
    (hr : 0 < r.toNat) (hrn : r.toNat ≤ (s.regs.get64 .rdx).toNat) :
    (Mem.loadInt (fwdMem (s.pushRa ra).dmem (s.regs.get64 .rdi) (s.regs.get64 .rsi)
      ((s.regs.get64 .rdx).toNat - r.toNat))
      (s.regs.get64 .rsi + BitVec.ofNat 64 ((s.regs.get64 .rdx).toNat - r.toNat)) 1).isSome
      = true := by
  obtain ⟨hs, hd, -, hsrc, -, -⟩ := h.facts
  have hother : (fwdMem (s.pushRa ra).dmem (s.regs.get64 .rdi) (s.regs.get64 .rsi)
      ((s.regs.get64 .rdx).toNat - r.toNat)).get?
        (s.regs.get64 .rsi + BitVec.ofNat 64 ((s.regs.get64 .rdx).toNat - r.toNat))
      = s.dmem.get? (s.regs.get64 .rsi + BitVec.ofNat 64 ((s.regs.get64 .rdx).toNat - r.toNat)) := by
    rw [fwdMem_other _ _ _ _ _ fun j hj => addr_ne (by omega) (by omega) (by omega)]
    exact pushRa_get?_src s ra h _ (by show _ < (s.regs.get64 .rdx).toNat; omega)
  rw [Mem.loadInt_one, hother, Option.isSome_map]
  exact hsrc _ (by omega)

@[grind =] theorem fwd_store (h : MMPre s) (hr : 0 < r.toNat)
    (hrn : r.toNat ≤ (s.regs.get64 .rdx).toNat) :
    (Mem.loadInt (fwdMem (s.pushRa ra).dmem (s.regs.get64 .rdi) (s.regs.get64 .rsi)
      ((s.regs.get64 .rdx).toNat - r.toNat))
      (s.regs.get64 .rdi + BitVec.ofNat 64 ((s.regs.get64 .rdx).toNat - r.toNat)) 1).isSome
      = true := by
  obtain ⟨hs, hd, -, -, hdst, -⟩ := h.facts
  have hother : (fwdMem (s.pushRa ra).dmem (s.regs.get64 .rdi) (s.regs.get64 .rsi)
      ((s.regs.get64 .rdx).toNat - r.toNat)).get?
        (s.regs.get64 .rdi + BitVec.ofNat 64 ((s.regs.get64 .rdx).toNat - r.toNat))
      = s.dmem.get? (s.regs.get64 .rdi + BitVec.ofNat 64 ((s.regs.get64 .rdx).toNat - r.toNat)) := by
    rw [fwdMem_other _ _ _ _ _ fun j hj => addr_ne (by omega) (by omega) (by omega)]
    exact pushRa_get?_dst s ra h _ (by show _ < (s.regs.get64 .rdx).toNat; omega)
  rw [Mem.loadInt_one, hother, Option.isSome_map]
  exact hdst _ (by omega)

@[grind =] theorem bwd_load (h : MMPre s)
    (hlt : (s.regs.get64 .rsi).toNat < (s.regs.get64 .rdi).toNat)
    (hr : 0 < r.toNat) (hrn : r.toNat ≤ (s.regs.get64 .rdx).toNat) :
    (Mem.loadInt (bwdMem (s.pushRa ra).dmem (s.regs.get64 .rdi) (s.regs.get64 .rsi)
      (s.regs.get64 .rdx).toNat ((s.regs.get64 .rdx).toNat - r.toNat))
      (s.regs.get64 .rsi + r - 1) 1).isSome = true := by
  obtain ⟨hs, hd, -, hsrc, -, -⟩ := h.facts
  have hother : (bwdMem (s.pushRa ra).dmem (s.regs.get64 .rdi) (s.regs.get64 .rsi)
      (s.regs.get64 .rdx).toNat ((s.regs.get64 .rdx).toNat - r.toNat)).get?
        (s.regs.get64 .rsi + BitVec.ofNat 64 (r.toNat - 1))
      = s.dmem.get? (s.regs.get64 .rsi + BitVec.ofNat 64 (r.toNat - 1)) := by
    rw [bwdMem_other _ _ _ _ _ _ (by omega) fun j hj hjn => addr_ne (by omega) (by omega) (by omega)]
    exact pushRa_get?_src s ra h _ (by show _ < (s.regs.get64 .rdx).toNat; omega)
  rw [add_sub_one _ _ hr, Mem.loadInt_one, hother, Option.isSome_map]
  exact hsrc _ (by omega)

@[grind =] theorem bwd_store (h : MMPre s) (hr : 0 < r.toNat)
    (hrn : r.toNat ≤ (s.regs.get64 .rdx).toNat) :
    (Mem.loadInt (bwdMem (s.pushRa ra).dmem (s.regs.get64 .rdi) (s.regs.get64 .rsi)
      (s.regs.get64 .rdx).toNat ((s.regs.get64 .rdx).toNat - r.toNat))
      (s.regs.get64 .rdi + r - 1) 1).isSome = true := by
  obtain ⟨hs, hd, -, -, hdst, -⟩ := h.facts
  have hother : (bwdMem (s.pushRa ra).dmem (s.regs.get64 .rdi) (s.regs.get64 .rsi)
      (s.regs.get64 .rdx).toNat ((s.regs.get64 .rdx).toNat - r.toNat)).get?
        (s.regs.get64 .rdi + BitVec.ofNat 64 (r.toNat - 1))
      = s.dmem.get? (s.regs.get64 .rdi + BitVec.ofNat 64 (r.toNat - 1)) := by
    rw [bwdMem_other _ _ _ _ _ _ (by omega) fun j hj hjn => addr_ne (by omega) (by omega) (by omega)]
    exact pushRa_get?_dst s ra h _ (by show _ < (s.regs.get64 .rdx).toNat; omega)
  rw [add_sub_one _ _ hr, Mem.loadInt_one, hother, Option.isSome_map]
  exact hdst _ (by omega)

/-- The pushed slot, under the written destination bytes. -/
theorem slot_facts {s : MachineData} (h : MMPre s) :
    (s.regs.get64 .rsp - 8#64).toNat = (s.regs.get64 .rsp).toNat - 8 := by
  obtain ⟨-, -, h8, -, -, -⟩ := h.facts
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]

@[grind =] theorem fwd_slot (h : MMPre s) (c : Nat) (hc : c ≤ (s.regs.get64 .rdx).toNat) :
    Mem.loadInt (fwdMem (s.pushRa ra).dmem (s.regs.get64 .rdi) (s.regs.get64 .rsi) c)
      (s.regs.get64 .rsp - 8#64) 8 = Mem.loadInt (s.pushRa ra).dmem (s.regs.get64 .rsp - 8#64) 8 := by
  obtain ⟨-, hd, h8, -, -, hslot⟩ := h.facts
  have hsp := slot_facts h
  have := (s.regs.get64 .rsp).isLt
  apply Mem.loadInt_congr
  intro i hi
  exact fwdMem_other _ _ _ _ _ fun j hj => addr_ne (by omega) (by omega) (by omega)

@[grind =] theorem bwd_slot (h : MMPre s) (c : Nat) (hc : c ≤ (s.regs.get64 .rdx).toNat) :
    Mem.loadInt (bwdMem (s.pushRa ra).dmem (s.regs.get64 .rdi) (s.regs.get64 .rsi)
      (s.regs.get64 .rdx).toNat c)
      (s.regs.get64 .rsp - 8#64) 8 = Mem.loadInt (s.pushRa ra).dmem (s.regs.get64 .rsp - 8#64) 8 := by
  obtain ⟨-, hd, h8, -, -, hslot⟩ := h.facts
  have hsp := slot_facts h
  have := (s.regs.get64 .rsp).isLt
  apply Mem.loadInt_congr
  intro i hi
  exact bwdMem_other _ _ _ _ _ _ hc fun j hj hjn => addr_ne (by omega) (by omega) (by omega)

@[grind =] theorem fwd_byte (h : MMPre s)
    (hle : (s.regs.get64 .rdi).toNat ≤ (s.regs.get64 .rsi).toNat) (c j : Nat)
    (hc : c ≤ (s.regs.get64 .rdx).toNat) (hj : j < c) :
    Mem.loadInt (fwdMem (s.pushRa ra).dmem (s.regs.get64 .rdi) (s.regs.get64 .rsi) c)
      (s.regs.get64 .rdi + BitVec.ofNat 64 j) 1
      = Mem.loadInt s.dmem (s.regs.get64 .rsi + BitVec.ofNat 64 j) 1 := by
  obtain ⟨hs, hd, -, hsrc, -, -⟩ := h.facts
  rw [Mem.loadInt_one, Mem.loadInt_one, fwdMem_copy _ _ _ _ hle (by omega) (by omega)
    (fun j' hj' => by
      rw [pushRa_get?_src s ra h _ (by show _ < (s.regs.get64 .rdx).toNat; omega)]
      exact hsrc _ hj') c hc j hj,
    pushRa_get?_src s ra h _ (by show _ < (s.regs.get64 .rdx).toNat; omega)]

@[grind =] theorem bwd_byte (h : MMPre s)
    (hlt : (s.regs.get64 .rsi).toNat < (s.regs.get64 .rdi).toNat) (c j : Nat)
    (hc : c ≤ (s.regs.get64 .rdx).toNat) (hj : (s.regs.get64 .rdx).toNat - c ≤ j)
    (hjn : j < (s.regs.get64 .rdx).toNat) :
    Mem.loadInt (bwdMem (s.pushRa ra).dmem (s.regs.get64 .rdi) (s.regs.get64 .rsi)
      (s.regs.get64 .rdx).toNat c) (s.regs.get64 .rdi + BitVec.ofNat 64 j) 1
      = Mem.loadInt s.dmem (s.regs.get64 .rsi + BitVec.ofNat 64 j) 1 := by
  obtain ⟨hs, hd, -, hsrc, -, -⟩ := h.facts
  rw [Mem.loadInt_one, Mem.loadInt_one, bwdMem_copy _ _ _ _ hlt (by omega)
    (fun j' hj' => by
      rw [pushRa_get?_src s ra h _ (by show _ < (s.regs.get64 .rdx).toNat; omega)]
      exact hsrc _ hj') c hc j hj hjn,
    pushRa_get?_src s ra h _ (by show _ < (s.regs.get64 .rdx).toNat; omega)]

end

/-- In `fwd`, `rdx` bytes remain: `fwdMem` has copied the bytes below them. -/
private abbrev MMFwd (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  MMPre s ∧ s.mmDst.toNat ≤ s.mmSrc.toNat ∧ t.mmN ≤ s.mmN
    ∧ t.mmSrc = s.mmSrc + BitVec.ofNat 64 (s.mmN - t.mmN)
    ∧ t.mmDst = s.mmDst + BitVec.ofNat 64 (s.mmN - t.mmN)
    ∧ t.regs.get64 .rsp = s.regs.get64 .rsp - 8#64
    ∧ t.dmem = fwdMem (s.pushRa ra).dmem s.mmDst s.mmSrc (s.mmN - t.mmN)

/-- In `bwd`, `rdx` bytes remain: `bwdMem` has copied the bytes above them. -/
private abbrev MMBwd (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  MMPre s ∧ s.mmSrc.toNat < s.mmDst.toNat ∧ t.mmN ≤ s.mmN
    ∧ t.mmSrc = s.mmSrc + t.regs.get64 .rdx ∧ t.mmDst = s.mmDst + t.regs.get64 .rdx
    ∧ t.regs.get64 .rsp = s.regs.get64 .rsp - 8#64
    ∧ t.dmem = bwdMem (s.pushRa ra).dmem s.mmDst s.mmSrc s.mmN (s.mmN - t.mmN)

/-- The callee's table, for a call from `s` that returns to `ra`. -/
private abbrev mm_table (s : MachineData) (ra : Int64) : Label → MachineData → Prop
  | "memmove", t => t = s.pushRa ra ∧ MMPre s
  | "bwd", t => MMBwd s ra t
  | "bdone", t => MMBwd s ra t ∧ t.mmN = 0
  | "fwd", t => MMFwd s ra t
  | "fdone", t => MMFwd s ra t ∧ t.mmN = 0
  | _, _ => False

/-- The contract of `memmove`, in every linked program. -/
theorem memmove_spec [LinkedProgram] (s : MachineData) (ra : Int64) :
    ⦃ fun t => t = s.pushRa ra ∧ MMPre s ⦄
      memmove
    ⦃ (fun _ _ => False); fun a t => a = ra ∧ MMPost s t ⦄ := by
  refine StateWP.cfg (p := memmove) (mm_table s ra) (fun _ t => (t.regs.get64 .rdx).toNat) (fun _ => False)
    (fun a t => a = ra ∧ MMPost s t) ?_
  cfg_cases [memmove]
  all_goals kvcgen64 [BitVec.and_self] with finish

/-! ## The caller -/

@[grind .] private theorem start_lt_done :
    Program.blockIdx memmoveProg "start" < Program.blockIdx memmoveProg "done" := by decide

@[grind .] private theorem done_isSome : (Program.blockAt memmoveProg "done").isSome := by decide

/-- The caller's table: `start` holds the arguments, `done` the moved bytes. The blocks of the
callee are entered only by the call. -/
private abbrev mp_table (d : MachineData) : Label → MachineData → Prop
  | "start", s => s = d
  | "done", s => ∀ i < d.mmN, s.byte (d.mmDst + BitVec.ofNat 64 i) = d.byte (d.mmSrc + BitVec.ofNat 64 i)
  | _, _ => False

private theorem memmove_call_spec [LinkedProgram] {Q : Unit → MachineData → Prop}
    {E : Int64 → MachineData → Prop} (asz osz : Width) :
    ⦃ fun s => memmoveC.Implemented
        ⊓ ((Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome = true)
        ⊓ MMPre s ⊓ (∀ s', MMPost s s' → Q () s') ⦄
      Directive.instr
        (.regular asz osz (.call (.rel (.sub (.label "memmove") .after_current_instruction))))
    ⦃ Q; E ⦄ :=
  StateWP.call_spec asz osz memmoveC

theorem memmove_correct [layout : Layout] [Kraken.Executable.ValidExecutable (layout memmoveProg)]
    (d : MachineData) (hpre : MMPre d)
    (hslot : (Mem.loadInt d.dmem (d.regs.get64 .rsp - 8#64) 8).isSome = true) :
    Eventually (straightlineStep (layout memmoveProg))
      (fun st => ∀ i < d.mmN, st.1.byte (d.mmDst + BitVec.ofNat 64 i) = d.byte (d.mmSrc + BitVec.ofNat 64 i))
      (d, layout.start) := by
  apply eventually_straightlineStep_of_wp
  intro _
  refine StateWP.cfg_wp (mp_table d) (fun _ _ => 0) _ ⊥ ?_ d rfl
  cfg_cases [memmoveProg, memmove]
  · intro k hlink
    have himpl : memmoveC.Implemented :=
      StateWP.implemented_of_triple (body := memmove.tail) (rest := parse("done:\n  nop")) hlink
        memmoveC (by decide) memmove_spec
    kvcgen64 [memmove_call_spec] with finish
  all_goals kvcgen64 with finish

end State
