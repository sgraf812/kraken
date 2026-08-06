/-
The register and system-state read-over-write API the spec framework discharges
against: `Sys D` and its projections, register reads over `set64` (both the
indexed `get64` and the per-field accessors), the `MachineData` record
projections, and the `StatusFlags`/`BitVec` reductions the flag and address
arithmetic normalize with.
-/
import Kraken.OmniSemantics
import Kraken.GrindFold
import Std.Tactic.Do

open Std.Internal.Do
open Std.Internal.Do.WPMonad

set_option mvcgen.warning false
set_option grind.warning false

/-! ## System state

The denotational monad runs over `Sys D`: the CPU `MachineData` plus a device
state `D`. Instruction primitives update `machine` and thread `device`; a `jump`
carries the whole `Sys D` in the exception, so `device` survives control transfer.
The projection-over-`mk` lemmas let the state-simplification and `easm` fold a
`Sys` update the way they already fold a `MachineData` update. -/

structure Sys (D : Type) where
  machine : MachineData
  device : D

@[simp] theorem Sys.machine_mk {D : Type} (m : MachineData) (d : D) :
    (Sys.mk m d).machine = m := rfl
@[simp] theorem Sys.device_mk {D : Type} (m : MachineData) (d : D) :
    (Sys.mk m d).device = d := rfl

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

@[simp, grind =] theorem Reg64s.get64_set64 (s : Reg64s) (r r' : Reg64) (v : BitVec 64) :
    (s.set64 r v).get64 r' = if r' = r then v else s.get64 r' := by
  cases r <;> cases r' <;> simp [Reg64s.set64, Reg64s.get64]

@[simp, grind =] theorem Reg64s.get_low64 (s : Reg64s) (r : Reg64) :
    s.get (.low r .W64) = s.get64 r := by
  simp [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop]

@[simp, grind =] theorem Reg64s.set_low64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    Reg64s.set s (.low r .W64) v = s.set64 r v := rfl

@[simp, grind =] theorem MachineData.regs_setReg (s : MachineData) {w} (r : Reg w) (v : w.type) :
    (s.setReg r v).regs = s.regs.set r v := rfl
@[simp, grind =] theorem MachineData.status_setReg (s : MachineData) {w} (r : Reg w) (v : w.type) :
    (s.setReg r v).status = s.status := rfl
@[simp, grind =] theorem MachineData.dmem_setReg (s : MachineData) {w} (r : Reg w) (v : w.type) :
    (s.setReg r v).dmem = s.dmem := rfl
@[simp, grind =] theorem MachineData.zmms_setReg (s : MachineData) {w} (r : Reg w) (v : w.type) :
    (s.setReg r v).zmms = s.zmms := rfl

@[simp] theorem MachineData.regs_mk (r z st d) : (MachineData.mk r z st d).regs = r := rfl
@[simp] theorem MachineData.dmem_mk (r z st d) : (MachineData.mk r z st d).dmem = d := rfl
@[simp] theorem MachineData.status_mk (r z st d) : (MachineData.mk r z st d).status = st := rfl
@[simp] theorem MachineData.zmms_mk (r z st d) : (MachineData.mk r z st d).zmms = z := rfl

@[grind =] theorem Int64.ofNat_lit (n : Nat) : (OfNat.ofNat n : Int64) = Int64.ofNat n := rfl
@[grind =] theorem Int64.toBitVec_lit (n : Nat) :
    (OfNat.ofNat n : Int64).toBitVec = BitVec.ofNat 64 n := rfl
@[grind =] theorem BitVec.setWidth_64_64 (x : BitVec 64) :
    BitVec.setWidth 64 x = x := BitVec.setWidth_eq x
@[simp, grind =] theorem BitVec.ofInt_toInt_int64 (c : Int64) :
    BitVec.ofInt 64 c.toInt = c.toBitVec := by
  rw [show c.toInt = c.toBitVec.toInt from rfl, BitVec.ofInt_toInt]

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
