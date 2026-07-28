/-
Per-instruction monadic actions over `X64M` and their accessor-style `@[spec]`
triples, plus the register read-over-write API used to discharge the benchmark
postconditions.

The instruction bodies are the direct monadic transliterations of the
corresponding cases of `Operation.interp` in `Kraken/Semantics.lean`, including
the status-flag effects. Formal adequacy of these actions with respect to the
straightline interpreter is out of scope here.
-/
import Kraken.OmniSemantics
import Std.Tactic.Do

open Std.Internal.Do
open Std.Internal.Do.WPMonad

set_option mvcgen.warning false
set_option grind.warning false

/-! ## `.unsigned`/`.signed` reductions -/
@[grind hom] theorem BitVec.unsigned_hom {w} (x : BitVec w) : x.unsigned = (x.toNat : Int) := rfl
@[simp] theorem BitVec.unsigned_eq {w} (x : BitVec w) : x.unsigned = (x.toNat : Int) := rfl
@[simp] theorem BitVec.signed_eq {w} (x : BitVec w) : x.signed = x.toInt := rfl

@[simp, grind =] theorem StatusFlags.cf_from_result {w} (v : BitVec w)
    (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result v f).cf = f.cf := rfl

/-! ## Register read-over-write API

Register reads are characterized by rewriting, so discharging queries only the
registers the postcondition mentions and the state chain is never unfolded into
record literals. -/

@[simp, grind =] theorem Reg64s.get64_set64 (s : Reg64s) (r r' : Reg64) (v : Width.W64.type) :
    (s.set64 r v).get64 r' = if r' = r then v else s.get64 r' := by
  cases r <;> cases r' <;> simp [Reg64s.set64, Reg64s.get64]

@[simp, grind =] theorem Reg64s.get_low64 (s : Reg64s) (r : Reg64) :
    s.get (.low r .W64) = s.get64 r := by
  simp [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop]

@[simp, grind =] theorem Reg64s.set_low64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
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

@[simp, grind =] theorem Reg64s.rax_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).rax = if r = .rax then .ofBitVec v else s.rax := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rbx_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).rbx = if r = .rbx then .ofBitVec v else s.rbx := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rcx_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).rcx = if r = .rcx then .ofBitVec v else s.rcx := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rdx_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).rdx = if r = .rdx then .ofBitVec v else s.rdx := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rsi_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).rsi = if r = .rsi then .ofBitVec v else s.rsi := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rdi_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).rdi = if r = .rdi then .ofBitVec v else s.rdi := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rbp_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).rbp = if r = .rbp then .ofBitVec v else s.rbp := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r8_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).r8 = if r = .r8 then .ofBitVec v else s.r8 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r9_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).r9 = if r = .r9 then .ofBitVec v else s.r9 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r10_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).r10 = if r = .r10 then .ofBitVec v else s.r10 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r11_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).r11 = if r = .r11 then .ofBitVec v else s.r11 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r12_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).r12 = if r = .r12 then .ofBitVec v else s.r12 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r13_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).r13 = if r = .r13 then .ofBitVec v else s.r13 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r14_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).r14 = if r = .r14 then .ofBitVec v else s.r14 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r15_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).r15 = if r = .r15 then .ofBitVec v else s.r15 := by cases r <;> simp [Reg64s.set64]

/-! ## Data-memory writer

The dual of `MachineData.setReg` for the data memory, with its own read-over-write
projections so the state chain after a store stays an atom characterized by
equations. -/

def MachineData.setDmem (s : MachineData) (d : DataMem) : MachineData := { s with dmem := d }

@[simp, grind =] theorem MachineData.dmem_setDmem (s : MachineData) (d : DataMem) :
    (s.setDmem d).dmem = d := rfl
@[simp, grind =] theorem MachineData.regs_setDmem (s : MachineData) (d : DataMem) :
    (s.setDmem d).regs = s.regs := rfl
@[simp, grind =] theorem MachineData.status_setDmem (s : MachineData) (d : DataMem) :
    (s.setDmem d).status = s.status := rfl
@[simp, grind =] theorem MachineData.zmms_setDmem (s : MachineData) (d : DataMem) :
    (s.setDmem d).zmms = s.zmms := rfl

/-! ## Explicit addressing

A memory operand as a base register, an optional scaled index register, and a
displacement. `Addr.eval` is the 64-bit effective address, matching
`AddrExpr.interp` at address size 64 (register components are signed, the scale
multiplies the index, the sum is reduced modulo `2^64`). -/

structure Addr where
  base : Reg64
  index : Option (Reg64 × Int64) := none
  disp : Int64 := 0

def Addr.eval (a : Addr) (s : MachineData) : BitVec 64 :=
  let base := (s.regs.get64 a.base).toInt
  let idx := match a.index with
    | some (r, scale) => (s.regs.get64 r).toInt * scale.toInt
    | none => 0
  BitVec.ofInt 64 (base + idx + a.disp.toInt)

/-- The effective address depends only on the register file, so a data-memory
write leaves it unchanged: a store address stays comparable to a later load
address across the intervening `setDmem`. -/
@[simp, grind =] theorem Addr.eval_setDmem (a : Addr) (s : MachineData) (d : DataMem) :
    a.eval (s.setDmem d) = a.eval s := rfl

/-! ## Per-instruction monadic actions

Each register action is a single `modify`; the memory actions read the current
state, compute the effective address, and delegate to `MachineData.load`/`store`.
Each body is the transliteration of the matching `Operation.interp` case (flag
effects included). The benchmark programs are do blocks of these actions. -/
namespace Op

def movRI (r : Reg64) (i : Int64) : X64M Unit :=
  modify (·.setReg (.low r .W64) (BitVec.setWidth 64 i.toBitVec))

def movRR (rd rs : Reg64) : X64M Unit :=
  modify fun s => s.setReg (.low rd .W64) (s.regs.get64 rs)

def decR (r : Reg64) : X64M Unit :=
  modify fun s =>
    let a := s.regs.get64 r
    let v := a - 1
    let status := StatusFlags.from_result v
      { cf := s.status.cf,
        af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
        of := v.signed != a.signed - 1 }
    { s with status }.setReg (.low r .W64) v

def addRI (r : Reg64) (i : Int64) : X64M Unit :=
  modify fun s =>
    let a := BitVec.setWidth 64 i.toBitVec
    let b := s.regs.get64 r
    let v := a + b
    let status := StatusFlags.from_result v
      { cf := v.unsigned != a.unsigned + b.unsigned,
        af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
        of := v.signed != a.signed + b.signed }
    { s with status }.setReg (.low r .W64) v

def adcRR (rd rs : Reg64) : X64M Unit :=
  modify fun s =>
    let a := s.regs.get64 rs
    let b := s.regs.get64 rd
    let c := s.status.cf
    let v := a + b + BitVec.ofNat 64 c.toNat
    let status := StatusFlags.from_result v
      { cf := v.unsigned != a.unsigned + b.unsigned + c.toNat,
        af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned + c.toNat,
        of := v.signed != a.signed + b.signed + c.toNat }
    { s with status }.setReg (.low rd .W64) v

def lea (dst : Reg64) (a : Addr) : X64M Unit :=
  modify fun s => s.setReg (.low dst .W64) (a.eval s)

/-- Read an 8-byte integer from `m` at `addr`, throwing on an unmapped address.
The data memory and address are explicit so the mapped-ness witness is a spec
premise rather than a state-dependent precondition, keeping `vcgen` stepping. -/
def loadIntM (m : DataMem) (addr : BitVec 64) : X64M Int := do
  match Mem.loadInt m addr 8 with
  | some i => pure i
  | none => throw (.nonmemLoad m addr .W64)

/-- Assert that `addr` is mapped in `m` (8 bytes), throwing otherwise, to gate a
store on the target being writable. -/
def checkMapped (m : DataMem) (addr : BitVec 64) : X64M Unit := do
  match Mem.loadInt m addr 8 with
  | some _ => pure ()
  | none => throw (.nonmemStore m addr .W64)

def movMI (a : Addr) (i : Int64) : X64M Unit := do
  let s ← get
  checkMapped s.dmem (a.eval s)
  modify fun s => s.setDmem (Mem.storeInt s.dmem (a.eval s) 8 (BitVec.setWidth 64 i.toBitVec).toInt)

def movMR (a : Addr) (src : Reg64) : X64M Unit := do
  let s ← get
  checkMapped s.dmem (a.eval s)
  modify fun s => s.setDmem (Mem.storeInt s.dmem (a.eval s) 8 (s.regs.get64 src).toInt)

def movRM (dst : Reg64) (a : Addr) : X64M Unit := do
  let s ← get
  let i ← loadIntM s.dmem (a.eval s)
  modify fun s => s.setReg (.low dst .W64) (BitVec.ofInt 64 i)

end Op

/-! ## Accessor-style `@[spec]` triples

The postcondition quantifies over a fresh post-state `sd'` characterized by
component equations (only the register file and the carry flag, the parts the
benchmark postconditions and later instructions read). Each transient wp goal
then carries `sd'` as an atom with a handful of equations, rather than a nested
state term. -/

section
variable (Q : Unit → MachineData → Prop) (E : X64Exit → MachineData → Prop)

@[spec] theorem Op.movRI_spec (r : Reg64) (i : Int64) :
    ⦃ fun sd => ∀ sd' : MachineData,
        sd'.regs = sd.regs.set64 r (BitVec.setWidth 64 i.toBitVec) →
        sd'.zmms = sd.zmms → sd'.status = sd.status → sd'.dmem = sd.dmem → Q () sd' ⦄
      Op.movRI r i ⦃ Q; E ⦄ := by
  apply Triple.intro; intro sd hsd; simp only [Op.movRI]; exact hsd _ rfl rfl rfl rfl

@[spec] theorem Op.movRR_spec (rd rs : Reg64) :
    ⦃ fun sd => ∀ sd' : MachineData,
        sd'.regs = sd.regs.set64 rd (sd.regs.get64 rs) →
        sd'.zmms = sd.zmms → sd'.status = sd.status → sd'.dmem = sd.dmem → Q () sd' ⦄
      Op.movRR rd rs ⦃ Q; E ⦄ := by
  apply Triple.intro; intro sd hsd; simp only [Op.movRR]; exact hsd _ rfl rfl rfl rfl

@[spec] theorem Op.decR_spec (r : Reg64) :
    ⦃ fun sd => ∀ sd' : MachineData,
        sd'.regs = sd.regs.set64 r (sd.regs.get64 r - 1) →
        sd'.zmms = sd.zmms → sd'.dmem = sd.dmem → sd'.status.cf = sd.status.cf → Q () sd' ⦄
      Op.decR r ⦃ Q; E ⦄ := by
  apply Triple.intro; intro sd hsd; simp only [Op.decR]; exact hsd _ rfl rfl rfl rfl

@[spec] theorem Op.addRI_spec (r : Reg64) (i : Int64) :
    ⦃ fun sd => ∀ sd' : MachineData,
        sd'.regs = sd.regs.set64 r (BitVec.setWidth 64 i.toBitVec + sd.regs.get64 r) →
        sd'.zmms = sd.zmms → sd'.dmem = sd.dmem →
        sd'.status.cf = ((BitVec.setWidth 64 i.toBitVec + sd.regs.get64 r).unsigned
          != (BitVec.setWidth 64 i.toBitVec).unsigned + (sd.regs.get64 r).unsigned) →
        Q () sd' ⦄
      Op.addRI r i ⦃ Q; E ⦄ := by
  apply Triple.intro; intro sd hsd; simp only [Op.addRI]; exact hsd _ rfl rfl rfl rfl

@[spec] theorem Op.adcRR_spec (rd rs : Reg64) :
    ⦃ fun sd => ∀ sd' : MachineData,
        sd'.regs = sd.regs.set64 rd
          (sd.regs.get64 rs + sd.regs.get64 rd + BitVec.ofNat 64 sd.status.cf.toNat) →
        sd'.zmms = sd.zmms → sd'.dmem = sd.dmem →
        sd'.status.cf = ((sd.regs.get64 rs + sd.regs.get64 rd + BitVec.ofNat 64 sd.status.cf.toNat).unsigned
          != (sd.regs.get64 rs).unsigned + (sd.regs.get64 rd).unsigned + sd.status.cf.toNat) →
        Q () sd' ⦄
      Op.adcRR rd rs ⦃ Q; E ⦄ := by
  apply Triple.intro; intro sd hsd; simp only [Op.adcRR]; exact hsd _ rfl rfl rfl rfl

@[spec] theorem Op.lea_spec (dst : Reg64) (a : Addr) :
    ⦃ fun sd => ∀ sd' : MachineData,
        sd'.regs = sd.regs.set64 dst (a.eval sd) →
        sd'.zmms = sd.zmms → sd'.status = sd.status → sd'.dmem = sd.dmem → Q () sd' ⦄
      Op.lea dst a ⦃ Q; E ⦄ := by
  apply Triple.intro; intro sd hsd; simp only [Op.lea]; exact hsd _ rfl rfl rfl rfl

end

/-! ### Memory primitive specs

`loadIntM`/`checkMapped` take the data memory and address explicitly, so the
mapped-ness witness `i : Int` is a spec premise and its equation
`Mem.loadInt m addr 8 = some i` is emitted as a side goal with `?i` undetermined
(the value flows into the pure continuation). `easm` discharges that side goal
from the internalized `h_load` facts, concretizing the sibling continuation VC. -/

@[spec] theorem loadIntM_spec (m : DataMem) (addr : BitVec 64) (i : Int)
    (Q : Int → MachineData → Prop) (E : X64Exit → MachineData → Prop)
    (h : Mem.loadInt m addr 8 = some i) :
    ⦃ fun st => Q i st ⦄ Op.loadIntM m addr ⦃ Q; E ⦄ := by
  apply Triple.intro; intro st hst
  simp only [Op.loadIntM, wp, WP.wpTrans, bind, EStateM.bind, pure, EStateM.pure, h]
  exact hst

@[spec] theorem checkMapped_spec (m : DataMem) (addr : BitVec 64) (i : Int)
    (Q : Unit → MachineData → Prop) (E : X64Exit → MachineData → Prop)
    (h : Mem.loadInt m addr 8 = some i) :
    ⦃ fun st => Q () st ⦄ Op.checkMapped m addr ⦃ Q; E ⦄ := by
  apply Triple.intro; intro st hst
  simp only [Op.checkMapped, wp, WP.wpTrans, bind, EStateM.bind, pure, EStateM.pure, h]
  exact hst
