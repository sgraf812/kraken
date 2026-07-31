/-
Per-instruction monadic actions over `X64M` and their `@[spec]` triples, plus
the register read-over-write API the benchmark postconditions are discharged
with.

The instruction bodies are the direct monadic transliterations of the
corresponding cases of `Operation.interp` in `Kraken/Semantics.lean`, including
the status-flag effects. Formal adequacy of these actions with respect to the
straightline interpreter is out of scope here.

Every triple applies the postcondition directly to the post-state, written as a
record update of the pre-state. A program's verification condition therefore
carries its state chain as nested record literals, with no state variables and
no component equations.
-/
import Kraken.OmniSemantics
import Kraken.GrindFold
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

@[simp, grind =] theorem Reg64s.get64_set64 (s : Reg64s) (r r' : Reg64) (v : Bv 64) :
    (s.set64 r v).get64 r' = if r' = r then v else s.get64 r' := by
  cases r <;> cases r' <;> simp [Reg64s.set64, Reg64s.get64]

@[simp, grind =] theorem Reg64s.get_low64 (s : Reg64s) (r : Reg64) :
    s.get (.low r .W64) = s.get64 r := by
  simp [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop]

@[simp, grind =] theorem Reg64s.set_low64 (s : Reg64s) (r : Reg64) (v : Bv 64) :
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

@[simp, grind =] theorem Reg64s.rax_set64 (s : Reg64s) (r : Reg64) (v : Bv 64) :
    (s.set64 r v).rax = if r = .rax then .ofBitVec v.toBitVec else s.rax := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rbx_set64 (s : Reg64s) (r : Reg64) (v : Bv 64) :
    (s.set64 r v).rbx = if r = .rbx then .ofBitVec v.toBitVec else s.rbx := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rcx_set64 (s : Reg64s) (r : Reg64) (v : Bv 64) :
    (s.set64 r v).rcx = if r = .rcx then .ofBitVec v.toBitVec else s.rcx := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rdx_set64 (s : Reg64s) (r : Reg64) (v : Bv 64) :
    (s.set64 r v).rdx = if r = .rdx then .ofBitVec v.toBitVec else s.rdx := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rsi_set64 (s : Reg64s) (r : Reg64) (v : Bv 64) :
    (s.set64 r v).rsi = if r = .rsi then .ofBitVec v.toBitVec else s.rsi := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rdi_set64 (s : Reg64s) (r : Reg64) (v : Bv 64) :
    (s.set64 r v).rdi = if r = .rdi then .ofBitVec v.toBitVec else s.rdi := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rsp_set64 (s : Reg64s) (r : Reg64) (v : Bv 64) :
    (s.set64 r v).rsp = if r = .rsp then .ofBitVec v.toBitVec else s.rsp := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rbp_set64 (s : Reg64s) (r : Reg64) (v : Bv 64) :
    (s.set64 r v).rbp = if r = .rbp then .ofBitVec v.toBitVec else s.rbp := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r8_set64 (s : Reg64s) (r : Reg64) (v : Bv 64) :
    (s.set64 r v).r8 = if r = .r8 then .ofBitVec v.toBitVec else s.r8 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r9_set64 (s : Reg64s) (r : Reg64) (v : Bv 64) :
    (s.set64 r v).r9 = if r = .r9 then .ofBitVec v.toBitVec else s.r9 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r10_set64 (s : Reg64s) (r : Reg64) (v : Bv 64) :
    (s.set64 r v).r10 = if r = .r10 then .ofBitVec v.toBitVec else s.r10 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r11_set64 (s : Reg64s) (r : Reg64) (v : Bv 64) :
    (s.set64 r v).r11 = if r = .r11 then .ofBitVec v.toBitVec else s.r11 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r12_set64 (s : Reg64s) (r : Reg64) (v : Bv 64) :
    (s.set64 r v).r12 = if r = .r12 then .ofBitVec v.toBitVec else s.r12 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r13_set64 (s : Reg64s) (r : Reg64) (v : Bv 64) :
    (s.set64 r v).r13 = if r = .r13 then .ofBitVec v.toBitVec else s.r13 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r14_set64 (s : Reg64s) (r : Reg64) (v : Bv 64) :
    (s.set64 r v).r14 = if r = .r14 then .ofBitVec v.toBitVec else s.r14 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r15_set64 (s : Reg64s) (r : Reg64) (v : Bv 64) :
    (s.set64 r v).r15 = if r = .r15 then .ofBitVec v.toBitVec else s.r15 := by cases r <;> simp [Reg64s.set64]

/-! ## Explicit addressing

A memory operand as a base register, an optional scaled index register, and a
displacement. `Addr.eval` is the 64-bit effective address, matching
`AddrExpr.interp` at address size 64 (register components are signed, the scale
multiplies the index, the sum is reduced modulo `2^64`). It takes the register
file, so a store address stays syntactically comparable to a later load address
across the intervening data-memory write. -/

structure Addr where
  base : Reg64
  index : Option (Reg64 × Int64) := none
  disp : Int64 := 0

def Addr.eval (a : Addr) (regs : Reg64s) : BitVec 64 :=
  let base := (regs.get64 a.base).toBitVec.toInt
  let idx := match a.index with
    | some (r, scale) => (regs.get64 r).toBitVec.toInt * scale.toInt
    | none => 0
  BitVec.ofInt 64 (base + idx + a.disp.toInt)

/-! ## Per-instruction monadic actions

Each register action is a single `modify`; the memory actions read the current
state, compute the effective address, and go through `Mem.loadInt`/`Mem.storeInt`.
Each body is the transliteration of the matching `Operation.interp` case (flag
effects included). The benchmark programs are do blocks of these actions. -/
namespace Op

def movRI (r : Reg64) (i : Int64) : X64M Unit :=
  modify (·.setReg (.low r .W64) (.ofBitVec (BitVec.setWidth 64 i.toBitVec)))

def movRR (rd rs : Reg64) : X64M Unit :=
  modify fun s => s.setReg (.low rd .W64) (s.regs.get64 rs)

def decR (r : Reg64) : X64M Unit :=
  modify fun s =>
    let a := (s.regs.get64 r).toBitVec
    let v := a - 1
    let status := StatusFlags.from_result v
      { cf := s.status.cf,
        af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
        of := v.signed != a.signed - 1 }
    { s with status }.setReg (.low r .W64) (.ofBitVec v)

def addRI (r : Reg64) (i : Int64) : X64M Unit :=
  modify fun s =>
    let a := BitVec.setWidth 64 i.toBitVec
    let b := (s.regs.get64 r).toBitVec
    let v := a + b
    let status := StatusFlags.from_result v
      { cf := v.unsigned != a.unsigned + b.unsigned,
        af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
        of := v.signed != a.signed + b.signed }
    { s with status }.setReg (.low r .W64) (.ofBitVec v)

def adcRR (rd rs : Reg64) : X64M Unit :=
  modify fun s =>
    let a := (s.regs.get64 rs).toBitVec
    let b := (s.regs.get64 rd).toBitVec
    let c := s.status.cf
    let v := a + b + BitVec.ofNat 64 c.toNat
    let status := StatusFlags.from_result v
      { cf := v.unsigned != a.unsigned + b.unsigned + c.toNat,
        af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned + c.toNat,
        of := v.signed != a.signed + b.signed + c.toNat }
    { s with status }.setReg (.low rd .W64) (.ofBitVec v)

def lea (dst : Reg64) (a : Addr) : X64M Unit :=
  modify fun s => s.setReg (.low dst .W64) (.ofBitVec (a.eval s.regs))

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
  checkMapped s.dmem (a.eval s.regs)
  modify fun s =>
    { s with dmem := Mem.storeInt s.dmem (a.eval s.regs) 8 (BitVec.setWidth 64 i.toBitVec).toInt }

def movMR (a : Addr) (src : Reg64) : X64M Unit := do
  let s ← get
  checkMapped s.dmem (a.eval s.regs)
  modify fun s =>
    { s with dmem := Mem.storeInt s.dmem (a.eval s.regs) 8 (s.regs.get64 src).toBitVec.toInt }

def movRM (dst : Reg64) (a : Addr) : X64M Unit := do
  let s ← get
  let i ← loadIntM s.dmem (a.eval s.regs)
  modify fun s => s.setReg (.low dst .W64) (.ofBitVec (BitVec.ofInt 64 i))

def xorRR (rd rs : Reg64) : X64M Unit :=
  modify fun s =>
    let v := (s.regs.get64 rd).toBitVec ^^^ (s.regs.get64 rs).toBitVec
    let status := StatusFlags.from_result v { cf := false, af := false, of := false }
    { s with status }.setReg (.low rd .W64) (.ofBitVec v)

/-- Fall through when `ZF` is set, jump to `l` otherwise. The taken branch leaves
the state monad through the `jump` exit; the fall-through is a `pure ()`. -/
def jnz (l : Int64) : X64M Unit := do
  let s ← get
  if s.status.zf then pure () else throw (.jump l)

/-- Push the 64-bit register `r`: decrement `rsp` by 8 and store the source at the
new top of stack, in one record update of the pre-state. -/
def pushR (r : Reg64) : X64M Unit := do
  let s ← get
  checkMapped s.dmem ((s.regs.get64 .rsp).toBitVec - 8#64)
  modify fun s =>
    let rsp := (s.regs.get64 .rsp).toBitVec - 8#64
    { s with
      regs := s.regs.set64 .rsp (.ofBitVec rsp)
      dmem := Mem.storeInt s.dmem rsp 8 (s.regs.get64 r).toBitVec.toInt }

/-- Pop into the 64-bit register `dst`: load from the top of stack, then increment
`rsp` by 8 and write the loaded value. -/
def popR (dst : Reg64) : X64M Unit := do
  let s ← get
  let i ← loadIntM s.dmem (s.regs.get64 .rsp).toBitVec
  modify fun s =>
    let regs := (s.regs.set64 .rsp (.ofBitVec ((s.regs.get64 .rsp).toBitVec + 8#64))).set64 dst (.ofBitVec (BitVec.ofInt 64 i))
    { s with regs }

/-- Add a memory operand into the 64-bit register `dst`: load the source from `a`
and add it to `dst`, with the status-flag effects of `add`. -/
def addRM (dst : Reg64) (a : Addr) : X64M Unit := do
  let s ← get
  let x ← loadIntM s.dmem (a.eval s.regs)
  modify fun s =>
    let av := BitVec.ofInt 64 x
    let bv := (s.regs.get64 dst).toBitVec
    let v := av + bv
    let status := StatusFlags.from_result v
      { cf := v.unsigned != av.unsigned + bv.unsigned,
        af := (v.take 4).unsigned != (av.take 4).unsigned + (bv.take 4).unsigned,
        of := v.signed != av.signed + bv.signed }
    { s with status }.setReg (.low dst .W64) (.ofBitVec v)

end Op

/-! ## Register instruction triples

The post-state is a record literal, so a spec application leaves the state one
record deep and every component the next instruction reads is a projection of a
literal. -/

section
variable (Q : Unit → MachineData → Prop) (E : X64Exit → MachineData → Prop)

@[spec] theorem Op.movRI_spec (r : Reg64) (i : Int64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 r (.ofBitVec (BitVec.setWidth 64 i.toBitVec)) } ⦄
      Op.movRI r i ⦃ Q; E ⦄ := by
  apply Triple.intro; intro s h; simp only [Op.movRI]; exact h

@[spec] theorem Op.movRR_spec (rd rs : Reg64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 rd (s.regs.get64 rs) } ⦄
      Op.movRR rd rs ⦃ Q; E ⦄ := by
  apply Triple.intro; intro s h; simp only [Op.movRR]; exact h

@[spec] theorem Op.decR_spec (r : Reg64) :
    ⦃ fun s =>
        Q () { s with
            regs := s.regs.set64 r (.ofBitVec ((s.regs.get64 r).toBitVec - 1))
            status := StatusFlags.from_result ((s.regs.get64 r).toBitVec - 1)
              { cf := s.status.cf,
                af := (((s.regs.get64 r).toBitVec - 1).take 4).unsigned
                  != ((s.regs.get64 r).toBitVec.take 4).unsigned - 1,
                of := ((s.regs.get64 r).toBitVec - 1).signed
                  != (s.regs.get64 r).toBitVec.signed - 1 } } ⦄
      Op.decR r ⦃ Q; E ⦄ := by
  apply Triple.intro; intro s h; simp only [Op.decR]; exact h

@[spec] theorem Op.addRI_spec (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        Q () { s with
            regs := s.regs.set64 r
              (.ofBitVec (BitVec.setWidth 64 i.toBitVec + (s.regs.get64 r).toBitVec))
            status := StatusFlags.from_result
              (BitVec.setWidth 64 i.toBitVec + (s.regs.get64 r).toBitVec)
              { cf := (BitVec.setWidth 64 i.toBitVec + (s.regs.get64 r).toBitVec).unsigned
                  != (BitVec.setWidth 64 i.toBitVec).unsigned
                    + (s.regs.get64 r).toBitVec.unsigned,
                af := ((BitVec.setWidth 64 i.toBitVec + (s.regs.get64 r).toBitVec).take 4).unsigned
                  != ((BitVec.setWidth 64 i.toBitVec).take 4).unsigned
                    + ((s.regs.get64 r).toBitVec.take 4).unsigned,
                of := (BitVec.setWidth 64 i.toBitVec + (s.regs.get64 r).toBitVec).signed
                  != (BitVec.setWidth 64 i.toBitVec).signed
                    + (s.regs.get64 r).toBitVec.signed } } ⦄
      Op.addRI r i ⦃ Q; E ⦄ := by
  apply Triple.intro; intro s h; simp only [Op.addRI]; exact h

@[spec] theorem Op.adcRR_spec (rd rs : Reg64) :
    ⦃ fun s =>
        Q () { s with
            regs := s.regs.set64 rd (.ofBitVec ((s.regs.get64 rs).toBitVec
              + (s.regs.get64 rd).toBitVec + BitVec.ofNat 64 s.status.cf.toNat))
            status := StatusFlags.from_result ((s.regs.get64 rs).toBitVec
                + (s.regs.get64 rd).toBitVec + BitVec.ofNat 64 s.status.cf.toNat)
              { cf := ((s.regs.get64 rs).toBitVec + (s.regs.get64 rd).toBitVec
                    + BitVec.ofNat 64 s.status.cf.toNat).unsigned
                  != (s.regs.get64 rs).toBitVec.unsigned + (s.regs.get64 rd).toBitVec.unsigned
                    + s.status.cf.toNat,
                af := (((s.regs.get64 rs).toBitVec + (s.regs.get64 rd).toBitVec
                    + BitVec.ofNat 64 s.status.cf.toNat).take 4).unsigned
                  != ((s.regs.get64 rs).toBitVec.take 4).unsigned
                    + ((s.regs.get64 rd).toBitVec.take 4).unsigned + s.status.cf.toNat,
                of := ((s.regs.get64 rs).toBitVec + (s.regs.get64 rd).toBitVec
                    + BitVec.ofNat 64 s.status.cf.toNat).signed
                  != (s.regs.get64 rs).toBitVec.signed + (s.regs.get64 rd).toBitVec.signed
                    + s.status.cf.toNat } } ⦄
      Op.adcRR rd rs ⦃ Q; E ⦄ := by
  apply Triple.intro; intro s h; simp only [Op.adcRR]; exact h

@[spec] theorem Op.lea_spec (dst : Reg64) (a : Addr) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 dst (.ofBitVec (a.eval s.regs)) } ⦄
      Op.lea dst a ⦃ Q; E ⦄ := by
  apply Triple.intro; intro s h; simp only [Op.lea]; exact h

@[spec] theorem Op.xorRR_spec (rd rs : Reg64) :
    ⦃ fun s =>
        Q () { s with
            regs := s.regs.set64 rd
              (.ofBitVec ((s.regs.get64 rd).toBitVec ^^^ (s.regs.get64 rs).toBitVec))
            status := StatusFlags.from_result
              ((s.regs.get64 rd).toBitVec ^^^ (s.regs.get64 rs).toBitVec)
              { cf := false, af := false, of := false } } ⦄
      Op.xorRR rd rs ⦃ Q; E ⦄ := by
  apply Triple.intro; intro s h; simp only [Op.xorRR]; exact h

set_option linter.unusedSimpArgs false in
@[spec] theorem Op.jnz_spec (l : Int64) :
    ⦃ fun s => if s.status.zf then Q () s else E (X64Exit.jump l) s ⦄
      Op.jnz l ⦃ Q; E ⦄ := by
  apply Triple.intro; intro s h
  cases hz : s.status.zf <;>
    simp only [Op.jnz, wp, WP.wpTrans, bind, EStateM.bind, get, getThe,
      MonadStateOf.get, EStateM.get, hz, EStateM.pure, EStateM.throw,
      Bool.false_eq_true, if_false, if_true, reduceIte] at h ⊢ <;>
    exact h

end

/-! ## Memory instruction triples

A memory access is mapped-ness plus a state update. The mapped-ness witness
`i : Int` is a theorem binder, an undetermined `?i` at application time, so its
equation sits in the precondition as a `Prop`-lattice meet conjunct alongside
the applied postcondition. `vcgen`'s lattice decomposition splits the meet,
emitting the equation as its own verification condition while stepping into the
continuation with the post-state literal. `easm` discharges the equation from
the internalized `h_load` facts, which concretizes the witness in the sibling
continuation. -/

section
open Lean.Order
variable (Q : Unit → MachineData → Prop) (E : X64Exit → MachineData → Prop)

@[spec] theorem Op.checkMapped_spec (m : DataMem) (addr : BitVec 64) (i : Int) :
    ⦃ fun s => (Mem.loadInt m addr 8 = some i) ⊓ Q () s ⦄ Op.checkMapped m addr ⦃ Q; E ⦄ := by
  apply Triple.intro; intro s hs
  rw [meet_prop_eq_and] at hs
  obtain ⟨h, hq⟩ := hs
  simp only [Op.checkMapped, wp, WP.wpTrans, pure, EStateM.pure, h]
  exact hq

@[spec] theorem Op.movMI_spec (a : Addr) (i : Int64) (v : Int) :
    ⦃ fun s => (Mem.loadInt s.dmem (a.eval s.regs) 8 = some v) ⊓
        Q () { s with
          dmem := Mem.storeInt s.dmem (a.eval s.regs) 8 (BitVec.setWidth 64 i.toBitVec).toInt } ⦄
      Op.movMI a i ⦃ Q; E ⦄ := by
  apply Triple.intro; intro s hs
  rw [meet_prop_eq_and] at hs
  obtain ⟨h, hq⟩ := hs
  simp only [Op.movMI, Op.checkMapped, wp, WP.wpTrans, bind, EStateM.bind, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet, h]
  exact hq

@[spec] theorem Op.movMR_spec (a : Addr) (src : Reg64) (v : Int) :
    ⦃ fun s => (Mem.loadInt s.dmem (a.eval s.regs) 8 = some v) ⊓
        Q () { s with
          dmem := Mem.storeInt s.dmem (a.eval s.regs) 8 (s.regs.get64 src).toBitVec.toInt } ⦄
      Op.movMR a src ⦃ Q; E ⦄ := by
  apply Triple.intro; intro s hs
  rw [meet_prop_eq_and] at hs
  obtain ⟨h, hq⟩ := hs
  simp only [Op.movMR, Op.checkMapped, wp, WP.wpTrans, bind, EStateM.bind, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet, h]
  exact hq

@[spec] theorem Op.movRM_spec (dst : Reg64) (a : Addr) (v : Int) :
    ⦃ fun s => (Mem.loadInt s.dmem (a.eval s.regs) 8 = some v) ⊓
        Q () { s with regs := s.regs.set64 dst (.ofBitVec (BitVec.ofInt 64 v)) } ⦄
      Op.movRM dst a ⦃ Q; E ⦄ := by
  apply Triple.intro; intro s hs
  rw [meet_prop_eq_and] at hs
  obtain ⟨h, hq⟩ := hs
  simp only [Op.movRM, Op.loadIntM, wp, WP.wpTrans, bind, EStateM.bind, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet, h]
  exact hq

@[spec] theorem Op.pushR_spec (r : Reg64) (v : Int) :
    ⦃ fun s => (Mem.loadInt s.dmem ((s.regs.get64 .rsp).toBitVec - 8#64) 8 = some v) ⊓
        Q () { s with
          regs := s.regs.set64 .rsp (.ofBitVec ((s.regs.get64 .rsp).toBitVec - 8#64))
          dmem := Mem.storeInt s.dmem ((s.regs.get64 .rsp).toBitVec - 8#64) 8
            (s.regs.get64 r).toBitVec.toInt } ⦄
      Op.pushR r ⦃ Q; E ⦄ := by
  apply Triple.intro; intro s hs
  rw [meet_prop_eq_and] at hs
  obtain ⟨h, hq⟩ := hs
  simp only [Op.pushR, Op.checkMapped, wp, WP.wpTrans, bind, EStateM.bind, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet, h]
  exact hq

@[spec] theorem Op.popR_spec (dst : Reg64) (v : Int) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 .rsp).toBitVec 8 = some v) ⊓
        Q () { s with regs := (s.regs.set64 .rsp (.ofBitVec ((s.regs.get64 .rsp).toBitVec + 8#64))).set64 dst (.ofBitVec (BitVec.ofInt 64 v)) } ⦄
      Op.popR dst ⦃ Q; E ⦄ := by
  apply Triple.intro; intro s hs
  rw [meet_prop_eq_and] at hs
  obtain ⟨h, hq⟩ := hs
  simp only [Op.popR, Op.loadIntM, wp, WP.wpTrans, bind, EStateM.bind, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet, h]
  exact hq

@[spec] theorem Op.addRM_spec (dst : Reg64) (a : Addr) (v : Int) :
    ⦃ fun s => (Mem.loadInt s.dmem (a.eval s.regs) 8 = some v) ⊓
        Q () { s with
            regs := s.regs.set64 dst
              (.ofBitVec (BitVec.ofInt 64 v + (s.regs.get64 dst).toBitVec))
            status := StatusFlags.from_result
              (BitVec.ofInt 64 v + (s.regs.get64 dst).toBitVec)
              { cf := (BitVec.ofInt 64 v + (s.regs.get64 dst).toBitVec).unsigned
                  != (BitVec.ofInt 64 v).unsigned + (s.regs.get64 dst).toBitVec.unsigned,
                af := ((BitVec.ofInt 64 v + (s.regs.get64 dst).toBitVec).take 4).unsigned
                  != ((BitVec.ofInt 64 v).take 4).unsigned
                    + ((s.regs.get64 dst).toBitVec.take 4).unsigned,
                of := (BitVec.ofInt 64 v + (s.regs.get64 dst).toBitVec).signed
                  != (BitVec.ofInt 64 v).signed + (s.regs.get64 dst).toBitVec.signed } } ⦄
      Op.addRM dst a ⦃ Q; E ⦄ := by
  apply Triple.intro; intro s hs
  rw [meet_prop_eq_and] at hs
  obtain ⟨h, hq⟩ := hs
  simp only [Op.addRM, Op.loadIntM, wp, WP.wpTrans, bind, EStateM.bind, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet, h]
  exact hq

end

-- The load primitive keeps its own triple: it leaves the state alone, so the
-- mapped-ness meet conjunct carries the whole precondition.
open Lean.Order in
@[spec] theorem Op.loadIntM_spec (m : DataMem) (addr : BitVec 64) (i : Int)
    (Q : Int → MachineData → Prop) (E : X64Exit → MachineData → Prop) :
    ⦃ fun s => (Mem.loadInt m addr 8 = some i) ⊓ Q i s ⦄ Op.loadIntM m addr ⦃ Q; E ⦄ := by
  apply Triple.intro; intro s hs
  rw [meet_prop_eq_and] at hs
  obtain ⟨h, hq⟩ := hs
  simp only [Op.loadIntM, wp, WP.wpTrans, pure, EStateM.pure, h]
  exact hq
