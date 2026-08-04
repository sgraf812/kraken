-- The reference semantics are taken from https://www.felixcloutier.com/x86/,
-- which itself is just extracted from https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html

import Lean
import Std
import Kraken.Syntax
import Kraken.Mem

-- injective coercions only
attribute [-instance] BitVec.instNatCast
attribute [-instance] BitVec.instIntCast
instance : Coe Bool Nat where coe := Bool.toNat
instance {n : Nat} : Coe Bool (BitVec n) where coe := fun b => BitVec.ofNat n b.toNat

def BitVec.unsigned {w} (x : BitVec w) : Int := x.toNat
def BitVec.signed {w} (x : BitVec w) : Int := x.toInt
def BitVec.take {w} (x : BitVec w) (n : Nat) : BitVec n := x.extractLsb' 0 n
def BitVec.drop {w} (x : BitVec w) (n : Nat) : BitVec (w - n) := x.extractLsb' n (w-n)
def BitVec.replaceLow {w n} (old : BitVec w) (new : BitVec n) : BitVec w :=
  (BitVec.append (old.drop n) new).setWidth _

namespace Reg
def base {w} (r : Reg w) : Reg64 := match r with
  | .low r _ => r
  | .ah => .rax | .bh => .rbx | .ch => .rcx | .dh => .rdx

def offset {w} (r : Reg w) : Nat := match r with
  | .low _ _ => 0
  | .ah | .bh | .ch | .dh => 8
end Reg

namespace AvxReg
def base {w} (r : AvxReg w) : RegMm := match r with
  | .xmm r => r
  | .ymm r => r
  | .zmm r => r
end AvxReg

structure Reg64s where
  rax : UInt64 := 0
  rbx : UInt64 := 0
  rcx : UInt64 := 0
  rdx : UInt64 := 0
  rsi : UInt64 := 0
  rdi : UInt64 := 0
  rsp : UInt64 := 0
  rbp : UInt64 := 0
  r8  : UInt64 := 0
  r9  : UInt64 := 0
  r10 : UInt64 := 0
  r11 : UInt64 := 0
  r12 : UInt64 := 0
  r13 : UInt64 := 0
  r14 : UInt64 := 0
  r15 : UInt64 := 0
  deriving Repr, BEq, DecidableEq, Hashable, Hashable, Lean.ToExpr

/-- The 64-bit register file is stated at the literal width, so a read's bits
carry `64` rather than an unreduced `Width.bits`. -/
def Reg64s.get64 (s : Reg64s) (r : Reg64) : Bv 64 := .ofBitVec (UInt64.toBitVec (match r with
  | .rax => s.rax | .rbx => s.rbx | .rcx => s.rcx | .rdx => s.rdx
  | .rsi => s.rsi | .rdi => s.rdi | .rsp => s.rsp | .rbp => s.rbp
  | .r8  => s.r8  | .r9  => s.r9  | .r10 => s.r10 | .r11 => s.r11
  | .r12 => s.r12 | .r13 => s.r13 | .r14 => s.r14 | .r15 => s.r15))

def Reg64s.set64 (regs : Reg64s) (r : Reg64) (v : Bv 64) : Reg64s :=
  let  v := UInt64.ofBitVec v.toBitVec
  match r with
  | .rax => { regs with rax := v } | .rbx => { regs with rbx := v }
  | .rcx => { regs with rcx := v } | .rdx => { regs with rdx := v }
  | .rsi => { regs with rsi := v } | .rdi => { regs with rdi := v }
  | .rsp => { regs with rsp := v } | .rbp => { regs with rbp := v }
  | .r8  => { regs with r8  := v } | .r9  => { regs with r9  := v }
  | .r10 => { regs with r10 := v } | .r11 => { regs with r11 := v }
  | .r12 => { regs with r12 := v } | .r13 => { regs with r13 := v }
  | .r14 => { regs with r14 := v } | .r15 => { regs with r15 := v }

def Reg64s.get (s : Reg64s) {w} (r : Reg w) : w.type :=
  .ofBitVec (((s.get64 r.base).toBitVec.drop r.offset).take w.bits)
  -- BitVec because it may be signed or unsigned depending on context

def Reg64s.set (s : Reg64s) {w} (r : Reg w) (v : w.type) : Reg64s := match r with
  | .low r .W64 => s.set64 r v
  | .low r .W32 => s.set64 r (.ofBitVec (v.toBitVec.zeroExtend _))
  | .low r w => s.set64 r (.ofBitVec ((s.get64 r).toBitVec.replaceLow v.toBitVec))
  | .ah | .bh | .ch | .dh => let old := (s.get64 r.base).toBitVec;
    s.set64 r.base (.ofBitVec
      (old.replaceLow (BitVec.append v.toBitVec (s.get (.low r.base .W8)).toBitVec)))

def ZmmValue : Type := BitVec 512
  deriving Repr, BEq, DecidableEq, Hashable, Hashable, Lean.ToExpr

def zmmZero : ZmmValue := 0#512

structure RegZmms where
  zmm0  : ZmmValue := zmmZero
  zmm1  : ZmmValue := zmmZero
  zmm2  : ZmmValue := zmmZero
  zmm3  : ZmmValue := zmmZero
  zmm4  : ZmmValue := zmmZero
  zmm5  : ZmmValue := zmmZero
  zmm6  : ZmmValue := zmmZero
  zmm7  : ZmmValue := zmmZero
  zmm8  : ZmmValue := zmmZero
  zmm9  : ZmmValue := zmmZero
  zmm10 : ZmmValue := zmmZero
  zmm11 : ZmmValue := zmmZero
  zmm12 : ZmmValue := zmmZero
  zmm13 : ZmmValue := zmmZero
  zmm14 : ZmmValue := zmmZero
  zmm15 : ZmmValue := zmmZero
  zmm16 : ZmmValue := zmmZero
  zmm17 : ZmmValue := zmmZero
  zmm18 : ZmmValue := zmmZero
  zmm19 : ZmmValue := zmmZero
  zmm20 : ZmmValue := zmmZero
  zmm21 : ZmmValue := zmmZero
  zmm22 : ZmmValue := zmmZero
  zmm23 : ZmmValue := zmmZero
  zmm24 : ZmmValue := zmmZero
  zmm25 : ZmmValue := zmmZero
  zmm26 : ZmmValue := zmmZero
  zmm27 : ZmmValue := zmmZero
  zmm28 : ZmmValue := zmmZero
  zmm29 : ZmmValue := zmmZero
  zmm30 : ZmmValue := zmmZero
  zmm31 : ZmmValue := zmmZero
  zmm32 : ZmmValue := zmmZero
  deriving Repr, BEq, DecidableEq, Hashable, Hashable, Lean.ToExpr

def RegZmms.get512 (s : RegZmms) (r : RegMm) : AvxWidth.W512.type := (match r with
  | .mm0  => s.zmm0  | .mm1  => s.zmm1  | .mm2  => s.zmm2  | .mm3  => s.zmm3
  | .mm4  => s.zmm4  | .mm5  => s.zmm5  | .mm6  => s.zmm6  | .mm7  => s.zmm7
  | .mm8  => s.zmm8  | .mm9  => s.zmm9  | .mm10 => s.zmm10 | .mm11 => s.zmm11
  | .mm12 => s.zmm12 | .mm13 => s.zmm13 | .mm14 => s.zmm14 | .mm15 => s.zmm15
  | .mm16 => s.zmm16 | .mm17 => s.zmm17 | .mm18 => s.zmm18 | .mm19 => s.zmm19
  | .mm20 => s.zmm20 | .mm21 => s.zmm21 | .mm22 => s.zmm22 | .mm23 => s.zmm23
  | .mm24 => s.zmm24 | .mm25 => s.zmm25 | .mm26 => s.zmm26 | .mm27 => s.zmm27
  | .mm28 => s.zmm28 | .mm29 => s.zmm29 | .mm30 => s.zmm30 | .mm31 => s.zmm31)

def RegZmms.set512 (regs : RegZmms) (r : RegMm) (v : AvxWidth.W512.type) : RegZmms :=
  match r with
  | .mm0  => { regs with zmm0  := v } | .mm1  => { regs with zmm1  := v }
  | .mm2  => { regs with zmm2  := v } | .mm3  => { regs with zmm3  := v }
  | .mm4  => { regs with zmm4  := v } | .mm5  => { regs with zmm5  := v }
  | .mm6  => { regs with zmm6  := v } | .mm7  => { regs with zmm7  := v }
  | .mm8  => { regs with zmm8  := v } | .mm9  => { regs with zmm9  := v }
  | .mm10 => { regs with zmm10 := v } | .mm11 => { regs with zmm11 := v }
  | .mm12 => { regs with zmm12 := v } | .mm13 => { regs with zmm13 := v }
  | .mm14 => { regs with zmm14 := v } | .mm15 => { regs with zmm15 := v }
  | .mm16 => { regs with zmm16 := v } | .mm17 => { regs with zmm17 := v }
  | .mm18 => { regs with zmm18 := v } | .mm19 => { regs with zmm19 := v }
  | .mm20 => { regs with zmm20 := v } | .mm21 => { regs with zmm21 := v }
  | .mm22 => { regs with zmm22 := v } | .mm23 => { regs with zmm23 := v }
  | .mm24 => { regs with zmm24 := v } | .mm25 => { regs with zmm25 := v }
  | .mm26 => { regs with zmm26 := v } | .mm27 => { regs with zmm27 := v }
  | .mm28 => { regs with zmm28 := v } | .mm29 => { regs with zmm29 := v }
  | .mm30 => { regs with zmm30 := v } | .mm31 => { regs with zmm31 := v }

def RegZmms.get (s : RegZmms) {w} (r : AvxReg w) : w.type :=
  (s.get512 r.base).take w.bits

def RegZmms.set (s : RegZmms) {w} (r : AvxReg w) (v : w.type) : RegZmms := match r with
  | .zmm r => s.set512 r v
  | .ymm r => s.set512 r (v.zeroExtend _)
  | .xmm r => s.set512 r (v.zeroExtend _)

def RegZmms.setLegacy (s : RegZmms) {w} (r : AvxReg w) (v : w.type) : RegZmms := match r with
  | .zmm r => s.set512 r v  -- impossible
  | .ymm r => s.set512 r ((s.get512 r).replaceLow v)  -- impossible
  | .xmm r => s.set512 r ((s.get512 r).replaceLow v)

structure Labels where label : Label → Int64

structure StatusFlags where
  cf : Bool
  pf : Bool
  af : Bool
  zf : Bool
  sf : Bool
  of : Bool
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

abbrev DataMem := Mem 64
instance : Repr DataMem where reprPrec _ _ := "<opaque memory>"
structure MachineData where -- does not include code or program position
  regs : Reg64s := {}
  zmms : RegZmms := {}
  status : StatusFlags := .mk false false false false false false
  dmem : DataMem := ∅
  deriving Repr, BEq, DecidableEq

/-- Exceptional exits from a monadic run of the instruction semantics.
`jump` carries a control-flow target out of the state monad; the remaining
constructors flag effects the straightline model leaves unresolved. -/
inductive X64Exit
  | jump (pc : Int64)
  | unimplemented (msg : String)
  | nonmemLoad (dmem : DataMem) (addr : BitVec 64) (w : Width)
  | nonmemStore (dmem : DataMem) (addr : BitVec 64) (w : Width)
  | undefinedFlags
  deriving Repr

/-- The instruction-semantics monad: error-state over `MachineData`. -/
abbrev X64M := EStateM X64Exit MachineData

section Interp

variable (labels : Labels) (address_size : AddressSize)

def BitVec.toAddressSize (w: BitVec 64): BitVec address_size.address_size.bits :=
  w.take address_size.address_size.bits

-- A load inside the mapped data memory returns the stored value. Outside it,
-- straightline execution throws: MMIO and other nonmemory effects are not modeled.
def MachineData.load (addr : BitVec 64) (w : Width) : X64M (BitVec w.bits) := do
  let s ← get
  match Mem.loadInt s.dmem addr w.bytes with
  | .some i => pure (.ofInt _ i)
  | .none => throw (.nonmemLoad s.dmem addr w)

def MachineData.loadAvx (addr : BitVec 64) (w : AvxWidth) : X64M w.type := do
  let s ← get
  match Mem.loadInt s.dmem addr w.bytes with
  | .some i => pure (.ofInt _ i)
  | .none => throw (.unimplemented "AVX nonmem load not supported")

def MachineData.store (addr : BitVec 64) {w : Width} (v : BitVec w.bits) : X64M Unit := do
  let s ← get
  match Mem.loadInt s.dmem addr w.bytes with
  | .some _ => set { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }
  | .none => throw (.nonmemStore s.dmem addr w)

def MachineData.storeAvx (addr : BitVec 64) {w : AvxWidth} (v : w.type) : X64M Unit := do
  let s ← get
  match Mem.loadInt s.dmem addr w.bytes with
  | .some _ => set { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }
  | .none => throw (.unimplemented "AVX nonmem store not supported")

def ConstExpr.interp : ConstExpr → Std.Rco _root_.Int64 → _root_.Int64
  | .label l, _ => labels.label l
  | .int64 i, _ => i
  | .before_current_instruction, r => r.lower
  | .after_current_instruction, r => r.upper
  | .add e1 e2, p => e1.interp p + e2.interp p
  | .sub e1 e2, p => e1.interp p - e2.interp p

def AddrExpr.interp (a : AddrExpr) (s : Reg64s) (p : Std.Rco Int64) :=
  let base := match a.base with
              | .some (.reg r) => ((s.get64 r).toBitVec.toAddressSize address_size).signed
              | .some .rip => p.upper.toInt
              | .none => 0
  let idx := match a.idx with
             | .some ⟨r, c⟩ => ((s.get64 r).toBitVec.toAddressSize address_size).signed * c.bytes
             | .none => 0
  BitVec.ofInt address_size.address_size.bits (base + idx + (a.disp.interp labels p).toInt)

def Reg.interp {w} (r : Reg w) : X64M (BitVec w.bits) := do
  return ((← get).regs.get r).toBitVec

def RegOrMem.interp {w} (o : RegOrMem w) (p : Std.Rco Int64) : X64M (BitVec w.bits) := do
  match o with
  | .reg r => return ((← get).regs.get r).toBitVec
  | .mem a => MachineData.load ((a.interp labels address_size (← get).regs p).zeroExtend _) w

def AvxRegOrMem.interp {w} (o : AvxRegOrMem w) (p : Std.Rco Int64) : X64M w.type := do
  match o with
  | .avx r => return (← get).zmms.get r
  | .mem a => MachineData.loadAvx ((a.interp labels address_size (← get).regs p).zeroExtend _) w

def MachineData.setReg (s : MachineData) {w} (r : Reg w) (v : w.type) : MachineData :=
  { s with regs := s.regs.set r v }

def MachineData.setAvxReg (s : MachineData) {w : AvxWidth} (r : AvxReg w) (v : w.type) : MachineData :=
  { s with zmms := s.zmms.set r v }

def MachineData.setAvxLegacyReg (s : MachineData) {w : AvxWidth} (r : AvxReg w) (v : w.type) : MachineData :=
  { s with zmms := s.zmms.setLegacy r v }

def MachineData.set {w} (d : Dst w) (v : BitVec w.bits) (p : Std.Rco Int64) : X64M Unit := do
  match d with
  | .reg r => modify (·.setReg r (.ofBitVec v))
  | .mem a => MachineData.store ((a.interp labels address_size (← get).regs p).zeroExtend _) v

def MachineData.setAvx {aw} (d : AvxDst aw) (v : aw.type) (p : Std.Rco Int64) : X64M Unit := do
  match d with
  | .avx r => modify (·.setAvxReg r v)
  | .mem a => MachineData.storeAvx ((a.interp labels address_size (← get).regs p).zeroExtend _) v

def MachineData.setAvxLegacy {w} (d : AvxDst w) (v : w.type) (p : Std.Rco Int64) : X64M Unit := do
  match d with
  | .avx r => modify (·.setAvxLegacyReg r v)
  | .mem a => MachineData.storeAvx ((a.interp labels address_size (← get).regs p).zeroExtend _) v

def Operand.interp {w} (o : Operand w) (p : Std.Rco Int64) : X64M (BitVec w.bits) := do
  match o with
  | .regOrMem rm => rm.interp labels address_size p
  | .imm v => pure ((v.interp labels p).toBitVec.truncate _)

def AvxOperand.interp {aw} (o : AvxOperand aw) (p : Std.Rco Int64) : X64M aw.type := do
  match o with
  | .regOrMem rm => rm.interp labels address_size p

def CondCode.interp (cc : CondCode) (s : StatusFlags) : Bool := match cc with
  | .z  => s.zf | .nz => !s.zf | .c  => s.cf | .nc => !s.cf
  | .a  => !s.cf && !s.zf | .be => s.cf || s.zf

def ShiftCountExpr.interp (c : ShiftCountExpr) (s : MachineData) (p : Std.Rco Int64) := match c with
  | .cl => s.regs.rcx.toBitVec.take 8
  | .imm8 v => (v.interp labels p).toBitVec.take _
def ShiftCountExpr.interpMasked (c : ShiftCountExpr) (s : MachineData) (p : Std.Rco Int64) (w : Width) : Nat :=
  (c.interp labels s p).toNat &&& match w with | .W64 => 0x3f | _ => 0x1f

def RelRegOrMem.interp (o : RelRegOrMem) (p : Std.Rco Int64) : X64M (BitVec 64) := do
  match o with
  | .rel c => pure (p.upper + c.interp labels p).toBitVec
  | .reg r => return ((← get).regs.get r).toBitVec
  | .mem a => MachineData.load ((a.interp labels address_size (← get).regs p).zeroExtend _) .W64

structure StatusFlags.from_result.Remaining where
  cf : Bool
  af : Bool
  of : Bool
  deriving Repr, BEq, DecidableEq

-- TEMPORARY: definitions stolen from Lean 4.28's standard library, but with a
-- different name so that this file builds with both 4.27 and 4.28
namespace BitVec
def cpopNatRec_ {w} (x : BitVec w) (pos acc : Nat) : Nat :=
  match pos with
  | 0 => acc
  | n + 1 => x.cpopNatRec_ n (acc + (x.getLsbD n).toNat)

def cpop_ {w} (x : BitVec w) : BitVec w := BitVec.ofNat w (cpopNatRec_ x w 0)
end BitVec

def StatusFlags.from_result {w} (result : BitVec w) (f : from_result.Remaining) : StatusFlags :=
  { pf := (result.take 8).cpop_ % 2 == BitVec.zero _
    zf := result == BitVec.zero _
    sf := result.msb, cf := f.cf, af := f.af, of := f.of }

set_option maxHeartbeats 1000000
def Operation.interp {w} (i : Operation w) (p : Std.Rco Int64) : X64M Unit := do
  match i with
  | .mov dst src =>
    let val ← src.interp labels address_size p
    MachineData.set labels address_size dst val p
  | .movsx dst src =>
    let val ← src.interp labels address_size p
    MachineData.set labels address_size dst (val.signExtend _) p
  | .movzx dst src =>
    let val ← src.interp labels address_size p
    MachineData.set labels address_size dst (val.zeroExtend _) p
  | .push src =>
    let v ← src.interp labels address_size p
    let s ← get
    let rsp := (s.regs.get64 .rsp).toBitVec - w.bytesv
    -- The store precedes the rsp commit, so a faulting push leaves rsp at its
    -- original value, as a restartable fault requires.
    MachineData.store rsp v
    modify (fun s => { s with regs := s.regs.set64 .rsp (.ofBitVec rsp) })
  | .pop dst =>
    let rsp := ((← get).regs.get64 .rsp).toBitVec
    let val ← MachineData.load rsp w
    modify (fun s => { s with regs := s.regs.set64 .rsp (.ofBitVec (rsp + w.bytesv)) })
    MachineData.set labels address_size dst val p
  | .setcc cc dst =>
    MachineData.set labels address_size dst (cc.interp (← get).status) p
  | .cmovcc cc dst src =>
    let src ← src.interp labels address_size p
    let s ← get
    let v := if cc.interp s.status then src else (s.regs.get dst).toBitVec
    set (s.setReg dst (.ofBitVec v))
-- Arithmetic
  | .lea dst src =>
    let s ← get
    set (s.setReg dst (.ofBitVec ((src.interp labels address_size s.regs p).zeroExtend _)))
  | .add dst src =>
    let a ← src.interp labels address_size p
    let b ← dst.interp labels address_size p
    let v := a + b
    let status := StatusFlags.from_result v {
      cf := v.unsigned != a.unsigned + b.unsigned
      af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
      of := v.signed != a.signed + b.signed }
    modify (fun s => { s with status })
    MachineData.set labels address_size dst v p
  | .adc dst src =>
    let a ← src.interp labels address_size p
    let b ← dst.interp labels address_size p
    let c := (← get).status.cf
    let v := a + b + c
    let status := StatusFlags.from_result v {
      cf := v.unsigned != a.unsigned + b.unsigned + c
      af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned + c,
      of := v.signed != a.signed + b.signed + c }
    modify (fun s => { s with status })
    MachineData.set labels address_size dst v p
  | .adcx dst src =>
    let a ← src.interp labels address_size p
    let s ← get
    let b := (s.regs.get dst).toBitVec
    let v := a + b + s.status.cf
    let cf := v.unsigned != a.unsigned + b.unsigned + s.status.cf
    set { s with regs := s.regs.set dst (.ofBitVec v), status := { s.status with cf := cf } }
  | .adox dst src =>
    let a ← src.interp labels address_size p
    let s ← get
    let b := (s.regs.get dst).toBitVec
    let v := a + b + s.status.of
    let of := v.unsigned != a.unsigned + b.unsigned + s.status.of
    set { s with regs := s.regs.set dst (.ofBitVec v), status := { s.status with of := of } }
  | .inc dst =>
    let a ← dst.interp labels address_size p
    let cf := (← get).status.cf
    let v := a + 1
    let status := StatusFlags.from_result v {
      cf := cf
      af := (v.take 4).unsigned != (a.take 4).unsigned + 1,
      of := v.signed != a.signed + 1 }
    modify (fun s => { s with status })
    MachineData.set labels address_size dst v p
  | .dec dst =>
    let a ← dst.interp labels address_size p
    let cf := (← get).status.cf
    let v := a - 1
    let status := StatusFlags.from_result v {
      cf := cf
      af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
      of := v.signed != a.signed - 1 }
    modify (fun s => { s with status })
    MachineData.set labels address_size dst v p
  | .neg dst =>
    let b ← dst.interp labels address_size p
    let v := -b
    let status := StatusFlags.from_result v {
      cf := b != 0
      af := (b.take 4) != 0,
      of := v.signed != - b.signed }
    modify (fun s => { s with status })
    MachineData.set labels address_size dst v p
  | .sub dst src =>
    let a ← src.interp labels address_size p
    let b ← dst.interp labels address_size p
    let v := b - a
    let status := StatusFlags.from_result v {
      cf := v.unsigned != b.unsigned - a.unsigned
      af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
      of := v.signed != b.signed - a.signed }
    modify (fun s => { s with status })
    MachineData.set labels address_size dst v p
  | .sbb dst src =>
    let a ← src.interp labels address_size p
    let b ← dst.interp labels address_size p
    let c := (← get).status.cf
    let v := b - a - c
    let status := StatusFlags.from_result v {
      cf := v.unsigned != b.unsigned - a.unsigned - c
      af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - c,
      of := v.signed != b.signed - a.signed - c }
    modify (fun s => { s with status })
    MachineData.set labels address_size dst v p
  | .cmp a b =>
    let a ← a.interp labels address_size p
    let b ← b.interp labels address_size p
    let v := a - b
    let status := StatusFlags.from_result v {
      cf := v.unsigned != a.unsigned - b.unsigned
      af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
      of := v.signed != a.signed - b.signed }
    modify (fun s => { s with status })
  | .mulx r_hi r_lo src1 =>
    let a ← src1.interp labels address_size p
    let s ← get
    let b := (s.regs.get (.low .rdx w)).toBitVec
    let v := a.unsigned * b.unsigned
    modify (fun s =>
      (s.setReg r_lo (.ofBitVec (.ofInt _ v))).setReg r_hi (.ofBitVec (.ofInt _ (v >>> w.bits))))
  | .not dst =>
    let a ← dst.interp labels address_size p
    MachineData.set labels address_size dst (~~~a) p
  | .bswap dst =>
    let a := ((← get).regs.get dst).toBitVec
    match w with
    | .W32 =>
      let v := a.take 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.drop 24
      modify (fun s => s.setReg dst (.ofBitVec (v.setWidth _)))
    | .W64 =>
      let v := a.take 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8
            ++ a.extractLsb' 32 8 ++ a.extractLsb' 40 8 ++ a.extractLsb' 48 8 ++ a.drop 56
      modify (fun s => s.setReg dst (.ofBitVec (v.setWidth _)))
    | _ => throw .undefinedFlags -- TODO: model undefined flags for bswap on W8/W16
  | .jcc cc l =>
    if cc.interp (← get).status
    then throw (.jump (labels.label l))
    else pure ()
  | .jmp tgt =>
    let a ← tgt.interp labels address_size p
    throw (.jump (.ofBitVec a))
  | .call tgt =>
    let a ← tgt.interp labels address_size p
    let s ← get
    let rsp := (s.regs.get64 .rsp).toBitVec - Width.W64.bytesv
    set { s with regs := s.regs.set64 .rsp (.ofBitVec rsp) }
    MachineData.store rsp (w := .W64) p.upper.toBitVec
    throw (.jump (.ofBitVec a))
  | .ret =>
    let rsp := ((← get).regs.get64 .rsp).toBitVec
    let ra ← MachineData.load rsp .W64
    modify (fun s => { s with regs := s.regs.set64 .rsp (.ofBitVec (rsp + 8)) })
    throw (.jump (.ofBitVec ra))
  | nop _ | nopalign _ _ => pure ()
  -- TODO: the following instructions leave some status flags undefined; the
  -- straightline model throws rather than committing to a nondeterministic value.
  | .mul .. | .imul1 .. | .imul .. | .test .. | .and .. | .or .. | .xor ..
  | .shl .. | .shr .. | .sar .. | .shld .. | .shrd ..
  | .rol .. | .ror .. | .rcl .. | .rcr .. => throw .undefinedFlags

-- AVX Operations Interpreter
def AvxOperation.interp {w} (i : AvxOperation w) (p : Std.Rco Int64) : X64M Unit := do
  match i with
  | .movups dst src =>
    let val ← src.interp labels address_size p
    MachineData.setAvxLegacy labels address_size dst val p
  | .vmovups dst src =>
    let val ← src.interp labels address_size p
    MachineData.setAvx labels address_size dst val p

end Interp

def Instr.interp (labels : Labels) (i : Instr) (p : Std.Rco Int64) : X64M Unit :=
  match i with
    | .regular addr_sz op_sz op =>
        Operation.interp (w := op_sz) labels (.mk addr_sz) op p
    | .avx addr_sz op_sz op =>
        AvxOperation.interp (w := op_sz) labels (.mk addr_sz) op p

def Directive.interp (labels : Labels) (d : Directive) (p : Std.Rco Int64) : X64M Unit :=
  match d with
  | .label _ => pure ()
  | .instr i => i.interp labels p
  | .byteArray _ => throw (.unimplemented s!"Unimplemented: execution reached data block at {p.1}")

def Directives.interp (labels : Labels)
  (ds : List (Directive × Nat)) (pc : Int64) : X64M Int64 := do
  match ds with
  | [] => pure pc
  | (d, sz) :: ds =>
    d.interp labels (.mk pc (pc+.ofNat sz))
    Directives.interp labels ds (pc+.ofNat sz)

class Layout where (start : Int64) (size : Nat → Nat)
def Layout.apply (l : Layout) (prog : Program) : Executable :=
  (l.start, prog.mapIdx (fun i d => (d, l.size i)))
instance : CoeFun Layout (fun _ => Program → Executable) where coe := Layout.apply

def Executable.withAddresses (e : Executable)  : List (Int64 × Directive × Nat) :=
  (List.scanl (fun (p, _, _) (d, z) => (p+.ofNat z, d, z)) (e.1, .byteArray (.mk #[]), 0) e.2)

@[instance_reducible] def Executable.labels (e : Executable) : Labels :=
  { label l := (e.withAddresses.findSome?
      (fun (p, d, _) => if d = .label l then .some p else .none)).getD (-1) }

def Executable.directivesAtAddress (e : Executable) (a : Int64) : List (Directive × Nat) :=
  (e.withAddresses.filter (·.1 = a)).map (·.2)

def Executable.directivesFromAddress (e : Executable) (a : Int64) : List (Directive × Nat) :=
  e.2.drop (((e.withAddresses).map (·.1)).idxOf a)

def Executable.directivesFromLabel (e : Executable) (l : Label) : List (Directive × Nat) :=
  e.2.dropWhile (·.1 != .label l)

abbrev MachineState := MachineData × Int64

def Executable.step (e : Executable) (pc : Int64) : X64M Int64 :=
  Directives.interp e.labels (e.directivesAtAddress pc) pc

def Executable.straightline (e : Executable) (pc : Int64) : X64M Int64 :=
  Directives.interp e.labels (e.directivesFromAddress pc) pc

-- -- Concrete evaluators for expedient testing

partial def Executable.eval (e : Executable) (s : MachineState) (until_ : MachineState → Bool) : Except String (MachineState) :=
  if until_ s then .ok s else
  match (e.straightline s.2).run s.1 with
  | .ok pc s' => eval e (s', pc) until_
  | .error (.jump pc) s' => eval e (s', pc) until_
  | .error (.unimplemented msg) _ => .error msg
  | .error (.nonmemLoad _ addr _) _ => .error s!"Load at unmapped address {repr addr}"
  | .error (.nonmemStore _ addr _) _ => .error s!"Store at unmapped address {repr addr}"
  | .error .undefinedFlags _ => .error "undefined flags encountered"

def Directive.fakeSize (hashOfProgram : UInt64) (d : Directive) : Nat :=
  match d with
  | .label _ => 0
  | .instr (.regular _ _ (.nop sz)) => sz -- may be zero
  | .instr i => (1 + hash (hashOfProgram, i) % 15).toNat
  | .byteArray bs => bs.size

def Program.fakeLayout (prog : Program) : Executable :=
  let : Inhabited Directive := .mk (.byteArray (.mk #[]))
  let h := hash prog;
  let layout : Layout := { start := h.toInt64<<<16, size i := prog[i]!.fakeSize h }
  layout prog

abbrev eval [layout : Layout] (prog : Program) := (layout prog).eval

/-- info: Except.ok 42 -/
#guard_msgs in
#eval
  let exe := Program.fakeLayout [
    .label "main",
    .instr (.regular .W64 .W64 (.lea (.low .rax .W64) (.mk .none .none (.int64 41)))),
    .instr (.regular .W64 .W64 (.inc (.reg (.low .rax .W64)))),
    .instr (.regular .W64 .W64 .ret) ]
  let start := exe.labels.label "main"
  let data := { dmem := Mem.storeInt {} 0x100 8 0x1337, regs := {rsp := 0x100} }
  (exe.eval (data, start) (fun (_, pc) => pc = 0x1337)).bind (fun s => .ok s.1.regs.rax)
