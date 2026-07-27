/-
Accessor-style instruction specs: the continuation is quantified over a fresh
post-state characterized by component equations, so goals accumulate one
constant and a few equations per step instead of a nested state term.
-/
import Kraken.VCGenSpike

set_option mvcgen.warning false
set_option grind.warning false

open Std.Internal.Do

/- Carry-chain theory: `.unsigned` is a homomorphism into the integers; the
carry chains fold in the lia solver through the BitVec/UInt64 hom rule sets. -/
@[grind hom] theorem BitVec.unsigned_hom {w} (x : BitVec w) : x.unsigned = (x.toNat : Int) := rfl

@[sym_simp, simp, grind =] theorem StatusFlags.cf_from_result {w} (v : BitVec w)
    (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result v f).cf = f.cf := rfl

section
variable (labels : Labels) (address_size : AddressSize)
  (p : Std.Rco Int64) (s : MachineData)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects)
  (post : MachineState → Prop) (epost : EPost.Nil)

@[spec high] theorem Operation.mov_ri_acc (r : Reg64) (i : Int64) :
    ⦃ ∀ s' : MachineData,
        s'.regs = s.regs.set64 r (BitVec.setWidth 64 i.toBitVec) →
        s'.zmms = s.zmms → s'.status = s.status → s'.dmem = s.dmem →
        wp (next s') post epost ⦄
      Operation.interp labels address_size (.mov (.reg (.low r .W64)) (.imm (.int64 i))) p s next jmp
      ⦃ post; epost ⦄ := by
  constructor
  intro h
  show wp (Operation.interp _ _ _ _ _ _ _) _ _
  simp only [Operation.interp, Operand.interp, ConstExpr.interp, MachineData.set,
    MachineData.setReg, Reg64s.set_low64]
  exact h _ rfl rfl rfl rfl

@[spec high] theorem Operation.mov_rr_acc (rd rs : Reg64) :
    ⦃ ∀ s' : MachineData,
        s'.regs = s.regs.set64 rd (s.regs.get64 rs) →
        s'.zmms = s.zmms → s'.status = s.status → s'.dmem = s.dmem →
        wp (next s') post epost ⦄
      Operation.interp labels address_size
        (.mov (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))) p s next jmp
      ⦃ post; epost ⦄ := by
  constructor
  intro h
  show wp (Operation.interp _ _ _ _ _ _ _) _ _
  simp only [Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp, MachineData.set,
    MachineData.setReg, Reg64s.set_low64, Reg64s.get_low64]
  exact h _ rfl rfl rfl rfl

@[spec high] theorem Operation.dec_r_acc (r : Reg64) :
    ⦃ ∀ s' : MachineData,
        s'.regs = s.regs.set64 r (s.regs.get64 r - 1) →
        s'.zmms = s.zmms → s'.dmem = s.dmem →
        wp (next s') post epost ⦄
      Operation.interp labels address_size (.dec (.reg (.low r .W64))) p s next jmp
      ⦃ post; epost ⦄ := by
  constructor
  intro h
  show wp (Operation.interp _ _ _ _ _ _ _) _ _
  simp only [Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp, MachineData.set,
    MachineData.setReg, Reg64s.set_low64, Reg64s.get_low64]
  exact h _ rfl rfl rfl

@[spec high] theorem Operation.add_ri_acc (r : Reg64) (i : Int64) :
    ⦃ ∀ s' : MachineData,
        s'.regs = s.regs.set64 r (BitVec.setWidth 64 i.toBitVec + s.regs.get64 r) →
        s'.zmms = s.zmms → s'.dmem = s.dmem →
        s'.status.cf = ((BitVec.setWidth 64 i.toBitVec + s.regs.get64 r).unsigned
          != (BitVec.setWidth 64 i.toBitVec).unsigned + (s.regs.get64 r).unsigned) →
        wp (next s') post epost ⦄
      Operation.interp labels address_size (.add (.reg (.low r .W64)) (.imm (.int64 i))) p s next jmp
      ⦃ post; epost ⦄ := by
  constructor
  intro h
  show wp (Operation.interp _ _ _ _ _ _ _) _ _
  simp only [Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp, ConstExpr.interp,
    MachineData.set, MachineData.setReg, Reg64s.set_low64, Reg64s.get_low64]
  exact h _ rfl rfl rfl rfl

@[spec high] theorem Operation.adc_rr_acc (rd rs : Reg64) :
    ⦃ ∀ s' : MachineData,
        s'.regs = s.regs.set64 rd
          (s.regs.get64 rs + s.regs.get64 rd + BitVec.ofNat 64 s.status.cf.toNat) →
        s'.zmms = s.zmms → s'.dmem = s.dmem →
        s'.status.cf = ((s.regs.get64 rs + s.regs.get64 rd + BitVec.ofNat 64 s.status.cf.toNat).unsigned
          != (s.regs.get64 rs).unsigned + (s.regs.get64 rd).unsigned + s.status.cf.toNat) →
        wp (next s') post epost ⦄
      Operation.interp labels address_size
        (.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))) p s next jmp
      ⦃ post; epost ⦄ := by
  constructor
  intro h
  show wp (Operation.interp _ _ _ _ _ _ _) _ _
  simp only [Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp, MachineData.set,
    MachineData.setReg, Reg64s.set_low64, Reg64s.get_low64]
  exact h _ rfl rfl rfl rfl

end

open Kraken.Parser in
def sp1a := parse("start: mov $2, %rax")

open Kraken.Parser in
example [layout : Layout] s :
    straightlineStep (layout sp1a) (s, layout.start) (fun s => s.1.regs.rax = 2) := by
  cases s with | mk regs zmms flags mem =>
  cases regs with | mk rax rbx rcx rdx rsi rdi rsp rbp r8 r9 r10 r11 r12 r13 r14 r15 =>
  delta sp1a
  dsimp only [straightlineStep, Executable.straightline]
  rw [Executable.directivesFromStart']
  simp [List.mapIdx, List.mapIdx.go]
  apply Effects.all_of_triple
  sym =>
    vcgen -internalize
    all_goals tactic => (simp_all; try decide)

open Kraken.Parser in
example [layout : Layout] s :
    straightlineStep (layout sp4) (s, layout.start) (fun s => s.1.regs.rax = 1) := by
  cases s with | mk regs zmms flags mem =>
  cases regs with | mk rax rbx rcx rdx rsi rdi rsp rbp r8 r9 r10 r11 r12 r13 r14 r15 =>
  delta sp4
  dsimp only [straightlineStep, Executable.straightline]
  rw [Executable.directivesFromStart']
  simp [List.mapIdx, List.mapIdx.go]
  apply Effects.all_of_triple
  sym =>
    vcgen -internalize
    all_goals tactic => (simp_all; try decide)
