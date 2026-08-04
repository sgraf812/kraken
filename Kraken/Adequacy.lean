/-
Adequacy of the per-instruction encoding against the baseline omni-semantics.

Each `Op.foo` action equals the matching case of `Operation.interp` at 64-bit
operand and address size: the encoding the `@[spec]` triples are stated over is
the omni-semantics on the deterministic-result instructions, so every triple
transports to `Operation.interp` by rewriting along these equalities.

`Op.xorRR` is deliberately out of scope: `Operation.interp` throws
`undefinedFlags` for `xor` and the rest of the flag-nondeterministic family,
whereas `Op.xorRR` commits to a result and to `cf/af/of := false`. The encoding
is a deliberate extension there, not the omni-semantics.
-/
import Kraken.Specs

open Std.Internal.Do
open Kraken

set_option mvcgen.warning false
set_option grind.warning false
set_option linter.unusedSimpArgs false

namespace Kraken

variable (labels : Labels) (p : Std.Rco Int64)

/-! ## Register instructions -/

theorem Op.movRI_adequate (r : Reg64) (i : Int64) :
    Op.movRI r i
      = Operation.interp labels (.mk .W64) (.mov (.reg (.low r .W64)) (.imm (.int64 i))) p := by
  funext s
  simp [Op.movRI, Operation.interp, Operand.interp, MachineData.set, ConstExpr.interp,
    bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet]

theorem Op.movRR_adequate (rd rs : Reg64) :
    Op.movRR rd rs
      = Operation.interp labels (.mk .W64)
          (.mov (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))) p := by
  funext s
  simp [Op.movRR, Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp, MachineData.set,
    Reg64s.get_low64, bind, EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get,
    EStateM.get, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, MachineData.setReg]

theorem Op.decR_adequate (r : Reg64) :
    Op.decR r
      = Operation.interp labels (.mk .W64) (.dec (.reg (.low r .W64))) p := by
  funext s
  simp [Op.decR, Operation.interp, RegOrMem.interp, Reg.interp, MachineData.set,
    Reg64s.get_low64, bind, EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get,
    EStateM.get, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, set, EStateM.set,
    MachineData.setReg]

theorem Op.addRI_adequate (r : Reg64) (i : Int64) :
    Op.addRI r i
      = Operation.interp labels (.mk .W64) (.add (.reg (.low r .W64)) (.imm (.int64 i))) p := by
  funext s
  simp [Op.addRI, Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp, MachineData.set,
    ConstExpr.interp, Reg64s.get_low64, bind, EStateM.bind, pure, EStateM.pure, get, getThe,
    MonadStateOf.get, EStateM.get, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    set, EStateM.set, MachineData.setReg]

theorem Op.adcRR_adequate (rd rs : Reg64) :
    Op.adcRR rd rs
      = Operation.interp labels (.mk .W64)
          (.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))) p := by
  funext s
  simp [Op.adcRR, Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp, MachineData.set,
    Reg64s.get_low64, bind, EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get,
    EStateM.get, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, set, EStateM.set,
    MachineData.setReg]

/-! ## Conditional jump

`Op.jnz l` jumps exactly when `ZF` is clear, which is `CondCode.nz`; it holds once
the label resolves to the concrete target. -/

theorem Op.jnz_adequate (l : Int64) (lbl : Label) (hlbl : labels.label lbl = l) :
    Op.jnz l
      = Operation.interp labels (.mk .W64) (.jcc .nz lbl : Operation .W64) p := by
  funext s
  simp only [Op.jnz, Operation.interp, CondCode.interp, hlbl, bind, EStateM.bind, get, getThe,
    MonadStateOf.get, EStateM.get, Bool.not_eq_true']
  split <;> simp_all [throw, EStateM.throw, MonadExceptOf.throw, pure, EStateM.pure]

/-! ## Memory addressing bridge

`Addr` is the base+scaled-index+displacement fragment of `AddrExpr`: no `rip`
base and no label displacement. At 64-bit addressing `Addr.eval` is exactly
`AddrExpr.interp` on the embedding, provided the index scale is a width's byte
count (`AddrExpr` scales by a `Width`, `Addr` by an `Int64`). -/

/-- Embed an `Addr` as an `AddrExpr`, reading the index scale off a width. -/
def Addr.toAddrExpr (a : Addr) (idxW : Width) : AddrExpr where
  base := some (.reg a.base)
  idx := a.index.map (fun ri => ⟨ri.1, idxW⟩)
  disp := .int64 a.disp

theorem Addr.interp_toAddrExpr (a : Addr) (idxW : Width) (regs : Reg64s)
    (hidx : ∀ r sc, a.index = some (r, sc) → sc.toInt = (idxW.bytes : Int)) :
    AddrExpr.interp labels (.mk .W64) (a.toAddrExpr idxW) regs p = a.eval regs := by
  simp only [Addr.eval, AddrExpr.interp, Addr.toAddrExpr, BitVec.toAddressSize, BitVec.take,
    BitVec.extractLsb'_eq_self, BitVec.signed, ConstExpr.interp]
  cases hai : a.index with
  | none => simp [hai]
  | some ri =>
    obtain ⟨r, sc⟩ := ri
    simp [hai, hidx r sc hai]

/-! ## Memory instructions -/

theorem Op.movRM_adequate (dst : Reg64) (a : Addr) (idxW : Width)
    (hidx : ∀ r sc, a.index = some (r, sc) → sc.toInt = (idxW.bytes : Int)) :
    Op.movRM dst a
      = Operation.interp labels (.mk .W64)
          (.mov (.reg (.low dst .W64)) (.regOrMem (.mem (a.toAddrExpr idxW)))) p := by
  funext s
  simp only [Op.movRM, Op.loadIntM, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.load, MachineData.set, Addr.interp_toAddrExpr labels p a idxW s.regs hidx,
    Width.bytes, Width.bits, BitVec.setWidth_eq, bind, EStateM.bind, pure, EStateM.pure, get,
    getThe, MonadStateOf.get, EStateM.get, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet, MachineData.setReg]
  cases Mem.loadInt s.dmem (a.eval s.regs) 8 <;> rfl

theorem Op.movMI_adequate (a : Addr) (i : Int64) (idxW : Width)
    (hidx : ∀ r sc, a.index = some (r, sc) → sc.toInt = (idxW.bytes : Int)) :
    Op.movMI a i
      = Operation.interp labels (.mk .W64)
          (.mov (.mem (a.toAddrExpr idxW)) (.imm (.int64 i)) : Operation .W64) p := by
  funext s
  simp only [Op.movMI, Op.checkMapped, Operation.interp, Operand.interp, MachineData.set,
    MachineData.store, ConstExpr.interp, Addr.interp_toAddrExpr labels p a idxW s.regs hidx,
    Width.bytes, Width.bits, BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_eq, bind, EStateM.bind,
    pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, set, EStateM.set, modify,
    modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, throw, throwThe, EStateM.throw,
    MonadExceptOf.throw]
  cases Mem.loadInt s.dmem (a.eval s.regs) 8 <;> rfl

theorem Op.movMR_adequate (a : Addr) (src : Reg64) (idxW : Width)
    (hidx : ∀ r sc, a.index = some (r, sc) → sc.toInt = (idxW.bytes : Int)) :
    Op.movMR a src
      = Operation.interp labels (.mk .W64)
          (.mov (.mem (a.toAddrExpr idxW)) (.regOrMem (.reg (.low src .W64)))) p := by
  funext s
  simp only [Op.movMR, Op.checkMapped, Operation.interp, Operand.interp, RegOrMem.interp,
    Reg.interp, MachineData.set, MachineData.store, Reg64s.get_low64,
    Addr.interp_toAddrExpr labels p a idxW s.regs hidx, Width.bytes, Width.bits,
    BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_eq, bind, EStateM.bind, pure, EStateM.pure, get,
    getThe, MonadStateOf.get, EStateM.get, set, EStateM.set, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, throw, throwThe, EStateM.throw, MonadExceptOf.throw]
  cases Mem.loadInt s.dmem (a.eval s.regs) 8 <;> rfl

theorem Op.addRM_adequate (dst : Reg64) (a : Addr) (idxW : Width)
    (hidx : ∀ r sc, a.index = some (r, sc) → sc.toInt = (idxW.bytes : Int)) :
    Op.addRM dst a
      = Operation.interp labels (.mk .W64)
          (.add (.reg (.low dst .W64)) (.regOrMem (.mem (a.toAddrExpr idxW)))) p := by
  funext s
  simp only [Op.addRM, Op.loadIntM, Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp,
    MachineData.load, MachineData.set, Reg64s.get_low64,
    Addr.interp_toAddrExpr labels p a idxW s.regs hidx, Width.bytes, Width.bits, BitVec.setWidth_eq,
    bind, EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, set,
    EStateM.set, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, MachineData.setReg]
  cases Mem.loadInt s.dmem (a.eval s.regs) 8 <;> rfl

/-! ## Stack instructions

`Op.pushR`/`Op.popR` are `.push`/`.pop` of a 64-bit register; the rsp-relative
address is computed inline rather than through an `Addr`.

`Op.pushR` decrements `rsp` only after confirming the new top of stack is mapped,
whereas `Operation.interp (.push …)` decrements `rsp` and then stores, so on an
unmapped push the two exit with different `rsp`. The equality is stated on the
mapped state, where they agree; the omni-semantics sends every non-jump exit to
`False`, so nothing is lost on the fault path. `Op.popR` loads before touching
`rsp`, so it agrees unconditionally. -/

theorem Op.pushR_adequate (r : Reg64) (s : MachineData) (v : Int)
    (hmap : Mem.loadInt s.dmem ((s.regs.get64 .rsp).toBitVec - 8#64) 8 = some v) :
    Op.pushR r s
      = Operation.interp labels (.mk .W64) (.push (.regOrMem (.reg (.low r .W64)))) p s := by
  simp only [Op.pushR, Op.checkMapped, Operation.interp, Operand.interp, RegOrMem.interp,
    Reg.interp, MachineData.store, Reg64s.get_low64, Width.bytes, Width.bytesv, hmap, bind,
    EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, set, EStateM.set,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

theorem Op.popR_adequate (dst : Reg64) :
    Op.popR dst
      = Operation.interp labels (.mk .W64) (.pop (.reg (.low dst .W64))) p := by
  funext s
  simp only [Op.popR, Op.loadIntM, Operation.interp, MachineData.load, MachineData.set,
    Reg64s.get_low64, Width.bytes, Width.bytesv, bind, EStateM.bind, pure, EStateM.pure, get,
    getThe, MonadStateOf.get, EStateM.get, set, EStateM.set, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, MachineData.setReg]
  cases Mem.loadInt s.dmem (s.regs.get64 .rsp).toBitVec 8 <;> rfl

/-! ## Transport

Each `@[spec]` triple over `Op.foo` transports to the matching `Operation.interp`
node by rewriting along the adequacy equality. `movRI` shown; every other spec
transports the same way. -/

theorem Operation.interp_movRI_spec (Q : Unit → MachineData → Prop)
    (E : X64Exit → MachineData → Prop) (r : Reg64) (i : Int64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 r (.ofBitVec (BitVec.setWidth 64 i.toBitVec)) } ⦄
      Operation.interp labels (.mk .W64) (.mov (.reg (.low r .W64)) (.imm (.int64 i))) p
      ⦃ Q; E ⦄ := by
  rw [← Op.movRI_adequate]; exact Op.movRI_spec Q E r i

end Kraken
