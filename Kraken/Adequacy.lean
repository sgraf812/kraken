/-
Adequacy of the `X64MNew` encoding against the baseline omni-semantics.

The baseline is `Operation.interp`, the straightline interpreter over
`EStateM X64Exit MachineData`. A device-parameterized action `Op.foo` runs over
`Sys D`, touching only the `machine` component; `liftMachine` embeds a baseline
computation into that component, and `liftMachineP` reads `rip` first so the
baseline's position range is the current one. Each deterministic `Op.foo` equals
`liftMachineP` of the matching `Operation.interp` case at 64-bit operand and
address size, so every `@[spec]` triple transports to the baseline by rewriting
along these equalities.

The operand-shape enumeration is the encoding's own partial match: `Op.foo`
implements the `.low` register and `.int64` immediate shapes and faults on the
rest. The one place the cases would otherwise duplicate work is the effective
address, and `evalAddr_apply` states it once for every memory case to rewrite
through. Landing those cases also needs `liftMachine` pushed through the load and
store bind, so its monad-morphism laws are the next step.

The flag-nondeterministic family is out of scope: the encoding commits to a
result and to `cf/af/of := false` where `Operation.interp` throws
`undefinedFlags`.
-/
import Kraken.X64MNew

open Std.Internal.Do

set_option linter.unusedSimpArgs false

namespace Kraken

/-- Run a baseline `X64M` computation on the `machine` component of a `Sys D`
state, threading the device state. -/
def liftMachine {D : Type} {α : Type} (c : X64M α) : X64MNew D α :=
  liftM (m := SysM D) (fun s =>
    match c s.machine with
    | .ok a m => .ok a { s with machine := m }
    | .error e m => .error e { s with machine := m })

/-- Read `rip` and run a baseline computation whose position range is that `rip`,
so an address or a jump target resolves against the current instruction. -/
def liftMachineP {D : Type} {α : Type} (c : Int64 → X64M α) : X64MNew D α := do
  let rip ← getThe Int64
  liftMachine (c rip)

/-- The effective address `evalAddr` computes, read off in one step: the baseline
`AddrExpr.interp` at 64-bit address size and the current position range, with the
state left untouched. Every memory-operand adequacy case rewrites its address
through this, so none re-derive the reader/state plumbing. -/
theorem evalAddr_apply {D : Type} (ae : AddrExpr) (env : Env) (rip : Int64) (s : Sys D) :
    (evalAddr ae : X64MNew D (BitVec 64)) env rip s
      = .ok (AddrExpr.interp env.labels (.mk .W64) ae s.machine.regs (.mk rip rip), rip) s := by
  simp only [evalAddr, getRco, getMachine, bind, pure, get, getThe, read, readThe,
    MonadReaderOf.read, ReaderT.read, ReaderT.bind, ReaderT.pure, StateT.bind, StateT.pure,
    StateT.get, StateT.lift, MonadStateOf.get, EStateM.get, EStateM.bind, EStateM.pure,
    liftM, monadLift, MonadLift.monadLift]

/-- Run both the encoding and the lifted baseline on a state and normalize the
resulting `Sys D` literal, resolving any effective address through
`evalAddr_apply`. -/
local macro "adequacy_reduce" op:ident : tactic =>
  `(tactic| (funext env rip s
             simp only [$op:ident, liftMachine, liftMachineP, modifyMachine, getMachine, getRco,
               evalAddr_apply, Operation.interp, Operand.interp, ConstExpr.interp, RegOrMem.interp,
               Reg.interp, MachineData.set, MachineData.setReg, MachineData.load, Reg64s.get_low64,
               Reg64s.set_low64, bind, pure, get, getThe, read, readThe, MonadReaderOf.read,
               ReaderT.read, ReaderT.bind, ReaderT.pure, StateT.bind, StateT.pure, StateT.get,
               StateT.lift, MonadStateOf.get, EStateM.get, MonadStateOf.modifyGet, EStateM.modifyGet,
               modify, modifyGet, EStateM.bind, EStateM.pure, liftM, monadLift, MonadLift.monadLift,
               Bv.ofBitVec_toBitVec, BitVec.setWidth_eq]))

variable (labels : Labels)

/-! ## Register moves -/

theorem Op.mov_reg_imm_adequate {D : Type} (r : Reg64) (i : Int64) :
    (Op.mov (.reg (.low r .W64)) (.imm (.int64 i)) : X64MNew D Unit)
      = liftMachineP (fun rip => Operation.interp labels (.mk .W64)
          (.mov (.reg (.low r .W64)) (.imm (.int64 i))) (.mk rip rip)) := by
  funext env rip s
  simp only [Op.mov, liftMachine, liftMachineP, modifyMachine, Operation.interp, Operand.interp,
    ConstExpr.interp, MachineData.set, MachineData.setReg, Reg64s.set_low64, bind, pure, getThe, get,
    ReaderT.bind, ReaderT.pure, StateT.bind, StateT.pure, StateT.get, StateT.lift, MonadStateOf.get,
    EStateM.get, MonadStateOf.modifyGet, EStateM.modifyGet, modify, modifyGet, EStateM.bind,
    EStateM.pure, liftM, monadLift, MonadLift.monadLift, Bv.ofBitVec_toBitVec, BitVec.setWidth_eq]

theorem Op.mov_reg_reg_adequate {D : Type} (rd rs : Reg64) :
    (Op.mov (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))) : X64MNew D Unit)
      = liftMachineP (fun rip => Operation.interp labels (.mk .W64)
          (.mov (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))) (.mk rip rip)) := by
  adequacy_reduce Op.mov

/-! ## Arithmetic -/

theorem Op.dec_reg_adequate {D : Type} (r : Reg64) :
    (Op.dec (.reg (.low r .W64)) : X64MNew D Unit)
      = liftMachineP (fun rip => Operation.interp labels (.mk .W64) (.dec (.reg (.low r .W64))) (.mk rip rip)) := by
  adequacy_reduce Op.dec

theorem Op.add_reg_imm_adequate {D : Type} (r : Reg64) (i : Int64) :
    (Op.add (.reg (.low r .W64)) (.imm (.int64 i)) : X64MNew D Unit)
      = liftMachineP (fun rip => Operation.interp labels (.mk .W64)
          (.add (.reg (.low r .W64)) (.imm (.int64 i))) (.mk rip rip)) := by
  adequacy_reduce Op.add

theorem Op.adc_reg_reg_adequate {D : Type} (rd rs : Reg64) :
    (Op.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))) : X64MNew D Unit)
      = liftMachineP (fun rip => Operation.interp labels (.mk .W64)
          (.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))) (.mk rip rip)) := by
  adequacy_reduce Op.adc

end Kraken
