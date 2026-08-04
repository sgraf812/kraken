/-
Adequacy of the `X64MNew` encoding against the baseline omni-semantics.

The baseline is `Operation.interp`, the straightline interpreter over
`EStateM X64Exit MachineData`. A device-parameterized action `Op.foo` runs over
`Sys D`, touching only the `machine` component; `liftMachine` embeds a baseline
computation into that component, threading the device state and `rip`. Each
deterministic `Op.foo` equals `liftMachine` of the matching `Operation.interp`
case at 64-bit operand and address size, so every `@[spec]` triple transports to
the baseline by rewriting along these equalities.

The flag-nondeterministic family is out of scope: the encoding commits to a
result and to `cf/af/of := false` where `Operation.interp` throws
`undefinedFlags`.
-/
import Kraken.X64MNew

open Std.Internal.Do

set_option linter.unusedSimpArgs false

namespace Kraken

/-- Run a baseline `X64M` computation on the `machine` component of a `Sys D`
state, threading the device state and `rip`. -/
def liftMachine {D : Type} {α : Type} (c : X64M α) : X64MNew D α :=
  liftM (m := SysM D) (fun s =>
    match c s.machine with
    | .ok a m => .ok a { s with machine := m }
    | .error e m => .error e { s with machine := m })

/-- Reduce a register-action adequacy goal: run both the encoding and the lifted
baseline on a state and normalize the resulting `Sys D` literal. The baseline
threads the operand reads through `get`; the encoding folds them into one
`modify`, so the two meet after the monad and the register round-trip reduce. -/
local macro "adequacy_reduce" op:ident : tactic =>
  `(tactic| (funext env rip s
             simp only [$op:ident, liftMachine, modifyMachine,
               Operation.interp, Operand.interp, ConstExpr.interp, RegOrMem.interp, Reg.interp,
               MachineData.set, MachineData.setReg, Reg64s.get_low64, Reg64s.set_low64,
               bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get,
               EStateM.get, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
               liftM, monadLift, MonadLift.monadLift, StateT.lift, Bv.ofBitVec_toBitVec]))

variable (labels : Labels)

/-- `mov r, imm`: a register-immediate move equals the baseline `mov` case. The
address size and `p` are inert here, so any values serve. -/
theorem Op.mov_reg_imm_adequate {D : Type} (r : Reg64) (i : Int64) :
    (Op.mov (.reg (.low r .W64)) (.imm (.int64 i)) : X64MNew D Unit)
      = liftMachine (Operation.interp labels (.mk .W64)
          (.mov (.reg (.low r .W64)) (.imm (.int64 i))) (.mk 0 0)) := by
  funext env rip s; rfl

/-- `mov rd, rs`: a register-register move. -/
theorem Op.mov_reg_reg_adequate {D : Type} (rd rs : Reg64) :
    (Op.mov (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))) : X64MNew D Unit)
      = liftMachine (Operation.interp labels (.mk .W64)
          (.mov (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))) (.mk 0 0)) := by
  adequacy_reduce Op.mov

/-- `dec r`: decrement, carry preserved. -/
theorem Op.dec_reg_adequate {D : Type} (r : Reg64) :
    (Op.dec (.reg (.low r .W64)) : X64MNew D Unit)
      = liftMachine (Operation.interp labels (.mk .W64) (.dec (.reg (.low r .W64))) (.mk 0 0)) := by
  adequacy_reduce Op.dec

/-- `add r, imm`: register-immediate add with the `add` flag effects. -/
theorem Op.add_reg_imm_adequate {D : Type} (r : Reg64) (i : Int64) :
    (Op.add (.reg (.low r .W64)) (.imm (.int64 i)) : X64MNew D Unit)
      = liftMachine (Operation.interp labels (.mk .W64)
          (.add (.reg (.low r .W64)) (.imm (.int64 i))) (.mk 0 0)) := by
  adequacy_reduce Op.add

/-- `adc rd, rs`: register-register add-with-carry. -/
theorem Op.adc_reg_reg_adequate {D : Type} (rd rs : Reg64) :
    (Op.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))) : X64MNew D Unit)
      = liftMachine (Operation.interp labels (.mk .W64)
          (.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))) (.mk 0 0)) := by
  adequacy_reduce Op.adc

end Kraken
