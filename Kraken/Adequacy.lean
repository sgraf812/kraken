/-
Adequacy of the `X64MNew` encoding against the baseline omni-semantics.

The baseline is `Operation.interp`, the straightline interpreter over
`EStateM X64Exit MachineData`. A device-parameterized action `Op.foo` runs over
`Sys D`, touching only the `machine` component; `liftMachine` embeds a baseline
computation into that component, `liftMachineP` reads `rip` first, and
`liftBaseline` reads the label environment. Each deterministic `Op.foo` equals
`liftBaseline` of the matching `Operation.interp` case at 64-bit operand and
address size.

The proofs run against a characterizing API rather than by unfolding at the use
site: a `liftMachine` monad-morphism dictionary (`lm_*`) pushes the lift to the
X64MNew primitives, the memory bridges (`lm_load_bind`/`lm_store`) turn a lifted
access into the `match` shape the encoding uses, and the state-operation fusion
and discard laws (`gm_*`, `read_bind_const`, …) normalize both sides to one form.
Every case closes with the same `simp` set.

The flag-nondeterministic family is out of scope: the encoding commits to a
result and to `cf/af/of := false` where `Operation.interp` throws
`undefinedFlags`.
-/
import Kraken.X64MNew

open Std.Internal.Do

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Kraken

/-- Run a baseline `X64M` computation on the `machine` component of a `Sys D`
state, threading the device state. -/
def liftMachine {D : Type} {α : Type} (c : X64M α) : X64MNew D α :=
  liftM (m := SysM D) (fun s =>
    match c s.machine with
    | .ok a m => .ok a { s with machine := m }
    | .error e m => .error e { s with machine := m })

/-- Read `rip` and run a baseline computation whose position range is that `rip`. -/
def liftMachineP {D : Type} {α : Type} (c : Int64 → X64M α) : X64MNew D α := do
  let rip ← getThe Int64
  liftMachine (c rip)

/-- Read the label environment and run the baseline `Operation.interp` of `op` at
64-bit address size against the current `rip`. -/
def liftBaseline {D : Type} (op : Operation .W64) : X64MNew D Unit := do
  let env ← read
  liftMachineP (fun rip => Operation.interp env.labels (.mk .W64) op (.mk rip rip))

/-! ## `liftMachine` monad-morphism dictionary -/

@[simp] theorem lm_pure {D α} (a : α) : (liftMachine (pure a) : X64MNew D α) = pure a := by
  funext env rip s; rfl
@[simp] theorem lm_bind {D α β} (x : X64M α) (f : α → X64M β) :
    (liftMachine (x >>= f) : X64MNew D β) = liftMachine x >>= fun a => liftMachine (f a) := by
  funext env rip s
  simp only [liftMachine, bind, liftM, monadLift, MonadLift.monadLift, ReaderT.bind, StateT.bind,
    StateT.lift, EStateM.bind, ReaderT.pure, StateT.pure, EStateM.pure]
  cases x s.machine <;> rfl
@[simp] theorem lm_ebind {D α β} (x : X64M α) (f : α → X64M β) :
    (liftMachine (EStateM.bind x f) : X64MNew D β) = liftMachine x >>= fun a => liftMachine (f a) :=
  lm_bind x f
@[simp] theorem lm_get {D} : (liftMachine (get : X64M MachineData) : X64MNew D MachineData) = getMachine := by
  funext env rip s; rfl
@[simp] theorem lm_eget {D} : (liftMachine EStateM.get : X64MNew D MachineData) = getMachine := by
  funext env rip s; rfl
@[simp] theorem lm_modify {D} (f : MachineData → MachineData) :
    (liftMachine (modify f) : X64MNew D Unit) = modifyMachine f := by
  funext env rip s; rfl
@[simp] theorem lm_set {D} (m : MachineData) :
    (liftMachine (set m : X64M Unit) : X64MNew D Unit) = modifyMachine (fun _ => m) := by
  funext env rip s; rfl
@[simp] theorem lm_throw {D α} (e : X64Exit) :
    (liftMachine (throw e) : X64MNew D α) = liftM (throw e : SysM D α) := by
  funext env rip s; rfl
@[simp] theorem lm_throw_bind {D α β} (e : X64Exit) (f : α → X64MNew D β) :
    ((liftM (throw e : SysM D α) : X64MNew D α) >>= f) = liftM (throw e : SysM D β) := by
  funext env rip s; rfl

/-- A lifted 8-byte load fused with its continuation: the mapped value feeds `k`,
an unmapped address faults, matching the encoding's inlined access. -/
@[simp] theorem lm_load_bind {D α} (addr : BitVec 64) (k : BitVec 64 → X64MNew D α) :
    ((liftMachine (MachineData.load addr .W64) : X64MNew D (BitVec 64)) >>= k)
      = getMachine >>= fun s => (match Mem.loadInt s.dmem addr 8 with
          | some i => k (BitVec.ofInt 64 i)
          | none => liftM (throw (.nonmemLoad s.dmem addr .W64) : SysM D α)) := by
  funext env rip s
  simp only [MachineData.load, liftMachine, getMachine, bind, pure, get, getThe, liftM, monadLift,
    MonadLift.monadLift, ReaderT.bind, ReaderT.pure, StateT.bind, StateT.pure, StateT.get,
    StateT.lift, MonadStateOf.get, EStateM.get, EStateM.bind, EStateM.pure, EStateM.throw, throw,
    throwThe, MonadExceptOf.throw, Width.bytes]
  cases Mem.loadInt s.machine.dmem addr 8 <;> rfl

/-- A lifted 8-byte store: a mapped address commits the write, an unmapped
address faults. The store is the last action of a memory-write instruction, so no
fused continuation is needed. -/
@[simp] theorem lm_store {D} (addr : BitVec 64) (v : BitVec 64) :
    (liftMachine (MachineData.store addr (w := .W64) v) : X64MNew D Unit)
      = getMachine >>= fun s => (match Mem.loadInt s.dmem addr 8 with
          | some _ => modifyMachine (fun m => { m with dmem := Mem.storeInt m.dmem addr 8 v.toInt })
          | none => liftM (throw (.nonmemStore s.dmem addr .W64) : SysM D Unit)) := by
  funext env rip s
  simp only [MachineData.store, liftMachine, getMachine, modifyMachine, bind, pure, get, set, getThe,
    liftM, monadLift, MonadLift.monadLift, ReaderT.bind, ReaderT.pure, StateT.bind, StateT.pure,
    StateT.get, StateT.lift, MonadStateOf.get, EStateM.get, MonadStateOf.set, EStateM.set,
    EStateM.bind, EStateM.pure, EStateM.throw, throw, throwThe, MonadExceptOf.throw, Width.bytes]
  cases Mem.loadInt s.machine.dmem addr 8 <;> rfl

/-! ## State-operation fusion and discard laws -/

@[simp] theorem gm_gm {D α} (f : MachineData → MachineData → X64MNew D α) :
    (getMachine >>= fun s => getMachine >>= fun s' => f s s' : X64MNew D α)
      = getMachine >>= fun s => f s s := by funext env rip s; rfl
@[simp] theorem gm_mm {D} (g : MachineData → MachineData → MachineData) :
    (getMachine >>= fun s => modifyMachine (g s) : X64MNew D Unit) = modifyMachine (fun m => g m m) := by
  funext env rip s; rfl
@[simp] theorem gm_mset {D} (g : MachineData → MachineData) :
    (getMachine >>= fun s => modifyMachine (fun _ => g s) : X64MNew D Unit) = modifyMachine g := by
  funext env rip s; rfl
@[simp] theorem gm_gt {D α} (k : MachineData → Int64 → X64MNew D α) :
    (getMachine >>= fun s => getThe Int64 >>= fun p => k s p : X64MNew D α)
      = getThe Int64 >>= fun p => getMachine >>= fun s => k s p := by funext env rip s; rfl
@[simp] theorem read_bind_const {D α} (k : X64MNew D α) :
    ((read : X64MNew D Env) >>= fun _ => k) = k := by funext env rip s; rfl
@[simp] theorem getThe_bind_const {D α} (k : X64MNew D α) :
    ((getThe Int64 : X64MNew D Int64) >>= fun _ => k) = k := by funext env rip s; rfl
@[simp] theorem read_read {D α} (k : Env → Env → X64MNew D α) :
    ((read : X64MNew D Env) >>= fun e => read >>= fun e' => k e e') = read >>= fun e => k e e := by
  funext env rip s; rfl
@[simp] theorem gt_gt {D α} (k : Int64 → Int64 → X64MNew D α) :
    ((getThe Int64 : X64MNew D Int64) >>= fun p => getThe Int64 >>= fun p' => k p p')
      = getThe Int64 >>= fun p => k p p := by funext env rip s; rfl
@[simp] theorem ze64 (x : BitVec 64) : BitVec.zeroExtend 64 x = x := BitVec.setWidth_64_64 x

/-- The value a store commits is read at store time; reading it from the earlier
`getMachine` is the same, since nothing between modifies the state. This fuses the
baseline's early operand read into the encoding's store. -/
@[simp] theorem gm_store_fuse {D} (addr : BitVec 64) (val : MachineData → Int) :
    (getMachine >>= fun s => (match Mem.loadInt s.dmem addr 8 with
       | some _ => modifyMachine (fun m => { m with dmem := Mem.storeInt m.dmem addr 8 (val s) })
       | none => liftM (throw (.nonmemStore s.dmem addr .W64) : SysM D Unit)) : X64MNew D Unit)
      = getMachine >>= fun s => (match Mem.loadInt s.dmem addr 8 with
       | some _ => modifyMachine (fun m => { m with dmem := Mem.storeInt m.dmem addr 8 (val m) })
       | none => liftM (throw (.nonmemStore s.dmem addr .W64) : SysM D Unit)) := by
  funext env rip s; cases Mem.loadInt s.machine.dmem addr 8 <;> rfl

/-- One reduction for every case: unfold the encoding and the baseline, push the
lift to leaves through the dictionary, fuse the state operations, and settle the
two matchers by definitional equality. -/
local macro "adeq" : tactic =>
  `(tactic| (simp only [Op.mov, Op.dec, Op.add, Op.adc, Op.lea, liftBaseline, liftMachineP,
      Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp, ConstExpr.interp,
      MachineData.set, evalAddr, getRco, lm_pure, lm_bind, lm_ebind, lm_get, lm_eget, lm_modify,
      lm_set, lm_throw, lm_throw_bind, lm_load_bind, lm_store, gm_gm, gm_mm, gm_mset, gm_gt,
      read_bind_const, getThe_bind_const, read_read, gt_gt, bind_assoc, pure_bind, bind_pure,
      MachineData.setReg, Reg64s.get_low64, Reg64s.set_low64, Bv.ofBitVec_toBitVec, Width.bytes,
      BitVec.ofInt_toInt, ze64, gm_store_fuse, BitVec.setWidth_64_64]; try rfl))

variable (labels : Labels)

/-! ## Register moves -/

theorem Op.mov_reg_imm_adequate {D} (r : Reg64) (i : Int64) :
    (Op.mov (.reg (.low r .W64)) (.imm (.int64 i)) : X64MNew D Unit)
      = liftBaseline (.mov (.reg (.low r .W64)) (.imm (.int64 i))) := by adeq

theorem Op.mov_reg_reg_adequate {D} (rd rs : Reg64) :
    (Op.mov (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))) : X64MNew D Unit)
      = liftBaseline (.mov (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))) := by adeq

theorem Op.mov_reg_mem_adequate {D} (rd : Reg64) (ae : AddrExpr) :
    (Op.mov (.reg (.low rd .W64)) (.regOrMem (.mem ae)) : X64MNew D Unit)
      = liftBaseline (.mov (.reg (.low rd .W64)) (.regOrMem (.mem ae))) := by adeq

theorem Op.mov_mem_imm_adequate {D} (ae : AddrExpr) (i : Int64) :
    (Op.mov (.mem ae) (.imm (.int64 i)) : X64MNew D Unit)
      = liftBaseline (.mov (.mem ae) (.imm (.int64 i))) := by adeq

theorem Op.mov_mem_reg_adequate {D} (ae : AddrExpr) (rs : Reg64) :
    (Op.mov (.mem ae) (.regOrMem (.reg (.low rs .W64))) : X64MNew D Unit)
      = liftBaseline (.mov (.mem ae) (.regOrMem (.reg (.low rs .W64)))) := by adeq

/-! ## Arithmetic -/

theorem Op.dec_reg_adequate {D} (r : Reg64) :
    (Op.dec (.reg (.low r .W64)) : X64MNew D Unit)
      = liftBaseline (.dec (.reg (.low r .W64))) := by adeq

theorem Op.add_reg_imm_adequate {D} (r : Reg64) (i : Int64) :
    (Op.add (.reg (.low r .W64)) (.imm (.int64 i)) : X64MNew D Unit)
      = liftBaseline (.add (.reg (.low r .W64)) (.imm (.int64 i))) := by adeq

theorem Op.add_reg_mem_adequate {D} (rd : Reg64) (ae : AddrExpr) :
    (Op.add (.reg (.low rd .W64)) (.regOrMem (.mem ae)) : X64MNew D Unit)
      = liftBaseline (.add (.reg (.low rd .W64)) (.regOrMem (.mem ae))) := by adeq

theorem Op.adc_reg_reg_adequate {D} (rd rs : Reg64) :
    (Op.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))) : X64MNew D Unit)
      = liftBaseline (.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))) := by adeq

theorem Op.lea_adequate {D} (rd : Reg64) (ae : AddrExpr) :
    (Op.lea rd ae : X64MNew D Unit)
      = liftBaseline (.lea (.low rd .W64) ae) := by adeq

end Kraken
