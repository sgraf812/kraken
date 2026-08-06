/-
Adequacy of the `X64MNew` encoding against the baseline omni-semantics.

The baseline is `Operation.interp`, the straightline interpreter over
`EStateM X64Exit MachineData`. A device-parameterized action `Op.foo` runs over
`Sys D`, touching only the `machine` component; `liftMachine` embeds a baseline
computation into that component, and `liftBaseline` reads the label environment
and `rip`. Each deterministic `Op.foo` equals `liftBaseline` of the matching
`Operation.interp` case at 64-bit operand and address size.

The proofs run against a characterizing API rather than by unfolding at the use
site: a `liftMachine` monad-morphism dictionary (`lm_*`) pushes the lift to the
X64MNew primitives, the memory bridges (`lm_load_bind`/`lm_store`) turn a lifted
access into the `match` shape the encoding uses, and the state-operation fusion
and discard laws (`gm_*`, `read_bind_const`, …) normalize both sides to one form.
The residual is closed by applying a state and reducing each primitive in one
step (`gm_apply`/`mm_apply`/…), so no whnf of the transformer stack ever runs.

The flag-nondeterministic family (`xor`, and the shifts and rotates once encoded)
throws `undefinedFlags` in both the baseline and the encoding, since x86 leaves a
flag such as `AF` undefined; adequacy is faithfulness to the baseline, so the
encoding declines to commit a value there too.
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

/-- Read the label environment and `rip`, then run the baseline `Operation.interp`
of `op` at 64-bit address size over the position range `.mk rip (rip + curSize)`. -/
def liftBaseline {D : Type} (op : Operation .W64) : X64MNew D Unit := do
  let env ← read
  let rip ← getThe Int64
  liftMachine (Operation.interp env.labels (.mk .W64) op (.mk rip (rip + Int64.ofNat env.curSize)))

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
@[simp] theorem mm_mm {D} (g h : MachineData → MachineData) :
    (modifyMachine g >>= fun _ => modifyMachine h : X64MNew D Unit) = modifyMachine (fun m => h (g m)) := by
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

/-! Single-step reductions of a primitive applied to a state. Each is a one-step
`rfl`, so using them keeps a goal that reaches an applied form propositional
instead of forcing a full whnf of the transformer stack. -/
theorem read_apply {D α} (k : Env → X64MNew D α) (env : Env) (rip : Int64) (s : Sys D) :
    ((read : X64MNew D Env) >>= k) env rip s = k env env rip s := rfl
theorem getThe_apply {D α} (k : Int64 → X64MNew D α) (env : Env) (rip : Int64) (s : Sys D) :
    ((getThe Int64 : X64MNew D Int64) >>= k) env rip s = k rip env rip s := rfl
theorem gm_apply {D α} (k : MachineData → X64MNew D α) (env : Env) (rip : Int64) (s : Sys D) :
    (getMachine >>= k) env rip s = k s.machine env rip s := rfl
theorem mm_apply {D} (f : MachineData → MachineData) (env : Env) (rip : Int64) (s : Sys D) :
    modifyMachine f env rip s = .ok ((), rip) { s with machine := f s.machine } := rfl
theorem throw_apply {D α} (e : X64Exit) (env : Env) (rip : Int64) (s : Sys D) :
    (liftM (throw e : SysM D α) : X64MNew D α) env rip s = .error e s := rfl
theorem pure_apply {D α} (a : α) (env : Env) (rip : Int64) (s : Sys D) :
    (pure a : X64MNew D α) env rip s = .ok (a, rip) s := rfl
theorem withReader_apply {D α} (f : Env → Env) (x : X64MNew D α) (env : Env) (rip : Int64) (s : Sys D) :
    (withReader f x : X64MNew D α) env rip s = x (f env) rip s := rfl

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
  funext env rip s
  simp only [gm_apply]
  cases Mem.loadInt s.machine.dmem addr 8 <;> simp only [mm_apply, throw_apply]

/-- Bind distributes over a `Mem.loadInt` dispatch: the continuation moves into
each branch, and the fault branch absorbs it. -/
@[simp] theorem match_bind {D γ α β} (o : Option γ) (some_br : γ → X64MNew D α)
    (e : X64Exit) (k : α → X64MNew D β) :
    ((match o with | some i => some_br i | none => liftM (throw e : SysM D α)) >>= k)
      = (match o with | some i => some_br i >>= k | none => liftM (throw e : SysM D β)) := by
  cases o <;> simp [lm_throw_bind]

/-- Unfold the encoding and the baseline and normalize both to one monadic form:
the dictionary pushes the lift to the leaves, `match_bind` and the store fuse the
memory access into the `match` shape the encoding uses, and the state-operation
fusion and discard laws align the reads and writes. -/
local macro "fw_simp" : tactic =>
  `(tactic| simp only [Op.exec, Op.mov, Op.dec, Op.add, Op.adc, Op.lea, Op.xor, Op.push, Op.pop, liftBaseline, Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp, ConstExpr.interp, MachineData.set, evalAddr, lm_pure, lm_bind, lm_ebind, lm_get, lm_eget, lm_modify, lm_set, lm_throw, lm_throw_bind, lm_load_bind, lm_store, gm_gm, gm_mm, gm_mset, mm_mm, gm_gt, read_bind_const, getThe_bind_const, read_read, gt_gt, bind_assoc, pure_bind, bind_pure, match_bind, MachineData.setReg, Reg64s.get_low64, Reg64s.set_low64, Width.bytes, Width.bytesv, BitVec.ofInt_toInt, ze64, gm_store_fuse, BitVec.setWidth_64_64])

/-- For the register and load cases: normalize, then apply to a state and reduce
each primitive in one step, so the two matchers settle by a `rfl` over the small
residual rather than a whnf of the transformer stack. -/
local macro "adeq" : tactic =>
  `(tactic| (fw_simp; all_goals (funext env rip s; simp only [read_apply, getThe_apply, gm_apply, mm_apply, throw_apply, pure_apply]; try rfl)))

/-! ## Front-end dispatch adequacy

Each equation encodes one instruction shape against the baseline. `Op.exec` in
the `fw_simp` set reduces the dispatch to its primitive first, so `adeq` closes
the register and load cases; the memory-write, stack, and jump cases split the
mapped-ness or the branch by hand. -/

/-! ### Register moves -/

theorem Op.exec_mov_reg_imm_adequate {D} (r : Reg64) (i : Int64) :
    (Op.exec (.mov (.reg (.low r .W64)) (.imm (.int64 i))) : X64MNew D Unit)
      = liftBaseline (.mov (.reg (.low r .W64)) (.imm (.int64 i))) := by adeq

theorem Op.exec_mov_reg_reg_adequate {D} (rd rs : Reg64) :
    (Op.exec (.mov (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))) : X64MNew D Unit)
      = liftBaseline (.mov (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))) := by adeq

theorem Op.exec_mov_reg_mem_adequate {D} (rd : Reg64) (ae : AddrExpr) :
    (Op.exec (.mov (.reg (.low rd .W64)) (.regOrMem (.mem ae))) : X64MNew D Unit)
      = liftBaseline (.mov (.reg (.low rd .W64)) (.regOrMem (.mem ae))) := by adeq

/-- The memory-write cases commit a `Mem.storeInt`; a `rfl` over that record is
slow, so reduce the reads, split the mapped-ness, and reduce each branch. -/
theorem Op.exec_mov_mem_imm_adequate {D} (ae : AddrExpr) (i : Int64) :
    (Op.exec (.mov (.mem ae) (.imm (.int64 i))) : X64MNew D Unit)
      = liftBaseline (.mov (.mem ae) (.imm (.int64 i))) := by
  fw_simp
  funext env rip s
  simp only [read_apply, getThe_apply, gm_apply]
  cases Mem.loadInt s.machine.dmem (AddrExpr.interp env.labels (.mk .W64) ae s.machine.regs (.mk rip (rip + Int64.ofNat env.curSize))) 8 <;>
    simp only [mm_apply, throw_apply]

theorem Op.exec_mov_mem_reg_adequate {D} (ae : AddrExpr) (rs : Reg64) :
    (Op.exec (.mov (.mem ae) (.regOrMem (.reg (.low rs .W64)))) : X64MNew D Unit)
      = liftBaseline (.mov (.mem ae) (.regOrMem (.reg (.low rs .W64)))) := by
  fw_simp
  funext env rip s
  simp only [read_apply, getThe_apply, gm_apply]
  cases Mem.loadInt s.machine.dmem (AddrExpr.interp env.labels (.mk .W64) ae s.machine.regs (.mk rip (rip + Int64.ofNat env.curSize))) 8 <;>
    simp only [mm_apply, throw_apply]

/-! ### Arithmetic -/

theorem Op.exec_dec_reg_adequate {D} (r : Reg64) :
    (Op.exec (.dec (.reg (.low r .W64))) : X64MNew D Unit)
      = liftBaseline (.dec (.reg (.low r .W64))) := by adeq

theorem Op.exec_add_reg_imm_adequate {D} (r : Reg64) (i : Int64) :
    (Op.exec (.add (.reg (.low r .W64)) (.imm (.int64 i))) : X64MNew D Unit)
      = liftBaseline (.add (.reg (.low r .W64)) (.imm (.int64 i))) := by adeq

theorem Op.exec_add_reg_mem_adequate {D} (rd : Reg64) (ae : AddrExpr) :
    (Op.exec (.add (.reg (.low rd .W64)) (.regOrMem (.mem ae))) : X64MNew D Unit)
      = liftBaseline (.add (.reg (.low rd .W64)) (.regOrMem (.mem ae))) := by adeq

theorem Op.exec_adc_reg_reg_adequate {D} (rd rs : Reg64) :
    (Op.exec (.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))) : X64MNew D Unit)
      = liftBaseline (.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))) := by adeq

theorem Op.exec_lea_adequate {D} (rd : Reg64) (ae : AddrExpr) :
    (Op.exec (.lea (.low rd .W64) ae) : X64MNew D Unit)
      = liftBaseline (.lea (.low rd .W64) ae) := by adeq

/-! ### Flag-undefined family

`xor` (like the shifts and rotates) leaves a flag undefined, so both sides throw
`undefinedFlags` regardless of the operands. -/

theorem Op.exec_xor_adequate {D} (dst : Dst .W64) (src : Operand .W64) :
    (Op.exec (.xor dst src) : X64MNew D Unit) = liftBaseline (.xor dst src) := by fw_simp

/-! ### Stack -/

theorem Op.exec_push_reg_adequate {D} (r : Reg64) :
    (Op.exec (.push (.regOrMem (.reg (.low r .W64)))) : X64MNew D Unit)
      = liftBaseline (.push (.regOrMem (.reg (.low r .W64)))) := by
  fw_simp
  funext env rip s
  simp only [read_apply, getThe_apply, gm_apply]
  cases Mem.loadInt s.machine.dmem ((s.machine.regs.get64 .rsp) - 8#64) 8 <;>
    simp only [lm_throw_bind, mm_mm, mm_apply, throw_apply]

theorem Op.exec_pop_reg_adequate {D} (d : Reg64) :
    (Op.exec (.pop (.reg (.low d .W64))) : X64MNew D Unit)
      = liftBaseline (.pop (.reg (.low d .W64))) := by
  fw_simp
  funext env rip s
  simp only [read_apply, getThe_apply, gm_apply]
  cases Mem.loadInt s.machine.dmem (s.machine.regs.get64 .rsp) 8 <;>
    simp only [mm_apply, throw_apply]

/-! ### Conditional jump

`Op.exec` resolves the jump's `Label` against `env.labels`; the baseline resolves
it inside `Operation.interp`. The two agree, so the equation holds unapplied. -/

theorem Op.exec_jcc_adequate {D} (cc : CondCode) (l : Label) :
    (Op.exec (.jcc cc l) : X64MNew D Unit) = liftBaseline (.jcc cc l) := by
  funext env rip s
  simp only [Op.exec, Op.jcc, liftBaseline, Operation.interp, read_apply, getThe_apply,
    gm_apply, lm_bind, lm_ebind, lm_get, lm_eget, apply_ite, lm_throw, lm_pure, bind_assoc,
    pure_bind, throw_apply, pure_apply]

end Kraken
