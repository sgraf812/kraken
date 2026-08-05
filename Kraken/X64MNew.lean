/-
The denotational spec monad, parameterized by a device-state type `D`.

`labels` sits in a reader, `rip` in state, over the error-state machine monad
whose state is `MachineData × D`. Putting `D` in the machine state (rather
than an outer `StateT`) means a `jump` — an `EStateM` throw that carries the
state — preserves the device state, exactly as it preserves `MachineData`.

Instruction primitives mirror the `Operation` constructors and touch only the
`MachineData` component, threading `D` untouched, so their `@[spec]` triples are
polymorphic in `D`. Memory operands are evaluated through the baseline
`AddrExpr.interp`; conditional jumps carry a resolved `Int64` target.
-/
import Kraken.Specs

open Std.Internal.Do
open Std.Internal.Do.WPMonad
open Lean.Order

namespace Kraken

/-- Program-constant inputs: the label table, together with the encoded length of
the instruction now executing, from which the position range's upper bound (the
address of the next instruction) is formed. -/
structure Env where
  labels : Labels
  curSize : Nat

/-- Error-state over the system state `Sys D`. A thrown exit (a `jump`)
carries this whole state, so the device component survives control transfer. -/
abbrev SysM (D : Type) := EStateM X64Exit (Sys D)

/-- Reader over the label environment, state over `rip`, over the system monad. -/
abbrev X64MNew (D : Type) := ReaderT Env (StateT Int64 (SysM D))

/-- Read the `MachineData` component of the system state. -/
def getMachine {D : Type} : X64MNew D MachineData := do
  let s ← liftM (getThe (Sys D) : SysM D (Sys D))
  pure s.machine

/-- Update the `MachineData` component, leaving the device state untouched. -/
def modifyMachine {D : Type} (f : MachineData → MachineData) : X64MNew D Unit :=
  liftM (modify (fun s => { s with machine := f s.machine }) : SysM D Unit)

/-- Effective address of a memory operand, via the baseline address semantics.
The position range is `rip` up to the next instruction's address `rip + curSize`,
matching the x86 resolution of a rip-relative reference against the following
instruction. -/
def evalAddr {D : Type} (ae : AddrExpr) : X64MNew D (BitVec 64) := do
  let e ← read
  let pc ← getThe Int64
  let s ← getMachine
  pure (AddrExpr.interp e.labels (.mk .W64) ae s.regs (.mk pc (pc + Int64.ofNat e.curSize)))

namespace Op
variable {D : Type}

def mov (dst : Dst .W64) (src : Operand .W64) : X64MNew D Unit := do
  match dst, src with
  | .reg (.low r _), .imm (.int64 i) =>
    modifyMachine (fun s => { s with regs := s.regs.set64 r (.ofBitVec (BitVec.setWidth 64 i.toBitVec)) })
  | .reg (.low rd _), .regOrMem (.reg (.low rs _)) =>
    modifyMachine (fun s => { s with regs := s.regs.set64 rd (s.regs.get64 rs) })
  | .reg (.low dst _), .regOrMem (.mem ae) =>
    let addr ← evalAddr ae
    let s ← getMachine
    match Mem.loadInt s.dmem addr 8 with
    | some i => modifyMachine (fun s => { s with regs := s.regs.set64 dst (.ofBitVec (BitVec.ofInt 64 i)) })
    | none => liftM (throw (.nonmemLoad s.dmem addr .W64) : SysM D Unit)
  | .mem ae, .imm (.int64 i) =>
    let addr ← evalAddr ae
    let s ← getMachine
    match Mem.loadInt s.dmem addr 8 with
    | some _ =>
      modifyMachine (fun s => { s with dmem := Mem.storeInt s.dmem addr 8 (BitVec.setWidth 64 i.toBitVec).toInt })
    | none => liftM (throw (.nonmemStore s.dmem addr .W64) : SysM D Unit)
  | .mem ae, .regOrMem (.reg (.low src _)) =>
    let addr ← evalAddr ae
    let s ← getMachine
    match Mem.loadInt s.dmem addr 8 with
    | some _ =>
      modifyMachine (fun s => { s with dmem := Mem.storeInt s.dmem addr 8 (s.regs.get64 src).toBitVec.toInt })
    | none => liftM (throw (.nonmemStore s.dmem addr .W64) : SysM D Unit)
  | _, _ => liftM (throw (.unimplemented "mov") : SysM D Unit)

def dec (o : Dst .W64) : X64MNew D Unit := do
  match o with
  | .reg (.low r _) =>
    modifyMachine (fun s =>
      let a := (s.regs.get64 r).toBitVec
      let v := a - 1
      let status := StatusFlags.from_result v
        { cf := s.status.cf,
          af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
          of := v.signed != a.signed - 1 }
      { s with status := status, regs := s.regs.set64 r (.ofBitVec v) })
  | _ => liftM (throw (.unimplemented "dec") : SysM D Unit)

/-- Conditional jump to a resolved `Int64` target: jump when the condition holds,
fall through otherwise. -/
def jcc (cc : CondCode) (l : Int64) : X64MNew D Unit := do
  let s ← getMachine
  if cc.interp s.status then liftM (throw (.jump l) : SysM D Unit) else pure ()

def add (dst : Dst .W64) (src : Operand .W64) : X64MNew D Unit := do
  match dst, src with
  | .reg (.low r _), .imm (.int64 i) =>
    modifyMachine (fun s =>
      let a := BitVec.setWidth 64 i.toBitVec
      let b := (s.regs.get64 r).toBitVec
      let v := a + b
      let status := StatusFlags.from_result v
        { cf := v.unsigned != a.unsigned + b.unsigned,
          af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
          of := v.signed != a.signed + b.signed }
      { s with status := status, regs := s.regs.set64 r (.ofBitVec v) })
  | .reg (.low dst _), .regOrMem (.mem ae) =>
    let addr ← evalAddr ae
    let s ← getMachine
    match Mem.loadInt s.dmem addr 8 with
    | some x =>
      modifyMachine (fun s =>
        let av := BitVec.ofInt 64 x
        let bv := (s.regs.get64 dst).toBitVec
        let v := av + bv
        let status := StatusFlags.from_result v
          { cf := v.unsigned != av.unsigned + bv.unsigned,
            af := (v.take 4).unsigned != (av.take 4).unsigned + (bv.take 4).unsigned,
            of := v.signed != av.signed + bv.signed }
        { s with status := status, regs := s.regs.set64 dst (.ofBitVec v) })
    | none => liftM (throw (.nonmemLoad s.dmem addr .W64) : SysM D Unit)
  | _, _ => liftM (throw (.unimplemented "add") : SysM D Unit)

def adc (dst : Dst .W64) (src : Operand .W64) : X64MNew D Unit := do
  match dst, src with
  | .reg (.low rd _), .regOrMem (.reg (.low rs _)) =>
    modifyMachine (fun s =>
      let a := (s.regs.get64 rs).toBitVec
      let b := (s.regs.get64 rd).toBitVec
      let c := s.status.cf
      let v := a + b + BitVec.ofNat 64 c.toNat
      let status := StatusFlags.from_result v
        { cf := v.unsigned != a.unsigned + b.unsigned + c.toNat,
          af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned + c.toNat,
          of := v.signed != a.signed + b.signed + c.toNat }
      { s with status := status, regs := s.regs.set64 rd (.ofBitVec v) })
  | _, _ => liftM (throw (.unimplemented "adc") : SysM D Unit)

def lea (dst : Reg64) (ae : AddrExpr) : X64MNew D Unit := do
  let addr ← evalAddr ae
  modifyMachine (fun s => { s with regs := s.regs.set64 dst (.ofBitVec addr) })

/-- `xor` leaves `AF` architecturally undefined, so the baseline throws
`undefinedFlags` rather than commit to a value; the encoding matches it. -/
def xor (_dst : Dst .W64) (_src : Operand .W64) : X64MNew D Unit :=
  liftM (throw .undefinedFlags : SysM D Unit)

def push (o : Operand .W64) : X64MNew D Unit := do
  match o with
  | .regOrMem (.reg (.low r _)) =>
    let s ← getMachine
    let rsp := (s.regs.get64 .rsp).toBitVec - 8#64
    match Mem.loadInt s.dmem rsp 8 with
    | some _ =>
      modifyMachine (fun s => { s with
        regs := s.regs.set64 .rsp (.ofBitVec rsp),
        dmem := Mem.storeInt s.dmem rsp 8 (s.regs.get64 r).toBitVec.toInt })
    | none => liftM (throw (.nonmemStore s.dmem rsp .W64) : SysM D Unit)
  | _ => liftM (throw (.unimplemented "push") : SysM D Unit)

def pop (dst : Dst .W64) : X64MNew D Unit := do
  match dst with
  | .reg (.low d _) =>
    let s ← getMachine
    let rsp := (s.regs.get64 .rsp).toBitVec
    match Mem.loadInt s.dmem rsp 8 with
    | some i =>
      modifyMachine (fun s => { s with
        regs := (s.regs.set64 .rsp (.ofBitVec (rsp + 8#64))).set64 d (.ofBitVec (BitVec.ofInt 64 i)) })
    | none => liftM (throw (.nonmemLoad s.dmem rsp .W64) : SysM D Unit)
  | _ => liftM (throw (.unimplemented "pop") : SysM D Unit)

/-- Dispatch a decoded operation to its encoded primitive, resolving a jump's
label against the environment. An operation or operand shape without an encoding
throws `unimplemented`. -/
def exec (op : Operation .W64) : X64MNew D Unit :=
  match op with
  | .mov dst src => mov dst src
  | .add dst src => add dst src
  | .adc dst src => adc dst src
  | .dec o => dec o
  | .xor dst src => xor dst src
  | .lea (.low r _) ae => lea r ae
  | .push src => push src
  | .pop dst => pop dst
  | .jcc cc l => do let env ← read; jcc cc (env.labels.label l)
  | _ => liftM (throw (.unimplemented "exec") : SysM D Unit)

end Op

/-! ## Program driver

`execDirs` runs a laid-out directive list the way the baseline `Directives.interp`
does: each instruction executes at its address, `rip` advancing by the encoded
size, so the position range read for that instruction is `.mk pc (pc+sz)`, the one
the baseline supplies. An instruction dispatches through `Op.exec`; a label is a
no-op; a data block or a non-64-bit instruction throws. -/

def execDir {D : Type} (d : Directive) : X64MNew D Unit :=
  match d with
  | .label _ => pure ()
  | .instr (.regular .W64 .W64 op) => Op.exec op
  | _ => liftM (throw (.unimplemented "execDir") : SysM D Unit)

/-- Run `x` with the executing instruction's encoded length recorded on the
reader, so the position range it reads spans to the next instruction. -/
def withCurSize {D α : Type} (sz : Nat) (x : X64MNew D α) : X64MNew D α :=
  withReader (fun e => { e with curSize := sz }) x

def execDirs {D : Type} (ds : List (Directive × Nat)) : X64MNew D Unit := do
  match ds with
  | [] => pure ()
  | (d, sz) :: ds =>
    withCurSize sz (execDir d)
    modifyThe Int64 (· + Int64.ofNat sz)
    execDirs ds

/-! ## Control flow

`execStraightlineFrom` runs from the current `rip` to the end of the program, a
taken jump throwing `X64Exit.jump`. `execProgram` catches that throw and resumes
at the target, bounded by `fuel`: unrolling it `fuel` times yields a finite
do-block, so a loop is verified by running the body a fixed number of times. A
`modifyMachine` write lands in the `Sys D` state a `jump` throw carries, so the
machine state at the jump survives into the handler; the handler sets `rip` to the
target, replacing whatever `rip` the interrupted segment reached. -/

def execStraightlineFrom {D : Type} (e : Executable) : X64MNew D Unit := do
  let pc ← getThe Int64
  execDirs (e.directivesFromAddress pc)

def execProgram {D : Type} (e : Executable) : Nat → X64MNew D Unit
  | 0 => pure ()
  | fuel + 1 =>
    tryCatch (execStraightlineFrom e) fun exc =>
      match exc with
      | .jump pc => do modifyThe Int64 (fun _ => pc); execProgram e fuel
      | exc => throw exc

/-! ## Specs, discriminating on operand shape, polymorphic in `D` -/

section
variable {D : Type} (Q : Unit → Env → Int64 → Sys D → Prop)
    (E : X64Exit → Sys D → Prop)

@[spec] theorem Op.mov_reg_imm_spec (r : Reg64) (i : Int64) :
    ⦃ fun env rip s =>
        Q () env rip { s with machine := { s.machine with regs := s.machine.regs.set64 r (.ofBitVec (BitVec.setWidth 64 i.toBitVec)) } } ⦄
      Op.mov (.reg (.low r .W64)) (.imm (.int64 i)) ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.mov, modifyMachine]
    all_goals finish

@[spec] theorem Op.mov_reg_reg_spec (rd rs : Reg64) :
    ⦃ fun env rip s => Q () env rip { s with machine := { s.machine with regs := s.machine.regs.set64 rd (s.machine.regs.get64 rs) } } ⦄
      Op.mov (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))) ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.mov, modifyMachine]
    all_goals finish

@[spec] theorem Op.mov_reg_mem_spec (dst : Reg64) (ae : AddrExpr) (v : Int) :
    ⦃ fun env rip s =>
        (Mem.loadInt s.machine.dmem (AddrExpr.interp env.labels (.mk .W64) ae s.machine.regs (.mk rip (rip + Int64.ofNat env.curSize))) 8 = some v) ⊓
        Q () env rip { s with machine := { s.machine with regs := s.machine.regs.set64 dst (.ofBitVec (BitVec.ofInt 64 v)) } } ⦄
      Op.mov (.reg (.low dst .W64)) (.regOrMem (.mem ae)) ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.mov, evalAddr, getMachine, modifyMachine]
    all_goals finish

@[spec] theorem Op.mov_mem_imm_spec (ae : AddrExpr) (i : Int64) (v : Int) :
    ⦃ fun env rip s =>
        (Mem.loadInt s.machine.dmem (AddrExpr.interp env.labels (.mk .W64) ae s.machine.regs (.mk rip (rip + Int64.ofNat env.curSize))) 8 = some v) ⊓
        Q () env rip { s with machine := { s.machine with
          dmem := Mem.storeInt s.machine.dmem (AddrExpr.interp env.labels (.mk .W64) ae s.machine.regs (.mk rip (rip + Int64.ofNat env.curSize))) 8
            (BitVec.setWidth 64 i.toBitVec).toInt } } ⦄
      Op.mov (.mem ae) (.imm (.int64 i)) ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.mov, evalAddr, getMachine, modifyMachine]
    all_goals finish

@[spec] theorem Op.mov_mem_reg_spec (ae : AddrExpr) (src : Reg64) (v : Int) :
    ⦃ fun env rip s =>
        (Mem.loadInt s.machine.dmem (AddrExpr.interp env.labels (.mk .W64) ae s.machine.regs (.mk rip (rip + Int64.ofNat env.curSize))) 8 = some v) ⊓
        Q () env rip { s with machine := { s.machine with
          dmem := Mem.storeInt s.machine.dmem (AddrExpr.interp env.labels (.mk .W64) ae s.machine.regs (.mk rip (rip + Int64.ofNat env.curSize))) 8
            (s.machine.regs.get64 src).toBitVec.toInt } } ⦄
      Op.mov (.mem ae) (.regOrMem (.reg (.low src .W64))) ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.mov, evalAddr, getMachine, modifyMachine]
    all_goals finish

@[spec] theorem Op.dec_reg_spec (r : Reg64) :
    ⦃ fun env rip s =>
        Q () env rip { s with machine := { s.machine with
            regs := s.machine.regs.set64 r (.ofBitVec ((s.machine.regs.get64 r).toBitVec - 1))
            status := StatusFlags.from_result ((s.machine.regs.get64 r).toBitVec - 1)
              { cf := s.machine.status.cf,
                af := (((s.machine.regs.get64 r).toBitVec - 1).take 4).unsigned
                  != ((s.machine.regs.get64 r).toBitVec.take 4).unsigned - 1,
                of := ((s.machine.regs.get64 r).toBitVec - 1).signed
                  != (s.machine.regs.get64 r).toBitVec.signed - 1 } } } ⦄
      Op.dec (.reg (.low r .W64)) ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.dec, modifyMachine]
    all_goals finish

/-- A conditional jump: the jump post under the taken condition, the fall-through
post otherwise. On a jump the exception post receives the whole state `s`, so the
device component survives. -/
@[spec] theorem Op.jcc_spec (cc : CondCode) (l : Int64) :
    ⦃ fun env rip s => if cc.interp s.machine.status then E (X64Exit.jump l) s else Q () env rip s ⦄
      Op.jcc cc l ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.jcc, getMachine]
    all_goals finish

@[spec] theorem Op.add_reg_imm_spec (r : Reg64) (i : Int64) :
    ⦃ fun env rip s =>
        Q () env rip { s with machine := { s.machine with
            regs := s.machine.regs.set64 r
              (.ofBitVec (BitVec.setWidth 64 i.toBitVec + (s.machine.regs.get64 r).toBitVec))
            status := StatusFlags.from_result
              (BitVec.setWidth 64 i.toBitVec + (s.machine.regs.get64 r).toBitVec)
              { cf := (BitVec.setWidth 64 i.toBitVec + (s.machine.regs.get64 r).toBitVec).unsigned
                  != (BitVec.setWidth 64 i.toBitVec).unsigned + (s.machine.regs.get64 r).toBitVec.unsigned,
                af := ((BitVec.setWidth 64 i.toBitVec + (s.machine.regs.get64 r).toBitVec).take 4).unsigned
                  != ((BitVec.setWidth 64 i.toBitVec).take 4).unsigned
                    + ((s.machine.regs.get64 r).toBitVec.take 4).unsigned,
                of := (BitVec.setWidth 64 i.toBitVec + (s.machine.regs.get64 r).toBitVec).signed
                  != (BitVec.setWidth 64 i.toBitVec).signed + (s.machine.regs.get64 r).toBitVec.signed } } } ⦄
      Op.add (.reg (.low r .W64)) (.imm (.int64 i)) ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.add, modifyMachine]
    all_goals finish

@[spec] theorem Op.add_reg_mem_spec (dst : Reg64) (ae : AddrExpr) (v : Int) :
    ⦃ fun env rip s =>
        (Mem.loadInt s.machine.dmem (AddrExpr.interp env.labels (.mk .W64) ae s.machine.regs (.mk rip (rip + Int64.ofNat env.curSize))) 8 = some v) ⊓
        Q () env rip { s with machine := { s.machine with
            regs := s.machine.regs.set64 dst (.ofBitVec (BitVec.ofInt 64 v + (s.machine.regs.get64 dst).toBitVec))
            status := StatusFlags.from_result (BitVec.ofInt 64 v + (s.machine.regs.get64 dst).toBitVec)
              { cf := (BitVec.ofInt 64 v + (s.machine.regs.get64 dst).toBitVec).unsigned
                  != (BitVec.ofInt 64 v).unsigned + (s.machine.regs.get64 dst).toBitVec.unsigned,
                af := ((BitVec.ofInt 64 v + (s.machine.regs.get64 dst).toBitVec).take 4).unsigned
                  != ((BitVec.ofInt 64 v).take 4).unsigned + ((s.machine.regs.get64 dst).toBitVec.take 4).unsigned,
                of := (BitVec.ofInt 64 v + (s.machine.regs.get64 dst).toBitVec).signed
                  != (BitVec.ofInt 64 v).signed + (s.machine.regs.get64 dst).toBitVec.signed } } } ⦄
      Op.add (.reg (.low dst .W64)) (.regOrMem (.mem ae)) ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.add, evalAddr, getMachine, modifyMachine]
    all_goals finish

@[spec] theorem Op.adc_reg_reg_spec (rd rs : Reg64) :
    ⦃ fun env rip s =>
        Q () env rip { s with machine := { s.machine with
            regs := s.machine.regs.set64 rd (.ofBitVec ((s.machine.regs.get64 rs).toBitVec
              + (s.machine.regs.get64 rd).toBitVec + BitVec.ofNat 64 s.machine.status.cf.toNat))
            status := StatusFlags.from_result ((s.machine.regs.get64 rs).toBitVec
                + (s.machine.regs.get64 rd).toBitVec + BitVec.ofNat 64 s.machine.status.cf.toNat)
              { cf := ((s.machine.regs.get64 rs).toBitVec + (s.machine.regs.get64 rd).toBitVec
                    + BitVec.ofNat 64 s.machine.status.cf.toNat).unsigned
                  != (s.machine.regs.get64 rs).toBitVec.unsigned + (s.machine.regs.get64 rd).toBitVec.unsigned
                    + s.machine.status.cf.toNat,
                af := (((s.machine.regs.get64 rs).toBitVec + (s.machine.regs.get64 rd).toBitVec
                    + BitVec.ofNat 64 s.machine.status.cf.toNat).take 4).unsigned
                  != ((s.machine.regs.get64 rs).toBitVec.take 4).unsigned
                    + ((s.machine.regs.get64 rd).toBitVec.take 4).unsigned + s.machine.status.cf.toNat,
                of := ((s.machine.regs.get64 rs).toBitVec + (s.machine.regs.get64 rd).toBitVec
                    + BitVec.ofNat 64 s.machine.status.cf.toNat).signed
                  != (s.machine.regs.get64 rs).toBitVec.signed + (s.machine.regs.get64 rd).toBitVec.signed
                    + s.machine.status.cf.toNat } } } ⦄
      Op.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))) ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.adc, modifyMachine]
    all_goals finish

@[spec] theorem Op.lea_spec (dst : Reg64) (ae : AddrExpr) :
    ⦃ fun env rip s =>
        Q () env rip { s with machine := { s.machine with
          regs := s.machine.regs.set64 dst (.ofBitVec (AddrExpr.interp env.labels (.mk .W64) ae s.machine.regs (.mk rip (rip + Int64.ofNat env.curSize)))) } } ⦄
      Op.lea dst ae ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.lea, evalAddr, getMachine, modifyMachine]
    all_goals finish

@[spec] theorem Op.xor_spec (dst : Dst .W64) (src : Operand .W64) :
    ⦃ fun _ _ s => E .undefinedFlags s ⦄ Op.xor dst src ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.xor]
    all_goals finish

@[spec] theorem Op.push_reg_spec (r : Reg64) (v : Int) :
    ⦃ fun env rip s =>
        (Mem.loadInt s.machine.dmem ((s.machine.regs.get64 .rsp).toBitVec - 8#64) 8 = some v) ⊓
        Q () env rip { s with machine := { s.machine with
          regs := s.machine.regs.set64 .rsp (.ofBitVec ((s.machine.regs.get64 .rsp).toBitVec - 8#64))
          dmem := Mem.storeInt s.machine.dmem ((s.machine.regs.get64 .rsp).toBitVec - 8#64) 8
            (s.machine.regs.get64 r).toBitVec.toInt } } ⦄
      Op.push (.regOrMem (.reg (.low r .W64))) ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.push, getMachine, modifyMachine]
    all_goals finish

@[spec] theorem Op.pop_reg_spec (dst : Reg64) (v : Int) :
    ⦃ fun env rip s =>
        (Mem.loadInt s.machine.dmem (s.machine.regs.get64 .rsp).toBitVec 8 = some v) ⊓
        Q () env rip { s with machine := { s.machine with
          regs := (s.machine.regs.set64 .rsp (.ofBitVec ((s.machine.regs.get64 .rsp).toBitVec + 8#64))).set64 dst
            (.ofBitVec (BitVec.ofInt 64 v)) } } ⦄
      Op.pop (.reg (.low dst .W64)) ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.pop, getMachine, modifyMachine]
    all_goals finish

end

end Kraken
