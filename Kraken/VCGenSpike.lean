/-
Spike: connect the omnisemantics `Effects.All` to the `vcgen` tactic via a
`Std.Internal.Do.WP` instance, to replace the manual straightline stepping
(`kstep`). Memory side conditions enter as plain `Mem.loadInt … = some _`
hypotheses; separation reasoning stays outside the vcgen layer.
-/
import Kraken.OmniSemantics
import Kraken.X64Sep
import Kraken.Parser
import Kraken.Eval
import Kraken.Separation
import Std.Tactic.Do

set_option mvcgen.warning false
set_option grind.warning false

open Std.Internal.Do
open Std.ExtHashMap

/-! ## The WP instance -/

theorem Effects.All.mono {p q : @Post MachineState} (h : ∀ a, p a → q a) (e : Effects) :
    e.All p → e.All q := by
  induction e <;> simp_all [Effects.All]

instance Effects.instWP : WP Effects MachineState Prop EPost.Nil where
  wpTrans e := ⟨fun post _ => e.All post⟩
  wp_trans_monotone e := fun _post _post' _ _ _ hpost => Effects.All.mono (fun a => hpost a) e

theorem Effects.wp_eq_All (e : Effects) (post : MachineState → Prop) (epost : EPost.Nil) :
    wp e post epost = e.All post := rfl

theorem Effects.all_of_triple {e : Effects} {post : MachineState → Prop}
    (h : ⦃True⦄ e ⦃post⦄) : e.All post :=
  h.le_wp trivial

/-! ## Specs for the effect nodes -/

@[spec] theorem Effects.done_spec (a : MachineState) (post : MachineState → Prop)
    (epost : EPost.Nil) :
    ⦃ post a ⦄ Effects.done a ⦃ post; epost ⦄ :=
  ⟨fun h => h⟩

@[spec] theorem Effects.require_exec_access_spec (p : Std.Rco Int64) (k : Unit → Effects)
    (post : MachineState → Prop) (epost : EPost.Nil) :
    ⦃ wp (k ()) post epost ⦄ Effects.require_exec_access p k ⦃ post; epost ⦄ :=
  ⟨fun h => h⟩

@[spec] theorem Effects.require_read_access_spec (addr : BitVec 64) (w : Width)
    (k : Unit → Effects) (post : MachineState → Prop) (epost : EPost.Nil) :
    ⦃ wp (k ()) post epost ⦄ Effects.require_read_access addr w k ⦃ post; epost ⦄ :=
  ⟨fun h => h⟩

@[spec] theorem Effects.require_write_access_spec (addr : BitVec 64) (w : Width)
    (k : Unit → Effects) (post : MachineState → Prop) (epost : EPost.Nil) :
    ⦃ wp (k ()) post epost ⦄ Effects.require_write_access addr w k ⦃ post; epost ⦄ :=
  ⟨fun h => h⟩

@[spec] theorem Effects.undefined_spec {α : Type} [NondetSupportingType α] (k : α → Effects)
    (post : MachineState → Prop) (epost : EPost.Nil) :
    ⦃ ∀ v, wp (k v) post epost ⦄ Effects.undefined k ⦃ post; epost ⦄ :=
  ⟨fun h => h⟩

/-! ## Specs for the memory primitives

The `some`-hypothesis pins the match inside `MachineData.load`/`store`; it is
established before running `vcgen`, e.g. from a separation hypothesis via
`Mem.loadInt_sep`. -/

@[spec] theorem MachineData.load_spec (s : MachineData) (addr : BitVec 64) (w : Width)
    (ret : w.type → MachineData → Effects) (i : Int)
    (h : Mem.loadInt s.dmem addr w.bytes = some i)
    (post : MachineState → Prop) (epost : EPost.Nil) :
    ⦃ wp (ret (.ofInt w.bits i) s) post epost ⦄ MachineData.load s addr w ret ⦃ post; epost ⦄ := by
  constructor
  intro hwp
  show (MachineData.load s addr w ret).All post
  simp only [MachineData.load, h]
  exact hwp

@[spec] theorem MachineData.store_spec (s : MachineData) (addr : BitVec 64) {w : Width}
    (v : w.type) (ret : MachineData → Effects) (i : Int)
    (h : Mem.loadInt s.dmem addr w.bytes = some i)
    (post : MachineState → Prop) (epost : EPost.Nil) :
    ⦃ wp (ret { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }) post epost ⦄
      MachineData.store s addr v ret ⦃ post; epost ⦄ := by
  constructor
  intro hwp
  show (MachineData.store s addr v ret).All post
  simp only [MachineData.store, h]
  exact hwp

/-! ## Per-instruction specs

One Triple per `Operation` constructor, keyed on the constructor pattern; the
precondition is the wp of the instruction's own CPS expansion, so the proof is
definitional. This replaces equation-unfolding of `Operation.interp`. -/

section InstrSpecs
variable [Labels] [AddressSize] {w : Width}
  (p : Std.Rco Int64) (s : MachineData)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects)
  (post : MachineState → Prop) (epost : EPost.Nil)

@[spec] theorem Operation.mov_spec (dst : Dst w) (src : Operand w) :
    ⦃ wp (src.interp s p (fun val s => s.set dst val p next)) post epost ⦄
      Operation.interp (.mov dst src) p s next jmp ⦃ post; epost ⦄ :=
  ⟨fun h => h⟩

@[spec] theorem Operation.dec_spec (dst : Dst w) :
    ⦃ wp (dst.interp s p (fun a s =>
        let v := a - 1
        let status := StatusFlags.from_result v {
          cf := s.status.cf
          af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
          of := v.signed != a.signed - 1 }
        { s with status }.set dst v p next)) post epost ⦄
      Operation.interp (.dec dst) p s next jmp ⦃ post; epost ⦄ :=
  ⟨fun h => h⟩

@[spec] theorem Operation.push_spec (src : Operand w) :
    ⦃ wp (src.interp s p (fun v s =>
        let rsp := s.regs.get64 .rsp - w.bytesv
        { s with regs := s.regs.set64 .rsp rsp }.store rsp v next)) post epost ⦄
      Operation.interp (.push src) p s next jmp ⦃ post; epost ⦄ :=
  ⟨fun h => h⟩

@[spec] theorem Operation.pop_spec (dst : Dst w) :
    ⦃ wp (let rsp := s.regs.get64 .rsp
          s.load rsp w (fun val s =>
          let s := { s with regs := s.regs.set64 .rsp (rsp + w.bytesv) }
          s.set dst val p next)) post epost ⦄
      Operation.interp (.pop dst) p s next jmp ⦃ post; epost ⦄ :=
  ⟨fun h => h⟩

@[spec] theorem Operation.lea_spec (dst : Reg w) (src : AddrExpr) :
    ⦃ wp (next (s.setReg dst ((src.interp s.regs p).zeroExtend _))) post epost ⦄
      Operation.interp (.lea dst src) p s next jmp ⦃ post; epost ⦄ :=
  ⟨fun h => h⟩

end InstrSpecs

/-! ## Stepping examples -/

open Kraken.Parser

theorem Executable.directivesFromStart' [layout : Layout] prog :
    (layout prog).directivesFromAddress layout.start = prog.mapIdx (fun i d => (d, layout.size i)) := by
  induction prog <;> simp [Executable.directivesFromAddress, Executable.withAddresses, Layout.apply]

def sp4 := eval% parse("start: mov $2, %rax
dec %rax")

example [layout : Layout] s : straightlineStep (layout sp4) (s, layout.start) (fun s => s.1.regs.rax = 1) := by
  let ss := s
  change (straightlineStep _ (ss, _) _)
  cases s with | mk regs zmms flags mem =>
  cases regs with | mk rax rbx rcx rdx rsi rdi rsp rbp r8 r9 r10 r11 r12 r13 r14 r15 =>
  delta sp4
  dsimp only [straightlineStep, Executable.straightline]
  rw [Executable.directivesFromStart']
  simp [List.mapIdx, List.mapIdx.go]
  apply Effects.all_of_triple
  sym =>
    vcgen -internalize [Directives.interp, Directive.interp, Instr.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, MachineData.set]
    all_goals tactic =>
      (simp only [ConstExpr.interp, MachineData.setReg, Reg64s.set, Reg64s.set64, Reg64s.get,
         Reg64s.get64, Reg.base, Reg.offset, BitVec.take, BitVec.drop];
       decide)

def sp6 := parse("push %rax
mov $0, %rax
pop %rax")

set_option maxHeartbeats 1000000 in
theorem sp6_correct [layout : Layout] (s₀ : MachineData)
    (stack : List UInt8) (h_len : stack.length = 8) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (stack.At (s₀.regs.rsp.toBitVec - 8#64)) ⋆ R) :
    Eventually (straightlineStep (layout sp6))
      (fun s' => s'.1.regs.rax = s₀.regs.rax ∧ s'.1.regs.rsp = s₀.regs.rsp)
      (s₀, layout.start) := by
  apply step_cps
  cases s₀ with | mk regs zmms flags mem =>
  cases regs with | mk rax rbx rcx rdx rsi rdi rsp rbp r8 r9 r10 r11 r12 r13 r14 r15 =>
  simp only at h_mem
  -- memory facts, derived from the separation hypothesis before entering vcgen
  have h_load0 : Mem.loadInt mem (rsp.toBitVec - 8#64) 8 = some (Int.ofBytes stack) :=
    Mem.loadInt_sep stack _ 8 R mem h_mem h_len (by decide)
  have h_mem1 := Mem.storeInt_sep (rsp.toBitVec - 8#64) 8 stack R mem ⟨h_mem, h_len⟩ rax.toBitVec.toInt
  have h_load1 : Mem.loadInt (Mem.storeInt mem (rsp.toBitVec - 8#64) 8 rax.toBitVec.toInt)
      (rsp.toBitVec - 8#64) 8 = some (Int.ofBytes (Int.toBytes 8 rax.toBitVec.toInt)) :=
    Mem.loadInt_sep _ _ 8 R _ h_mem1 (Int.toBytes_length 8 _) (by decide)
  delta sp6
  dsimp only [straightlineStep, Executable.straightline]
  rw [Executable.directivesFromStart']
  simp [List.mapIdx, List.mapIdx.go]
  apply Effects.all_of_triple
  sym =>
    vcgen -internalize [Directives.interp, Directive.interp, Instr.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, MachineData.set]
    all_goals tactic =>
      first
      | (simp [MachineData.setReg, Reg64s.set, Reg64s.set64, Reg64s.get, Reg64s.get64,
           Reg.base, Reg.offset, ConstExpr.interp, BitVec.take, BitVec.drop, Width.bits,
           Int64.toBitVec_ofNat, UInt64.ofBitVec_ofNat,
           UInt64.toBitVec_sub, UInt64.toBitVec_ofNat, UInt64.ofBitVec_add, UInt64.ofBitVec_sub,
           UInt64.ofBitVec_toBitVec, h_load0, h_load1] <;> rfl)
      | (apply Eventually.done;
         simp only [MachineData.setReg, Reg64s.set, Reg64s.set64, Reg64s.get, Reg64s.get64,
           Reg.base, Reg.offset, ConstExpr.interp, BitVec.take, BitVec.drop,
           Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.setWidth_eq, UInt64.ofBitVec_ofNat,
           UInt64.toBitVec_sub, UInt64.toBitVec_ofNat, UInt64.ofBitVec_add, UInt64.ofBitVec_sub,
           UInt64.ofBitVec_toBitVec, UInt64.sub_add_cancel, and_true];
         have hv : UInt64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 rax.toBitVec.toInt))) = rax := by
           rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, UInt64.ofBitVec_toBitVec]
         exact hv)

def sdyn := parse("
    movq $99, -8(%rsp)
    movq %rsp, %rbp
    leaq -1024(%rsp, %r9, 8), %rsp
    movq $42, %rax
    movq %rax, 16(%rsp, %r15, 8)
    movq $0, %rax
    movq 16(%rsp, %r15, 8), %rax
    movq %rbp, %rsp
    movq -8(%rsp), %rbx
")

set_option maxHeartbeats 1000000 in
theorem sdyn_correct [layout : Layout] (s₀ : MachineData)
    (stack : List UInt8) (lstack : stack.length = 1024) (R : DataMem → Prop)
    (h : s₀.regs.r9.toNat + s₀.regs.r15.toNat < 125)
    (h_mem : s₀.dmem =⋆ Eq (stack.At (s₀.regs.rsp.toBitVec - 1024)) ⋆ R) :
    Eventually (straightlineStep (layout sdyn))
      (fun s' => s'.1.regs.rax = 42 ∧ s'.1.regs.rbx = 99 ∧ s'.1.regs.rsp = s₀.regs.rsp)
      (s₀, layout.start) := by
  apply step_cps
  cases s₀ with | mk regs zmms flags mem =>
  cases regs with | mk rax rbx rcx rdx rsi rdi rsp rbp r8 r9 r10 r11 r12 r13 r14 r15 =>
  simp only at h_mem h
  -- the 1024-byte stack region, split at the last 8 bytes (the -8(%rsp) slot)
  have h_split : stack = stack.take 1016 ++ stack.drop 1016 := (List.take_append_drop 1016 stack).symm
  have h_len_take : (stack.take 1016).length = 1016 := by simp [lstack]
  have h_len_drop : (stack.drop 1016).length = 8 := by simp [lstack]
  rw [h_split, Mem.At_append_sep _ _ _ (by rw [h_len_take, h_len_drop]; decide), sep_assoc] at h_mem
  rw [h_len_take] at h_mem
  -- slot for -8(%rsp): last 8 bytes, at rsp - 8
  have h_addr3 : rsp.toBitVec - 1024 + 1016#64 = rsp.toBitVec - 8#64 := by bv_decide
  rw [h_addr3] at h_mem
  -- facts for instruction 1: store $99 to rsp - 8
  replace h_mem : (Eq ((stack.drop 1016).At (rsp.toBitVec - 8#64)) ⋆
      (Eq ((stack.take 1016).At (rsp.toBitVec - 1024)) ⋆ R)) mem :=
    cast (congrFun (by ac_rfl) _) h_mem
  have h_L1 : Mem.loadInt mem (rsp.toBitVec - 8#64) 8 = some (Int.ofBytes (stack.drop 1016)) :=
    Mem.loadInt_sep _ _ 8 _ mem h_mem h_len_drop (by decide)
  have h_mem1 := Mem.storeInt_sep (rsp.toBitVec - 8#64) 8 (stack.drop 1016) _ mem ⟨h_mem, h_len_drop⟩ 99
  -- split the low 1016 bytes at the dynamic slot offset o = 16 + 8*(r9+r15)
  have h_o : 16 + 8 * (r9.toNat + r15.toNat) + 8 ≤ 1016 := by omega
  have h_lt1 : ((stack.take 1016).take (16 + 8 * (r9.toNat + r15.toNat))).length
      = 16 + 8 * (r9.toNat + r15.toNat) := by simp [lstack]; omega
  have h_lt2 : (((stack.take 1016).drop (16 + 8 * (r9.toNat + r15.toNat))).take 8).length = 8 := by
    simp [lstack]; omega
  rw [show stack.take 1016
        = (stack.take 1016).take (16 + 8 * (r9.toNat + r15.toNat))
          ++ (stack.take 1016).drop (16 + 8 * (r9.toNat + r15.toNat))
      from (List.take_append_drop _ _).symm,
      Mem.At_append_sep _ _ _ (by simp [lstack]; omega),
      show (stack.take 1016).drop (16 + 8 * (r9.toNat + r15.toNat))
        = ((stack.take 1016).drop (16 + 8 * (r9.toNat + r15.toNat))).take 8
          ++ ((stack.take 1016).drop (16 + 8 * (r9.toNat + r15.toNat))).drop 8
      from (List.take_append_drop _ _).symm,
      Mem.At_append_sep _ _ _ (by simp [lstack]; omega),
      h_lt1, h_lt2, sep_assoc] at h_mem1
  -- facts for instruction 5/7: store 42 to, then load from, the dynamic slot
  replace h_mem1 : (Eq
        ((List.take 8 (List.drop (16 + 8 * (r9.toNat + r15.toNat)) (List.take 1016 stack))).At
          (rsp.toBitVec - 1024 + BitVec.ofNat 64 (16 + 8 * (r9.toNat + r15.toNat)))) ⋆
      (Eq ((Int.toBytes 8 99).At (rsp.toBitVec - 8#64)) ⋆
        Eq ((List.take (16 + 8 * (r9.toNat + r15.toNat)) (List.take 1016 stack)).At (rsp.toBitVec - 1024)) ⋆
        Eq ((List.drop 8 (List.drop (16 + 8 * (r9.toNat + r15.toNat)) (List.take 1016 stack))).At
          (rsp.toBitVec - 1024 + BitVec.ofNat 64 (16 + 8 * (r9.toNat + r15.toNat)) + 8#64)) ⋆
        R)) (Mem.storeInt mem (rsp.toBitVec - 8#64) 8 99) :=
    cast (congrFun (by ac_rfl) _) h_mem1
  have h_L2 := Mem.loadInt_sep _ _ 8 _ _ h_mem1 h_lt2 (by decide)
  have h_mem2 := Mem.storeInt_sep
    (rsp.toBitVec - 1024 + BitVec.ofNat 64 (16 + 8 * (r9.toNat + r15.toNat))) 8
    _ _ _ ⟨h_mem1, h_lt2⟩ 42
  have h_L3 := Mem.loadInt_sep _ _ 8 _ _ h_mem2 (Int.toBytes_length 8 _) (by decide)
  -- fact for instruction 9: load 99 back from rsp - 8
  replace h_mem2 : (Eq ((Int.toBytes 8 99).At (rsp.toBitVec - 8#64)) ⋆
      (Eq ((Int.toBytes 8 42).At
          (rsp.toBitVec - 1024 + BitVec.ofNat 64 (16 + 8 * (r9.toNat + r15.toNat)))) ⋆
        Eq ((List.take (16 + 8 * (r9.toNat + r15.toNat)) (List.take 1016 stack)).At (rsp.toBitVec - 1024)) ⋆
        Eq ((List.drop 8 (List.drop (16 + 8 * (r9.toNat + r15.toNat)) (List.take 1016 stack))).At
          (rsp.toBitVec - 1024 + BitVec.ofNat 64 (16 + 8 * (r9.toNat + r15.toNat)) + 8#64)) ⋆
        R))
      (Mem.storeInt (Mem.storeInt mem (rsp.toBitVec - 8#64) 8 99)
        (rsp.toBitVec - 1024 + BitVec.ofNat 64 (16 + 8 * (r9.toNat + r15.toNat))) 8 42) :=
    cast (congrFun (by ac_rfl) _) h_mem2
  have h_L4 := Mem.loadInt_sep _ _ 8 _ _ h_mem2 (Int.toBytes_length 8 _) (by decide)
  simp only [BitVec.ofNat_eq_ofNat] at h_L1 h_L2 h_L3 h_L4
  -- bridge the interpreter's address normal forms to the fact addresses
  have hA3 : rsp.toBitVec + 18446744073709551608#64 = rsp.toBitVec - 8#64 := by bv_decide
  have hAD : BitVec.ofInt 64 ((rsp.toBitVec.toInt + r9.toBitVec.toInt * 8 + -1024).bmod 18446744073709551616)
        + r15.toBitVec * 8#64 + 16#64
      = rsp.toBitVec - 1024 + BitVec.ofNat 64 (16 + 8 * (r9.toNat + r15.toNat)) := by
    rw [show ((rsp.toBitVec.toInt + r9.toBitVec.toInt * 8 + -1024).bmod 18446744073709551616)
          = (BitVec.ofInt 64 (rsp.toBitVec.toInt + r9.toBitVec.toInt * 8 + -1024)).toInt
        from (BitVec.toInt_ofInt (n := 64) _).symm,
      BitVec.ofInt_toInt]
    simp only [Nat.mul_add, ← Nat.add_assoc, BitVec.ofNat_add, BitVec.ofNat_mul,
      BitVec.ofNat_uInt64ToNat, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
      BitVec.ofInt_neg, BitVec.ofInt_ofNat]
    grind
  delta sdyn
  dsimp only [straightlineStep, Executable.straightline]
  rw [Executable.directivesFromStart']
  simp [List.mapIdx, List.mapIdx.go]
  apply Effects.all_of_triple
  sym =>
    vcgen -internalize [Directives.interp, Directive.interp, Instr.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, MachineData.set]
    all_goals tactic =>
      first
      | (simp [MachineData.setReg, Reg64s.set, Reg64s.set64, Reg64s.get, Reg64s.get64,
          Reg.base, Reg.offset, ConstExpr.interp, AddrExpr.interp, BitVec.toAddressSize,
          BitVec.signed, BitVec.take, BitVec.drop, Width.bits,
          Int64.toBitVec_ofNat, UInt64.ofBitVec_ofNat, UInt64.toBitVec_sub, UInt64.toBitVec_ofNat,
          UInt64.ofBitVec_add, UInt64.ofBitVec_sub, UInt64.ofBitVec_toBitVec,
          BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
          hA3, hAD, h_L1, h_L2, h_L3, h_L4] <;> rfl)
      | (simp [MachineData.setReg, Reg64s.set, Reg64s.set64, Reg64s.get, Reg64s.get64,
          Reg.base, Reg.offset, ConstExpr.interp, AddrExpr.interp, BitVec.toAddressSize,
          BitVec.signed, BitVec.take, BitVec.drop, Width.bits,
          Int64.toBitVec_ofNat, UInt64.ofBitVec_ofNat, UInt64.toBitVec_sub, UInt64.toBitVec_ofNat,
          UInt64.ofBitVec_add, UInt64.ofBitVec_sub, UInt64.ofBitVec_toBitVec,
          BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
          hA3, hAD, h_L1, h_L2, h_L3, h_L4];
         apply Eventually.done;
         simp [MachineData.setReg, Reg64s.set, Reg64s.set64, Reg64s.get, Reg64s.get64,
           Reg.base, Reg.offset, ConstExpr.interp, BitVec.take, BitVec.drop, Width.bits,
           Int64.toBitVec_ofNat, UInt64.ofBitVec_ofNat, UInt64.toBitVec_ofNat,
           UInt64.ofBitVec_add, UInt64.ofBitVec_sub, UInt64.ofBitVec_toBitVec];
         and_intros <;> first
           | exact (by decide : UInt64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 42))) = 42)
           | exact (by decide : UInt64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 99))) = 99)
           | rfl)
