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

@[spec] theorem MachineData.loadAvx_spec (s : MachineData) (addr : BitVec 64) (w : AvxWidth)
    (ret : w.type → MachineData → Effects) (i : Int)
    (h : Mem.loadInt s.dmem addr w.bytes = some i)
    (post : MachineState → Prop) (epost : EPost.Nil) :
    ⦃ wp (ret (.ofInt w.bits i) s) post epost ⦄ MachineData.loadAvx s addr w ret ⦃ post; epost ⦄ := by
  constructor
  intro hwp
  show (MachineData.loadAvx s addr w ret).All post
  simp only [MachineData.loadAvx, h]
  exact hwp

@[spec] theorem MachineData.storeAvx_spec (s : MachineData) (addr : BitVec 64) {w : AvxWidth}
    (v : w.type) (ret : MachineData → Effects) (i : Int)
    (h : Mem.loadInt s.dmem addr w.bytes = some i)
    (post : MachineState → Prop) (epost : EPost.Nil) :
    ⦃ wp (ret { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }) post epost ⦄
      MachineData.storeAvx s addr v ret ⦃ post; epost ⦄ := by
  constructor
  intro hwp
  show (MachineData.storeAvx s addr v ret).All post
  simp only [MachineData.storeAvx, h]
  exact hwp

/-! ## The kraken Sym.simp set

Equations of the pure interpreter functions and the `UInt64`/`BitVec` coercion
round-trips, so sym-mode `simp` normalizes register-file and address terms. -/

attribute [sym_simp] Reg64s.set
  Reg.base Reg.offset ConstExpr.interp
  AddrExpr.interp BitVec.toAddressSize BitVec.signed

@[sym_simp] theorem UInt64.ofNat_lit (n : Nat) : (OfNat.ofNat n : UInt64) = UInt64.ofNat n := rfl

attribute [sym_simp] UInt64.ofBitVec_sub UInt64.ofBitVec_add UInt64.ofBitVec_toBitVec
  UInt64.ofBitVec_ofNat UInt64.toBitVec_ofBitVec UInt64.toBitVec_sub UInt64.toBitVec_ofNat
  Int64.toBitVec_ofNat BitVec.ofInt_add BitVec.ofInt_mul BitVec.ofInt_toInt BitVec.setWidth_eq
  UInt64.sub_add_cancel

/-! ## Specs for the remaining effect nodes: straightline code performs no MMIO
and reaches no data blocks, so their weakest precondition is `False`. -/

@[spec] theorem Effects.unimplemented_spec (msg : String) (post : MachineState → Prop)
    (epost : EPost.Nil) :
    ⦃ (False : Prop) ⦄ Effects.unimplemented msg ⦃ post; epost ⦄ :=
  ⟨fun h => h.elim⟩

@[spec] theorem Effects.nonmem_load_spec (dmem : DataMem) (addr : BitVec 64) (w : Width)
    (ret : w.type → DataMem → Effects) (post : MachineState → Prop) (epost : EPost.Nil) :
    ⦃ (False : Prop) ⦄ Effects.nonmem_load dmem addr w ret ⦃ post; epost ⦄ :=
  ⟨fun h => h.elim⟩

@[spec] theorem Effects.nonmem_store_spec (dmem : DataMem) (addr : BitVec 64) {w : Width}
    (v : w.type) (ret : DataMem → Effects) (post : MachineState → Prop) (epost : EPost.Nil) :
    ⦃ (False : Prop) ⦄ Effects.nonmem_store dmem addr v ret ⦃ post; epost ⦄ :=
  ⟨fun h => h.elim⟩

/-! ## Spec generation for the CPS interpreter

Each equation `f args = rhs` of an `Effects`-returning interpreter function
yields the spec `⦃ wp rhs post epost ⦄ f args ⦃ post; epost ⦄`; the proof is
definitional since the equations are iota reductions. -/

open Lean Meta Elab Term Command in
elab "gen_cps_specs " fs:ident+ : command => do
  for f in fs do
    let fname ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo f
    let some eqns ← liftTermElabM <| getEqnsFor? fname
      | throwError "no equation theorems for {fname}"
    let mut i := 0
    for eqn in eqns do
      i := i + 1
      let thmName := fname ++ Name.mkSimple s!"cps_spec_{i}"
      liftTermElabM do
        let info ← getConstInfo eqn
        let (thmType, thmValue) ← forallTelescope info.type fun xs eqTy => do
          let some (_, lhs, rhs) := eqTy.eq? | throwError "not an equation: {eqTy}"
          withLocalDeclD `post (← mkArrow (mkConst ``MachineState) (mkSort .zero)) fun post =>
          withLocalDeclD `epost (mkConst ``Std.Internal.Do.EPost.Nil) fun epost => do
            let pre ← mkAppM ``Std.Internal.Do.WP.wp #[rhs, post, epost]
            let triple ← mkAppM ``Std.Internal.Do.Triple #[lhs, pre, post, epost]
            let eqPrf := mkAppN (mkConst eqn (info.levelParams.map .param)) xs
            let lewp ← mkAppM ``Std.Internal.Do.wp_le_wp_of_eq #[eqPrf, post, epost]
            let prf ← mkAppM ``Std.Internal.Do.Triple.intro #[lewp]
            return (← mkForallFVars (xs ++ #[post, epost]) triple,
                    ← mkLambdaFVars (xs ++ #[post, epost]) prf)
        addDecl <| .thmDecl {
          name := thmName, levelParams := info.levelParams, type := thmType, value := thmValue }
        Term.applyAttributes thmName #[{ name := `spec, stx := ← `(attr| spec), kind := .global }]

gen_cps_specs Directives.interp Directive.interp Instr.interp Operation.interp
  AvxOperation.interp Operand.interp AvxOperand.interp RegOrMem.interp AvxRegOrMem.interp
  RelRegOrMem.interp Reg.interp MachineData.set MachineData.setAvx MachineData.setAvxLegacy


/-! ## Read-over-write API: characterize register reads by rewriting, so
discharging queries only the registers the postcondition mentions and the
state chain is never unfolded into record literals. -/

@[sym_simp, simp, grind =] theorem Reg64s.get64_set64 (s : Reg64s) (r r' : Reg64) (v : Width.W64.type) :
    (s.set64 r v).get64 r' = if r' = r then v else s.get64 r' := by
  cases r <;> cases r' <;> simp [Reg64s.set64, Reg64s.get64]

@[sym_simp, simp, grind =] theorem Reg64s.get_low64 (s : Reg64s) (r : Reg64) :
    s.get (.low r .W64) = s.get64 r := by
  simp [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop]

@[sym_simp, simp, grind =] theorem Reg64s.rax_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).rax = if r = .rax then .ofBitVec v else s.rax := by
  cases r <;> simp [Reg64s.set64]

@[sym_simp, simp, grind =] theorem MachineData.regs_setReg (s : MachineData) {w} (r : Reg w) (v : w.type) :
    (s.setReg r v).regs = s.regs.set r v := rfl

@[sym_simp, simp] theorem MachineData.regs_mk (r z st d) : (MachineData.mk r z st d).regs = r := rfl
@[sym_simp, simp] theorem MachineData.dmem_mk (r z st d) : (MachineData.mk r z st d).dmem = d := rfl
@[sym_simp, simp] theorem MachineData.status_mk (r z st d) : (MachineData.mk r z st d).status = st := rfl
@[sym_simp, simp] theorem MachineData.zmms_mk (r z st d) : (MachineData.mk r z st d).zmms = z := rfl

/-! ## Grind theory for interpreter values

Characterization lemmas for the value-level interpreter functions and the
integer coercion round-trips, in E-matchable form. A `UInt64` literal is
normalized to `UInt64.ofBitVec` of a `BitVec` literal, so register-value goals
reduce through constructor injectivity to the `BitVec` `grind` ring. With these,
`finish` discharges VCs without per-call-site lemma lists. -/

section
variable (labels : Labels) (p : Std.Rco Int64)

@[grind =] theorem ConstExpr.interp_label (l : Label) :
    ConstExpr.interp labels (.label l) p = labels.label l := rfl
@[grind =] theorem ConstExpr.interp_int64 (i : Int64) :
    ConstExpr.interp labels (.int64 i) p = i := rfl
@[grind =] theorem ConstExpr.interp_before :
    ConstExpr.interp labels .before_current_instruction p = p.lower := rfl
@[grind =] theorem ConstExpr.interp_after :
    ConstExpr.interp labels .after_current_instruction p = p.upper := rfl
@[grind =] theorem ConstExpr.interp_add (e1 e2 : ConstExpr) :
    ConstExpr.interp labels (.add e1 e2) p
      = ConstExpr.interp labels e1 p + ConstExpr.interp labels e2 p := rfl
@[grind =] theorem ConstExpr.interp_sub (e1 e2 : ConstExpr) :
    ConstExpr.interp labels (.sub e1 e2) p
      = ConstExpr.interp labels e1 p - ConstExpr.interp labels e2 p := rfl

end

@[grind =] theorem Reg64s.set_low64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    Reg64s.set s (.low r .W64) v = s.set64 r v := rfl

@[grind =] theorem Int64.ofNat_lit (n : Nat) : (OfNat.ofNat n : Int64) = Int64.ofNat n := rfl
@[grind =] theorem Int64.toBitVec_ofNat_lit (n : Nat) :
    (Int64.ofNat n).toBitVec = BitVec.ofNat 64 n := rfl
@[grind =] theorem Int64.toBitVec_lit (n : Nat) :
    (OfNat.ofNat n : Int64).toBitVec = BitVec.ofNat 64 n := rfl
theorem UInt64.ofNat_lit' (n : Nat) :
    (OfNat.ofNat n : UInt64) = UInt64.ofBitVec (BitVec.ofNat 64 n) := rfl
@[grind =] theorem BitVec.setWidth_64_64 (x : BitVec 64) :
    BitVec.setWidth 64 x = x := BitVec.setWidth_eq x

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
    vcgen -internalize
    all_goals (simp; cbv; tactic => rfl)

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
    vcgen -internalize
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
    vcgen -internalize
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

/-! ## Field reads over set64, one lemma per register field -/

@[sym_simp, simp, grind =] theorem Reg64s.rbx_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).rbx = if r = .rbx then .ofBitVec v else s.rbx := by
  cases r <;> simp [Reg64s.set64]

@[sym_simp, simp, grind =] theorem Reg64s.rcx_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).rcx = if r = .rcx then .ofBitVec v else s.rcx := by
  cases r <;> simp [Reg64s.set64]

@[sym_simp, simp, grind =] theorem Reg64s.rdx_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).rdx = if r = .rdx then .ofBitVec v else s.rdx := by
  cases r <;> simp [Reg64s.set64]

@[sym_simp, simp, grind =] theorem Reg64s.rsi_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).rsi = if r = .rsi then .ofBitVec v else s.rsi := by
  cases r <;> simp [Reg64s.set64]

@[sym_simp, simp, grind =] theorem Reg64s.rdi_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).rdi = if r = .rdi then .ofBitVec v else s.rdi := by
  cases r <;> simp [Reg64s.set64]

@[sym_simp, simp, grind =] theorem Reg64s.rsp_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).rsp = if r = .rsp then .ofBitVec v else s.rsp := by
  cases r <;> simp [Reg64s.set64]

@[sym_simp, simp, grind =] theorem Reg64s.rbp_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).rbp = if r = .rbp then .ofBitVec v else s.rbp := by
  cases r <;> simp [Reg64s.set64]

@[sym_simp, simp, grind =] theorem Reg64s.r8_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).r8 = if r = .r8 then .ofBitVec v else s.r8 := by
  cases r <;> simp [Reg64s.set64]

@[sym_simp, simp, grind =] theorem Reg64s.r9_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).r9 = if r = .r9 then .ofBitVec v else s.r9 := by
  cases r <;> simp [Reg64s.set64]

@[sym_simp, simp, grind =] theorem Reg64s.r10_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).r10 = if r = .r10 then .ofBitVec v else s.r10 := by
  cases r <;> simp [Reg64s.set64]

@[sym_simp, simp, grind =] theorem Reg64s.r11_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).r11 = if r = .r11 then .ofBitVec v else s.r11 := by
  cases r <;> simp [Reg64s.set64]

@[sym_simp, simp, grind =] theorem Reg64s.r12_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).r12 = if r = .r12 then .ofBitVec v else s.r12 := by
  cases r <;> simp [Reg64s.set64]

@[sym_simp, simp, grind =] theorem Reg64s.r13_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).r13 = if r = .r13 then .ofBitVec v else s.r13 := by
  cases r <;> simp [Reg64s.set64]

@[sym_simp, simp, grind =] theorem Reg64s.r14_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).r14 = if r = .r14 then .ofBitVec v else s.r14 := by
  cases r <;> simp [Reg64s.set64]

@[sym_simp, simp, grind =] theorem Reg64s.r15_set64 (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).r15 = if r = .r15 then .ofBitVec v else s.r15 := by
  cases r <;> simp [Reg64s.set64]
