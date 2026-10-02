module

/-
The weakest precondition over whole machine states. An assertion is a
predicate on `MachineData`, data memory included, and `Int64 →` that for the
exit channel. `StateWP.instWP` interprets a `Program` by its run
`Program.run`: `wp p Q E s` holds when every burst that runs `p` from `s`
falls through with `Q ()` or exits with `E`. The instance is scoped, so a file
opts in with `open scoped StateWP`.

The specs below carry the schematic post to the state the instruction
leaves. A memory access asks for the slot to be mapped. `vcgen` sequences
them by `StateWP.cons_spec`, and `eventually_straightlineStep_of_wp` reads the
wp of a laid-out program back as the `Eventually` judgment.
-/
public import Kraken.ProgramRun
public import Kraken.X64.Registers
public import Kraken.KVCGen
public import Std.WP
public import Std.Tactic.Do

@[expose] public section

open Std.WP
open Lean.Order

namespace StateWP

/-- Programs interpreted by their run, at predicates over machine states. -/
scoped instance instWP [LinkedProgram] : WP Program Unit (MachineData → Prop) (Int64 → MachineData → Prop) where
  trans q := ⟨fun Q E s => Program.run q (Q ()) E s⟩
  trans_monotone _ := fun _ _ _ _ hE hQ _ h => Program.run_mono (hQ ()) hE h

theorem wp_apply_iff [LinkedProgram] (q : Program) (Q : Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) :
    WP.wp q Q E s ↔ Program.run q (Q ()) E s := Iff.rfl

/-- Triples of one directive: the interpretation of the singleton program. -/
scoped instance [LinkedProgram] : WP Directive Unit (MachineData → Prop) (Int64 → MachineData → Prop) where
  trans d := WP.trans (self := instWP) [d]
  trans_monotone d := WP.trans_monotone (self := instWP) [d]

theorem triple_directive [LinkedProgram] {d : Directive} {P : MachineData → Prop}
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} :
    (⦃ P ⦄ d ⦃ Q; E ⦄) ↔ (⦃ P ⦄ [d] ⦃ Q; E ⦄) :=
  ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩

variable [LinkedProgram] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

/-- The empty program: its wp is the postcondition. -/
@[spec] theorem nil_spec : ⦃ fun s => Q () s ⦄ ([] : Program) ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  intro k _
  exact Eventually.done _ (Or.inl ⟨rfl, hpre⟩)

/-- Chaining: a program runs its first directive with the wp of the rest as
the post. -/
@[spec] theorem cons_spec (d : Directive) (p : Program) :
    ⦃ WP.wp d (fun _ => WP.wp p Q E) E ⦄ (d :: p) ⦃ Q; E ⦄ :=
  ⟨fun _ h => Program.run_cons h⟩

/-- Load an immediate into a 64-bit register. -/
@[spec] theorem mov_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 r (BitVec.setWidth 64 i.toBitVec) } ⦄
      Directive.instr (.regular asz .W64 (.mov (.reg (.low r .W64)) (.imm (.int64 i))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  intro k hs
  obtain ⟨z, hz⟩ := LinkedProgram.cell_of_prefix hs.1
  refine LinkedProgram.eventually_cell hz fun R next jmp hQ _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    MachineData.set, MachineData.setReg, Reg64s.set_low_W64, Effects.All]
  exact hQ _ (Or.inl ⟨rfl, hpre⟩)

/-- Store a 64-bit register at `disp(base)`, a mapped slot. -/
@[spec] theorem mov_store_reg_spec (b : Reg64) (d : Int64) (rs : Reg64) :
    ⦃ fun s => ((Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8).isSome = true)
        ⊓ Q () { s with
            dmem := Mem.storeInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8
              (s.regs.get64 rs).toInt } ⦄
      Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩)
            (.regOrMem (.reg (.low rs .W64)))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := (meet_prop_eq_and _ _) ▸ hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  intro k hs
  obtain ⟨z, hz⟩ := LinkedProgram.cell_of_prefix hs.1
  refine LinkedProgram.eventually_cell hz fun R next jmp hQ _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store, Reg64s.get_low_W64,
    AddrExpr.zeroExtend_interp_base_disp, hload, Effects.All]
  exact hQ _ (Or.inl ⟨rfl, hpre⟩)

/-- Add the 64-bit word at `disp(base)`, a mapped slot, to a register. -/
@[spec] theorem add_reg_mem_spec (rd b : Reg64) (d : Int64) :
    ⦃ fun s => ((Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8).isSome = true)
        ⊓ ∀ i, Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8 = some i →
          let a := BitVec.ofInt 64 i
          let bv := s.regs.get64 rd
          let v := a + bv
          Q () { s with
            regs := s.regs.set64 rd v
            status := StatusFlags.from_result v
              { cf := v.unsigned != a.unsigned + bv.unsigned,
                af := (v.take 4).unsigned != (a.take 4).unsigned + (bv.take 4).unsigned,
                of := v.signed != a.signed + bv.signed } } ⦄
      Directive.instr (.regular .W64 .W64
          (.add (.reg (.low rd .W64))
            (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := (meet_prop_eq_and _ _) ▸ hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  intro k hs
  obtain ⟨z, hz⟩ := LinkedProgram.cell_of_prefix hs.1
  refine LinkedProgram.eventually_cell hz fun R next jmp hQ _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.get_low_W64, Reg64s.set_low_W64, AddrExpr.zeroExtend_interp_base_disp,
    hload, Effects.All]
  exact hQ _ (Or.inl ⟨rfl, (hpre i hload)⟩)

/-! ## Control flow and the instructions of the loop examples -/

/-- The simp set that reduces one directive of a burst. -/
local macro "run_step" : tactic =>
  `(tactic| simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
      RegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp, MachineData.set, MachineData.setReg,
      Reg64s.get_low_W64, Reg64s.set_low_W64, Effects.All])

/-- A label occupies no step of the machine. -/
@[spec] theorem label_spec (l : Label) : ⦃ fun s => Q () s ⦄ Directive.label l ⦃ Q ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  intro k hs
  obtain ⟨z, hz⟩ := LinkedProgram.cell_of_prefix hs.1
  refine LinkedProgram.eventually_cell hz fun R next jmp hQ _ => ?_
  run_step
  exact hQ _ (Or.inl ⟨rfl, hpre⟩)

/-- A no-op. -/
@[spec] theorem nop_spec (asz osz : Width) (n : Nat) :
    ⦃ fun s => Q () s ⦄ Directive.instr (.regular asz osz (.nop n)) ⦃ Q ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  intro k hs
  obtain ⟨z, hz⟩ := LinkedProgram.cell_of_prefix hs.1
  refine LinkedProgram.eventually_cell hz fun R next jmp hQ _ => ?_
  run_step
  exact hQ _ (Or.inl ⟨rfl, hpre⟩)

/-- Subtract an immediate from a 64-bit register. -/
@[spec] theorem sub_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let b := s.regs.get64 r
        let a := BitVec.setWidth 64 i.toBitVec
        let v := b - a
        Q () { s with
          regs := s.regs.set64 r v
          status := StatusFlags.from_result v
            { cf := v.unsigned != b.unsigned - a.unsigned,
              af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
              of := v.signed != b.signed - a.signed } } ⦄
      Directive.instr (.regular asz .W64 (.sub (.reg (.low r .W64)) (.imm (.int64 i))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  intro k hs
  obtain ⟨z, hz⟩ := LinkedProgram.cell_of_prefix hs.1
  refine LinkedProgram.eventually_cell hz fun R next jmp hQ _ => ?_
  run_step
  exact hQ _ (Or.inl ⟨rfl, hpre⟩)

/-- The unsigned product of a register and `rdx`, split into two registers. -/
@[spec] theorem mulx_reg_spec (asz : Width) (hi lo rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rs).unsigned * (s.regs.get64 .rdx).unsigned
        Q () { s with regs :=
          (s.regs.set64 lo (BitVec.ofInt 64 v)).set64 hi (BitVec.ofInt 64 (v >>> 64)) } ⦄
      Directive.instr (.regular asz .W64
          (.mulx (.low hi .W64) (.low lo .W64) (.reg (.low rs .W64))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  intro k hs
  obtain ⟨z, hz⟩ := LinkedProgram.cell_of_prefix hs.1
  refine LinkedProgram.eventually_cell hz fun R next jmp hQ _ => ?_
  run_step
  exact hQ _ (Or.inl ⟨rfl, hpre⟩)

/-- Add an immediate to a 64-bit register. -/
@[spec] theorem add_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := BitVec.setWidth 64 i.toBitVec
        let b := s.regs.get64 r
        let v := a + b
        Q () { s with
          regs := s.regs.set64 r v
          status := StatusFlags.from_result v
            { cf := v.unsigned != a.unsigned + b.unsigned,
              af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
              of := v.signed != a.signed + b.signed } } ⦄
      Directive.instr (.regular asz .W64 (.add (.reg (.low r .W64)) (.imm (.int64 i))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  intro k hs
  obtain ⟨z, hz⟩ := LinkedProgram.cell_of_prefix hs.1
  refine LinkedProgram.eventually_cell hz fun R next jmp hQ _ => ?_
  run_step
  exact hQ _ (Or.inl ⟨rfl, hpre⟩)

/-- Add a 64-bit register and the carry flag to a register. -/
@[spec] theorem adc_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 rs
        let b := s.regs.get64 rd
        let c := s.status.cf
        let v := a + b + BitVec.ofNat 64 c.toNat
        Q () { s with
          regs := s.regs.set64 rd v
          status := StatusFlags.from_result v
            { cf := v.unsigned != a.unsigned + b.unsigned + c,
              af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned + c,
              of := v.signed != a.signed + b.signed + c } } ⦄
      Directive.instr (.regular asz .W64
          (.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  intro k hs
  obtain ⟨z, hz⟩ := LinkedProgram.cell_of_prefix hs.1
  refine LinkedProgram.eventually_cell hz fun R next jmp hQ _ => ?_
  run_step
  exact hQ _ (Or.inl ⟨rfl, hpre⟩)

/-- Exclusive-or of two 64-bit registers. The adjust flag is unspecified, so
the post must hold for either value. -/
@[spec] theorem xor_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let v := s.regs.get64 rd ^^^ s.regs.get64 rs
        ∀ af : Bool, Q () { s with
          regs := s.regs.set64 rd v
          status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      Directive.instr (.regular asz .W64
          (.xor (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  intro k hs
  obtain ⟨z, hz⟩ := LinkedProgram.cell_of_prefix hs.1
  refine LinkedProgram.eventually_cell hz fun R next jmp hQ _ => ?_
  run_step
  intro af
  exact hQ _ (Or.inl ⟨rfl, (hpre af)⟩)

/-- Decrement a 64-bit register. The carry flag is kept. -/
@[spec] theorem dec_reg_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 r
        let v := a - 1
        Q () { s with
          regs := s.regs.set64 r v
          status := StatusFlags.from_result v
            { cf := s.status.cf,
              af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
              of := v.signed != a.signed - 1 } } ⦄
      Directive.instr (.regular asz .W64 (.dec (.reg (.low r .W64))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  intro k hs
  obtain ⟨z, hz⟩ := LinkedProgram.cell_of_prefix hs.1
  refine LinkedProgram.eventually_cell hz fun R next jmp hQ _ => ?_
  run_step
  exact hQ _ (Or.inl ⟨rfl, hpre⟩)

theorem _root_.Int64.add_sub_self_left (a b : Int64) : a + (b - a) = b := by
  apply Int64.toBitVec_inj.mp
  simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
  rw [BitVec.add_comm, BitVec.sub_add_cancel]

/-- A jump to a label exits at the label's address. -/
@[spec] theorem jmp_label_spec (asz osz : Width) (l : Label) :
    ⦃ fun s => E (label l) s ⦄
      Directive.instr (.regular asz osz (.jmp (.rel (.sub (.label l) .after_current_instruction))))
    ⦃ Q; E ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  intro k hs
  obtain ⟨z, hz⟩ := LinkedProgram.cell_of_prefix hs.1
  refine LinkedProgram.eventually_cell hz fun R next jmp _ hE => ?_
  run_step
  rw [Int64.ofBitVec_toBitVec, Int64.add_sub_self_left]
  exact hE _ _ (Or.inr hpre)

/-- A conditional jump to a label: it exits at the label's address when the
condition holds and falls through otherwise. -/
@[spec] theorem jcc_spec (asz osz : Width) (cc : CondCode) (l : Label) :
    ⦃ fun s => (cc.interp s.status = true → E (label l) s) ⊓ (cc.interp s.status = false → Q () s) ⦄
      Directive.instr (.regular asz osz (.jcc cc l))
    ⦃ Q; E ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  obtain ⟨hjmp, hfall⟩ := (meet_prop_eq_and _ _) ▸ hpre
  intro k hs
  obtain ⟨z, hz⟩ := LinkedProgram.cell_of_prefix hs.1
  refine LinkedProgram.eventually_cell hz fun R next jmp hQ hE => ?_
  run_step
  cases hc : CondCode.interp cc s.status <;>
    simp only [hc, Bool.false_eq_true, ite_true, ite_false]
  · exact hQ _ (Or.inl ⟨rfl, (hfall hc)⟩)
  · exact hE _ _ (Or.inr (hjmp hc))

/-- The return address on top of the stack. -/
def _root_.MachineData.retAddr (t : MachineData) : Option Int64 :=
  (Mem.loadInt t.dmem (t.regs.get64 .rsp) 8).map (fun i => Int64.ofBitVec (BitVec.ofInt 64 i))

@[grind =] theorem _root_.MachineData.retAddr_eq (t : MachineData) :
    t.retAddr = (Mem.loadInt t.dmem (t.regs.get64 .rsp) 8).map
      (fun i => Int64.ofBitVec (BitVec.ofInt 64 i)) := rfl

@[spec] theorem ret_spec (asz osz : Width) :
    ⦃ fun s => (s.retAddr.isSome = true)
        ⊓ (∀ ra, s.retAddr = some ra →
            E ra { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64) }) ⦄
      Directive.instr (.regular asz osz .ret)
    ⦃ Q; E ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hexit⟩ := (meet_prop_eq_and _ _) ▸ hpre
  obtain ⟨ra, hra⟩ := Option.isSome_iff_exists.mp hmapped
  obtain ⟨i, hi, hval⟩ : ∃ i, Mem.loadInt s.dmem (s.regs.get64 .rsp) 8 = some i
      ∧ Int64.ofBitVec (BitVec.ofInt 64 i) = ra := by
    unfold MachineData.retAddr at hra
    cases hl : Mem.loadInt s.dmem (s.regs.get64 .rsp) 8 with
    | none => rw [hl] at hra; exact absurd hra (by simp)
    | some i => exact ⟨i, rfl, by rw [hl] at hra; simpa using hra⟩
  intro k hs
  obtain ⟨z, hz⟩ := LinkedProgram.cell_of_prefix hs.1
  refine LinkedProgram.eventually_cell hz fun R next jmp _ hE => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.load, hi,
    Effects.All, hval]
  exact hE _ _ (Or.inr (hexit ra hra))

end StateWP

/-! ## Reading the wp back as the baseline judgment

The wp of a program with no exits is a run of the laid-out program: if the wp
holds of `s` for the postcondition that asks `post` of the final state at
every pc, the run from `s` at the layout's start eventually ends in `post`.
The hypothesis is the entailment `⊤ ⊑ wp …` at `s`, the goal form of `vcgen`,
in every linked program. The laid-out program is a valid executable. -/

open StateWP in
theorem eventually_straightlineStep_of_wp [layout : Layout] {p : Program}
    [Kraken.Executable.ValidExecutable (layout p)] {s : MachineData} {post : MachineState → Prop}
    (h : ∀ [LinkedProgram], ⊤ ⊑ WP.wp p (fun _ s' => ∀ pc, post (s', pc)) ⊥ s) :
    Eventually (straightlineStep (layout p)) post (s, layout.start) :=
  Program.run_eventually (Q := fun s' => ∀ pc, post (s', pc))
    (E := (⊥ : Int64 → MachineData → Prop)) (of_top_le_prop (@h ⟨layout p⟩)) (fun _ hq => hq)
    (fun a s' hE => (bot_le (α := Int64 → MachineData → Prop) fun _ _ => False) a s' hE)
