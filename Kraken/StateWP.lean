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
wp of a laid-out program back as the `straightlineStep` judgment.
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
scoped instance instWP [Labels] : WP Program Unit (MachineData → Prop) (Int64 → MachineData → Prop) where
  trans q := ⟨fun Q E s => Program.run q (Q ()) E s⟩
  trans_monotone _ := fun _ _ _ _ hE hQ _ h => Program.run_mono (hQ ()) hE h

theorem wp_apply_iff [Labels] (q : Program) (Q : Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) :
    WP.wp q Q E s ↔ Program.run q (Q ()) E s := Iff.rfl

/-- Triples of one directive: the interpretation of the singleton program. -/
scoped instance [Labels] : WP Directive Unit (MachineData → Prop) (Int64 → MachineData → Prop) where
  trans d := WP.trans (self := instWP) [d]
  trans_monotone d := WP.trans_monotone (self := instWP) [d]

theorem triple_directive [Labels] {d : Directive} {P : MachineData → Prop}
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} :
    (⦃ P ⦄ d ⦃ Q; E ⦄) ↔ (⦃ P ⦄ [d] ⦃ Q; E ⦄) :=
  ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩

variable [Labels] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

/-- The empty program: its wp is the postcondition. -/
@[spec] theorem nil_spec : ⦃ fun s => Q () s ⦄ ([] : Program) ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  intro ds rest pc Φ hds hQ _
  obtain rfl := List.map_eq_nil_iff.mp hds
  exact hQ s hpre

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
  intro ds rest pc Φ hds hQ _
  obtain ⟨⟨_, z⟩, rfl, rfl⟩ := List.map_eq_singleton_iff.mp hds
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    MachineData.set, MachineData.setReg, Reg64s.set_low_W64, Effects.All, List.cons_append,
    List.nil_append, Directives.interp]
  exact hQ _ hpre

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
  intro ds rest pc Φ hds hQ _
  obtain ⟨⟨_, z⟩, rfl, rfl⟩ := List.map_eq_singleton_iff.mp hds
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store, Reg64s.get_low_W64,
    AddrExpr.zeroExtend_interp_base_disp, hload, Effects.All, List.cons_append, List.nil_append,
    Directives.interp]
  exact hQ _ hpre

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
  intro ds rest pc Φ hds hQ _
  obtain ⟨⟨_, z⟩, rfl, rfl⟩ := List.map_eq_singleton_iff.mp hds
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.get_low_W64, Reg64s.set_low_W64, AddrExpr.zeroExtend_interp_base_disp,
    hload, Effects.All, List.cons_append, List.nil_append, Directives.interp]
  exact hQ _ (hpre i hload)

end StateWP

/-! ## Reading the wp back as the baseline judgment

The wp of a program with no exits is a run of the laid-out program: if the wp
holds of `s` for the postcondition that asks `post` of the final state at
every pc, the run from `s` at the layout's start ends in `post`. The
hypothesis is the entailment `⊤ ⊑ wp …` at `s`, the goal form of `vcgen`,
under every label table: the program does not jump, so its run is the same
for every table. -/

open StateWP in
theorem straightlineStep_of_wp [layout : Layout] {p : Program} {s : MachineData}
    {post : MachineState → Prop}
    (h : ∀ [Labels], ⊤ ⊑ WP.wp p (fun _ s' => ∀ pc, post (s', pc)) ⊥ s) :
    straightlineStep (layout p) (s, layout.start) post :=
  Program.run_straightlineStep (of_top_le_prop (@h (Executable.labels (layout p))))
    (fun st' hq => hq st'.2)
    (fun a s' hE => ((bot_le (α := Int64 → MachineData → Prop) fun _ _ => False) a s' hE).elim)

open StateWP in
/-- `straightlineStep_of_wp` for a burst that ends the run. -/
theorem eventually_straightlineStep_of_wp [layout : Layout] {p : Program} {s : MachineData}
    {post : MachineState → Prop}
    (h : ∀ [Labels], ⊤ ⊑ WP.wp p (fun _ s' => ∀ pc, post (s', pc)) ⊥ s) :
    Eventually (straightlineStep (layout p)) post (s, layout.start) :=
  .step _ _ (straightlineStep_of_wp h) fun _ h => .done _ h
