module

/-
The control-flow rule of the state wp. A program with labels is a list of
basic blocks (`Program.blockAt`). `StateWP.cfg` proves the baseline judgment
of the laid-out program from one triple per block: a table `T` gives the
assertion at each label, and a variant `var` orders the jumps. A block falls
into the next block, and a jump reaches the cell of its label. A call links to
its return through a `Contract` that the callee implements.
-/
public import Kraken.StateWP
public import Kraken.SegmentExtract

@[expose] public section

open Std.WP
open Lean.Order

/-! ## The text of a block -/

/-- The text from a block's label: the label cell, the block's body, and the
text from the label the block falls into. -/
theorem Program.fromLabel_block {p : Program} (hnd : (Program.labels p).Nodup)
    {l : Label} {blk : Program.Block} (h : Program.blockAt p l = some blk) :
    Program.fromLabel p l
      = Directive.label l :: (blk.body ++ blk.next.elim [] (Program.fromLabel p)) := by
  obtain ⟨-, i, hi, hnext⟩ := Program.blockAtAux_spec h
  rw [Program.fromLabel_view hnd hi, Program.drop_flatMap_cons hi]
  congr 2
  cases hj : (Program.view p).2[i + 1]? with
  | none =>
    rw [hj] at hnext
    rw [hnext, List.drop_eq_nil_of_le (List.getElem?_eq_none_iff.mp hj)]
    rfl
  | some lb =>
    obtain ⟨l', b'⟩ := lb
    rw [hj] at hnext
    rw [hnext]
    exact (Program.fromLabel_view hnd hj).symm

/-- The text from a label is a suffix of the program. -/
theorem Program.drop_fromLabel (p : Program) (l : Label) :
    p.drop (p.length - (Program.fromLabel p l).length) = Program.fromLabel p l := by
  obtain ⟨t, ht⟩ := Program.fromLabel_suffix p l
  have hlen := congrArg List.length ht
  rw [List.length_append] at hlen
  rw [show p.length - (Program.fromLabel p l).length = t.length by omega]
  calc p.drop t.length = (t ++ Program.fromLabel p l).drop t.length := by rw [ht]
    _ = Program.fromLabel p l := List.drop_left

/-! ## Calls -/

def MachineData.pushRa (s : MachineData) (ra : Int64) : MachineData :=
  { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp - 8#64),
           dmem := Mem.storeInt s.dmem (s.regs.get64 .rsp - 8#64) 8 ra.toBitVec.toInt }

@[grind =] theorem MachineData.regs_pushRa (s : MachineData) (ra : Int64) :
    (s.pushRa ra).regs = s.regs.set64 .rsp (s.regs.get64 .rsp - 8#64) := rfl

@[grind =] theorem MachineData.dmem_pushRa (s : MachineData) (ra : Int64) :
    (s.pushRa ra).dmem = Mem.storeInt s.dmem (s.regs.get64 .rsp - 8#64) 8 ra.toBitVec.toInt := rfl

@[grind =] theorem Mem.loadInt_storeInt_64 (m : DataMem) (a : BitVec 64) (v : Int) :
    (m.storeInt a 8 v).loadInt a 8 = some (Int.ofBytes (Int.toBytes 8 v)) :=
  Mem.loadInt_storeInt m a _ v (by decide)

@[grind =] theorem Int64.ofBitVec_ofBytes_toBytes (ra : Int64) :
    Int64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 ra.toBitVec.toInt))) = ra := by
  rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]

@[grind =] theorem MachineData.retAddr_pushRa (s : MachineData) (ra : Int64) :
    (s.pushRa ra).retAddr = some ra := by
  simp only [MachineData.retAddr, MachineData.pushRa, Reg64s.get64_set64, reduceIte,
    Mem.loadInt_storeInt _ _ _ _ (by decide : 8 ≤ 2 ^ 64), Option.map_some,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]

structure Contract where
  f : Label
  Pre : MachineData → Prop
  Post : MachineData → MachineData → Prop

/-- The code at `c.f`, entered with a return address `ra` on the stack, returns to `ra`. -/
def Contract.Implemented [Host] (c : Contract) : Prop :=
  ∀ s ra, c.Pre s →
    Eventually Host.step (fun st => st.2 = ra ∧ c.Post s st.1) (s.pushRa ra, label c.f)

namespace StateWP

variable [layout : Layout] [host : Host] {Q : Unit → MachineData → Prop}
  {E : Int64 → MachineData → Prop}

@[spec] theorem call_spec (asz osz : Width) (c : Contract) :
    ⦃ fun s => c.Implemented
        ⊓ ((Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome = true)
        ⊓ c.Pre s ⊓ (∀ s', c.Post s s' → Q () s') ⦄
      Directive.instr (.regular asz osz (.call (.rel (.sub (.label c.f) .after_current_instruction))))
    ⦃ Q; E ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  simp only [meet_prop_eq_and] at hpre
  obtain ⟨⟨⟨himpl, hmapped⟩, hpre⟩, hcont⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  intro k hs
  obtain ⟨z, hz⟩ := Host.cell_of_prefix hs.1
  refine Eventually.step _ (fun st => st = (s.pushRa (Host.exe.addrOf (k + 1)), label c.f))
    ⟨k, _, z, hz, rfl, fun R next jmp _ hj => ?_⟩ ?_
  · simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
      ConstExpr.interp, MachineData.store, hload, Effects.All]
    rw [Int64.ofBitVec_toBitVec, Int64.add_sub_self_left]
    exact hj _ _ rfl
  · rintro _ rfl
    refine eventually_trans _ _ _ _ (himpl s _ hpre) ?_
    rintro ⟨s'', a⟩ ⟨ha, hpost⟩
    exact Eventually.done _ (Or.inl ⟨ha, hcont s'' hpost⟩)

theorem implemented_of_triple {P body rest : Program} {k : Nat} (hP : P.LinkedAt k)
    (c : Contract) (hat : Program.fromLabel P c.f = Directive.label c.f :: (body ++ rest))
    (hbody : ∀ s ra, ⦃ fun t => t = s.pushRa ra ∧ c.Pre s ⦄ body
      ⦃ (fun _ _ => False); fun a s' => a = ra ∧ c.Post s s' ⦄) :
    c.Implemented := by
  intro s ra hpre
  have hl := Program.drop_fromLabel P c.f ▸ hP.drop (P.length - (Program.fromLabel P c.f).length)
  generalize k + (P.length - (Program.fromLabel P c.f).length) = i at hl
  rw [hat] at hl
  obtain ⟨hlab, hrest⟩ := Program.LinkedAt.append (a := [Directive.label c.f]) hl
  obtain ⟨hbody', -⟩ := Program.LinkedAt.append hrest
  obtain ⟨z, hz⟩ := Host.cell_of_prefix hlab.1
  rw [hlab.2 0 c.f rfl, Nat.add_zero]
  refine Eventually.step _ (fun st => st = (s.pushRa ra, Host.exe.addrOf (i + 1)))
    ⟨i, _, z, hz, rfl, fun R next jmp hn _ => by simp only [Directive.interp]; exact hn _ rfl⟩ ?_
  rintro _ rfl
  refine eventually_trans _ _ _ _ ((hbody s ra).1 _ ⟨rfl, hpre⟩ (i + 1) hbody') ?_
  rintro _ (⟨_, h⟩ | ⟨rfl, hpost⟩)
  · exact h.elim
  · exact Eventually.done _ ⟨rfl, hpost⟩

/-! ## The control-flow rule -/

omit host in
/-- The control-flow rule: one table `T`, one variant `var`, one triple per block of
`Program.blockAt`. Each block is entered with its table entry and the variant snapshotted as
`n`. It falls into the next block with the entry there and the variant not increased, or, as the
last block, falls through the end of the program with `post`. A jump exits at the address of a
mapped label along `Program.EdgeLt`. -/
theorem cfg {p p' : Program} {l₀ : Label} {post : MachineState → Prop}
    [Kraken.Executable.ValidLayout (layout p)]
    (T : Label → MachineData → Prop) (var : Label → MachineData → Nat := fun _ _ => 0)
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ n : Nat, ∀ [Host], p.LinkedAt 0 →
      ⦃ fun s => T l s ∧ var l s = n ⦄
        blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T l' s ∧ var l' s ≤ n
         | none => fun _ s => ∀ pc, post (s, pc));
        fun a s => ∃ l', label l' = a
          ∧ (Program.blockAt p l').isSome ∧ T l' s ∧ Program.EdgeLt p var l n l' s ⦄)
    (hp : p = Directive.label l₀ :: p' := by rfl) (hwf : Program.WF p := by decide) :
    ∀ s, T l₀ s → Eventually (straightlineStep (layout p)) post (s, layout.start) := by
  letI : Host := ⟨layout p⟩
  have hnd := hwf.nodup
  have hlink : p.LinkedAt 0 := Program.linkedAt_layout hnd
  have hplen : (layout p).2.length = p.length := by simp [Layout.apply_snd]
  let Fin := fun st : MachineState => st.2 = (layout p).addrOf (layout p).2.length
    ∧ ∀ pc, post (st.1, pc)
  have hK : ∀ l, Program.blockIdx p l ≤ (Program.view p).2.length := Program.blockIdx_le p
  have hcellOf : ∀ l, Program.fromLabel p l ≠ [] →
      p[p.length - (Program.fromLabel p l).length]? = some (Directive.label l) := by
    intro l hne
    have hdrop := Program.drop_fromLabel p l
    obtain ⟨t, rest, -, hfl, -, -⟩ := Program.fromLabel_split hnd hne
    conv at hdrop => rhs; rw [hfl]
    simpa [List.head?_drop] using congrArg List.head? hdrop
  have key : ∀ x : Label × MachineData, (Program.blockAt p x.1).isSome → T x.1 x.2 →
      Eventually Host.step Fin
        (x.2, (layout p).addrOf (p.length - (Program.fromLabel p x.1).length)) := by
    intro x
    induction x using (measure (Program.cfgMeasure p var)).wf.induction with
    | _ x ih =>
      obtain ⟨l, s⟩ := x
      intro hsome hT
      dsimp only at hsome hT ⊢
      obtain ⟨blk, hblk⟩ := Option.isSome_iff_exists.mp hsome
      have htext := Program.fromLabel_block hnd hblk
      have hlen := congrArg List.length htext
      simp only [List.length_cons, List.length_append] at hlen
      have hdrop := Program.drop_fromLabel p l
      have hsuf : (Program.fromLabel p l).length ≤ p.length := by
        have := congrArg List.length hdrop
        simp only [List.length_drop] at this
        omega
      have hl := hdrop ▸ hlink.drop (p.length - (Program.fromLabel p l).length)
      generalize hi : p.length - (Program.fromLabel p l).length = i at hdrop hl
      rw [Nat.zero_add, htext] at hl
      obtain ⟨hlab, hrest⟩ := Program.LinkedAt.append (a := [Directive.label l]) hl
      obtain ⟨hbody, -⟩ := Program.LinkedAt.append hrest
      obtain ⟨z, hz⟩ := Host.cell_of_prefix hlab.1
      refine Eventually.step _ (fun st => st = (s, (layout p).addrOf (i + 1)))
        ⟨i, _, z, hz, rfl, fun R next jmp hn _ => by simp only [Directive.interp]; exact hn _ rfl⟩ ?_
      rintro _ rfl
      refine eventually_trans _ _ _ _ ((hblocks l blk hblk (var l s) hlink).1 s ⟨hT, rfl⟩
        (i + 1) hbody) ?_
      rintro ⟨s', a⟩ (⟨hend, hq⟩ | hE)
      · dsimp only at hend hq
        subst hend
        cases hn : blk.next with
        | none =>
          rw [hn] at hq hlen
          refine Eventually.done _ ⟨?_, hq⟩
          show (layout p).addrOf (i + 1 + blk.body.length) = _
          simp only [Option.elim, List.length_nil] at hlen
          rw [hplen]
          congr 1
          omega
        | some l' =>
          rw [hn] at hq hlen
          obtain ⟨hT', hvar⟩ := hq
          obtain ⟨hsome', hidx'⟩ := Program.blockAt_next hnd hblk hn
          simp only [Option.elim] at hlen
          rw [show i + 1 + blk.body.length = p.length - (Program.fromLabel p l').length by omega]
          refine ih (l', s') ?_ hsome' hT'
          have hK' := hK l'
          show Program.cfgMeasure p var (l', s') < Program.cfgMeasure p var (l, s)
          unfold Program.cfgMeasure
          dsimp only
          have hmul : var l' s' * ((Program.view p).2.length + 1)
              ≤ var l s * ((Program.view p).2.length + 1) :=
            Nat.mul_le_mul_right _ hvar
          omega
      · obtain ⟨l', hlab', hsome', hT', hedge⟩ := hE
        dsimp only at hlab'
        subst hlab'
        have hne : Program.fromLabel p l' ≠ [] := by
          obtain ⟨blk', hblk'⟩ := Option.isSome_iff_exists.mp hsome'
          rw [Program.fromLabel_block hnd hblk']
          exact List.cons_ne_nil _ _
        rw [hlink.2 _ l' (hcellOf l' hne), Nat.zero_add]
        refine ih (l', s') ?_ hsome' hT'
        have hK' := hK l'
        show Program.cfgMeasure p var (l', s') < Program.cfgMeasure p var (l, s)
        unfold Program.cfgMeasure
        dsimp only
        rcases hedge with hlt | ⟨heq, hij⟩
        · have hmul : (var l' s' + 1) * ((Program.view p).2.length + 1)
              ≤ var l s * ((Program.view p).2.length + 1) :=
            Nat.mul_le_mul_right _ hlt
          have hsucc : (var l' s' + 1) * ((Program.view p).2.length + 1)
              = var l' s' * ((Program.view p).2.length + 1)
                + ((Program.view p).2.length + 1) := Nat.succ_mul _ _
          omega
        · rw [heq]
          omega
  intro s hT
  have h0 : (Program.blockAt p l₀).isSome := by
    rw [hp]
    show (Program.blockAtAux (Program.view (Directive.label l₀ :: p')).2 l₀).isSome = true
    simp [Program.view, Program.blockAtAux]
  have hfl : Program.fromLabel p l₀ = p := by
    have hnot : Program.fromLabel p' l₀ = [] := Classical.byContradiction fun hne => by
      have hmem := Program.mem_labels_of_cell (Program.fromLabel_mem hne)
      have hnd' := hnd
      rw [hp] at hnd'
      simp only [Program.labels] at hnd'
      exact (List.nodup_cons.mp hnd').1 hmem
    rw [hp]
    simp [hnot]
  have := key (l₀, s) h0 hT
  rw [hfl, Nat.sub_self] at this
  have := Host.eventually_straightlineStep (e := layout p) (post := post)
    (fun st hst => hst) this
  rwa [Kraken.Executable.addrOf_zero, Layout.apply_fst] at this

end StateWP
