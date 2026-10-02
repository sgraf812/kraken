module

/-
The control-flow rule of the state wp. A program with labels is a list of
basic blocks (`Program.blockAt`). `StateWP.cfg` proves the baseline judgment
of the laid-out program from one triple per block: a table `T` gives the
assertion at each label, and a variant `var` orders the jumps. A block falls
into the next block inside one burst, and a jump starts a new burst at the
target's address. `Host.Placed` is what the rule needs of the layout: the
address of an index looks up to the text from that index on.
`Host.placed_of_valid` derives it from `ValidLayout`. A call links to its return
through `Host.Placed` and a `Contract` that the callee implements.
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

/-! ## Placement -/

/-- Entering the host at the address of index `k` runs the host from index `k`. -/
def Host.Placed [Host] : Prop :=
  ∀ k s Φ, k ≤ Host.exe.2.length → Host.burst k s Φ →
    (Executable.straightline Host.exe (s, Host.exe.addrOf k) .done).All Φ

/-- Label cells of size zero cost the burst nothing. -/
theorem Directives.interp_labels_append [Labels] {pre rest : List (Directive × Nat)}
    (hpre : ∀ c ∈ pre, c.1.isLabel = true ∧ c.2 = 0) (s : MachineData) (pc : Int64)
    (ret : Int64 → MachineData → Effects) :
    Directives.interp (pre ++ rest) s pc ret = Directives.interp rest s pc ret := by
  induction pre with
  | nil => rfl
  | cons c pre ih =>
    obtain ⟨hlab, hz⟩ := hpre c List.mem_cons_self
    obtain ⟨d, z⟩ := c
    cases d with
    | label l =>
      dsimp only at hz
      subst hz
      have h0 : pc + Int64.ofNat 0 = pc := by simp
      simp only [List.cons_append, Directives.interp, Directive.interp, h0]
      exact ih (fun c hc => hpre c (List.mem_cons_of_mem _ hc))
    | instr _ => cases hlab
    | byteArray _ => cases hlab

theorem Host.placed_of_valid [Host] [hv : Kraken.Executable.ValidLayout Host.exe] : Host.Placed := by
  intro k s Φ hk h
  obtain ⟨j, hjk, hdir, hlab⟩ := Kraken.Executable.exists_cut Host.exe hk
  have hsplit : Host.exe.2.drop j = (Host.exe.2.drop j).take (k - j) ++ Host.exe.2.drop k := by
    conv => lhs; rw [← List.take_append_drop (k - j) (Host.exe.2.drop j)]
    rw [List.drop_drop, show j + (k - j) = k by omega]
  show (Directives.interp (Host.exe.directivesFromAddress (Host.exe.addrOf k)) s
    (Host.exe.addrOf k) fun pc s => .done (s, pc)).All Φ
  rw [hdir, hsplit, Directives.interp_labels_append]
  · exact h
  · intro c hc
    obtain ⟨m, hm, hcm⟩ := List.getElem_of_mem hc
    simp only [List.length_take, List.length_drop] at hm
    have hmc : Host.exe.2[j + m]? = some c := by
      rw [← hcm, List.getElem?_eq_getElem (by omega)]
      simp [List.getElem_take, List.getElem_drop]
    obtain ⟨l, z, hlz⟩ := hlab (j + m) (by omega) (by omega)
    rw [hmc] at hlz
    cases hlz
    exact ⟨rfl, hv.label_size (j + m) l z hmc⟩

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
def Contract.Implemented [Layout] [Host] (c : Contract) : Prop :=
  ∀ s ra, c.Pre s →
    Eventually (straightlineStep Host.exe) (fun st => st.2 = ra ∧ c.Post s st.1)
      (s.pushRa ra, label c.f)

theorem Int64.add_sub_self_left (a b : Int64) : a + (b - a) = b := by
  apply Int64.toBitVec_inj.mp
  simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
  rw [BitVec.add_comm, BitVec.sub_add_cancel]

namespace StateWP

variable [layout : Layout] [host : Host] {Q : Unit → MachineData → Prop}
  {E : Int64 → MachineData → Prop}

@[spec] theorem call_spec (asz osz : Width) (c : Contract) :
    ⦃ fun s => (Host.Placed ∧ c.Implemented)
        ⊓ ((Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome = true)
        ⊓ c.Pre s ⊓ (∀ s', c.Post s s' → Q () s') ⦄
      Directive.instr (.regular asz osz (.call (.rel (.sub (.label c.f) .after_current_instruction))))
    ⦃ Q; E ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  simp only [meet_prop_eq_and] at hpre
  obtain ⟨⟨⟨⟨hplaced, himpl⟩, hmapped⟩, hpre⟩, hcont⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  intro ds rest pc Φ hds hg hQ _
  obtain ⟨⟨_, z⟩, rfl, rfl⟩ := List.map_eq_singleton_iff.mp hds
  obtain ⟨k, hdrop, hpc, hclosed⟩ := hg
  have hcell := congrArg List.head? hdrop
  simp only [List.head?_drop, List.cons_append, List.nil_append, List.head?_cons] at hcell
  have hk : k + 1 ≤ Host.exe.2.length := (List.getElem?_eq_some_iff.mp hcell).1
  have hrest : Host.exe.2.drop (k + 1) = rest := by
    rw [← List.drop_drop, hdrop]
    rfl
  have hra : Host.exe.addrOf (k + 1) = pc + .ofNat z := by
    rw [Kraken.Executable.addrOf_succ _ hcell, hpc]
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, MachineData.store, hload, Effects.All, List.cons_append,
    List.nil_append, Directives.interp]
  rw [Int64.ofBitVec_toBitVec, Int64.add_sub_self_left]
  refine closed_of_eventually ?_ hclosed (himpl s _ hpre)
  rintro ⟨s'', a⟩ ⟨rfl, hpost⟩
  refine hclosed _ ?_
  rw [← hra]
  refine hplaced (k + 1) s'' Φ hk ?_
  unfold Host.burst
  rw [hrest, hra]
  exact hQ s'' (hcont s'' hpost)

theorem implemented_of_triple {P body rest : Program} [Kraken.Executable.ValidLayout Host.exe]
    (hhost : Host.exe = layout P) (hnd : (Program.labels P).Nodup) (c : Contract)
    (hat : Program.fromLabel P c.f = Directive.label c.f :: (body ++ rest))
    (hbody : ∀ s ra, ⦃ fun t => t = s.pushRa ra ∧ c.Pre s ⦄ body
      ⦃ (fun _ _ => False); fun a s' => a = ra ∧ c.Post s s' ⦄) :
    c.Implemented := by
  have hplaced : Host.Placed := Host.placed_of_valid
  obtain ⟨e⟩ := host
  change e = _ at hhost
  subst hhost
  letI : Host := ⟨layout P⟩
  intro s ra hpre
  have hdrop := Program.drop_fromLabel P c.f
  rw [show label c.f = (layout P).addrOf (P.length - (Program.fromLabel P c.f).length) from
    Program.label_addrOf_drop hnd hdrop (by rw [hat]; exact List.cons_ne_nil _ _)]
  have hle : P.length - (Program.fromLabel P c.f).length ≤ (layout P).2.length := by
    simp [Layout.apply_snd]
  generalize P.length - (Program.fromLabel P c.f).length = i at hdrop hle
  rw [hat] at hdrop
  have hcell : P[i]? = some (Directive.label c.f) := by
    simpa [List.head?_drop] using congrArg List.head? hdrop
  have hcell' : (layout P).2[i]? = some (Directive.label c.f, Kraken.Layout.size Directive i) := by
    rw [Layout.apply_getElem?, hcell]; rfl
  refine Eventually.step _ _ (hplaced i _ _ hle ?_) fun _ h => h
  rw [Host.burst_label hcell']
  refine Program.run_at ((hbody s ra).1 _ ⟨rfl, hpre⟩) ?_ (eventually_closed _ _)
    (fun _ h => h.elim) ?_
  · show body <+: ((layout P).2.map (·.1)).drop (i + 1)
    rw [Layout.text, ← List.drop_drop, hdrop]
    exact List.prefix_append _ _
  · rintro a s' ⟨rfl, hpost⟩
    exact Eventually.done _ ⟨rfl, hpost⟩

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
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ n : Nat, ∀ [Host],
      Host.exe = layout p →
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
  have hplaced : Host.Placed := Host.placed_of_valid
  have hnd := hwf.nodup
  have hK : ∀ l, Program.blockIdx p l ≤ (Program.view p).2.length := Program.blockIdx_le p
  have key : ∀ x : Label × MachineData, (Program.blockAt p x.1).isSome → T x.1 x.2 →
      Host.burst (p.length - (Program.fromLabel p x.1).length) x.2
        (Eventually (straightlineStep (layout p)) post) := by
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
      generalize hi : p.length - (Program.fromLabel p l).length = i at hdrop
      rw [htext] at hdrop
      have hcell : p[i]? = some (Directive.label l) := by
        simpa [List.head?_drop] using congrArg List.head? hdrop
      have hcell' : (layout p).2[i]? = some (Directive.label l, Kraken.Layout.size Directive i) := by
        rw [Layout.apply_getElem?, hcell]; rfl
      have hbody : blk.body <+: ((layout p).2.map (·.1)).drop (i + 1) := by
        rw [Layout.text, ← List.drop_drop, hdrop]
        exact List.prefix_append _ _
      rw [Host.burst_label hcell']
      refine Program.run_at ((hblocks l blk hblk (var l s) rfl).1 s ⟨hT, rfl⟩) hbody
        (eventually_closed _ _) (fun s' hq => ?_) (fun a s' hE => ?_)
      · cases hn : blk.next with
        | none =>
          rw [hn] at hq hlen
          refine Host.burst_end ?_ fun pc => Eventually.done _ (hq pc)
          show (layout p).2.length ≤ _
          simp only [Option.elim, List.length_nil] at hlen
          simp only [Layout.apply_snd, Layout.frag, List.length_mapIdx]
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
      · obtain ⟨l', hlab, hsome', hT', hedge⟩ := hE
        subst hlab
        have hne : Program.fromLabel p l' ≠ [] := by
          obtain ⟨blk', hblk'⟩ := Option.isSome_iff_exists.mp hsome'
          rw [Program.fromLabel_block hnd hblk']
          exact List.cons_ne_nil _ _
        rw [show label l' = (layout p).addrOf (p.length - (Program.fromLabel p l').length) from
          Program.label_addrOf_drop hnd (Program.drop_fromLabel p l') hne]
        refine eventually_closed _ _ _ (hplaced _ _ _ (by show _ ≤ (layout p).2.length; simp only [Layout.apply_snd, Layout.frag, List.length_mapIdx]; omega)
          (ih (l', s') ?_ hsome' hT'))
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
  exact eventually_of_burst this

end StateWP
