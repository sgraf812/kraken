module

/-
The control-flow rule of the state wp. A program with labels is a list of
basic blocks (`Program.blockAt`). `StateWP.cfg` proves the baseline judgment
of the laid-out program from one triple per block: a table `T` gives the
assertion at each label, and a variant `var` orders the jumps. A block falls
into the next block inside one burst, and a jump starts a new burst at the
target's address. `Program.LabelsPlaced` is what the rule needs of the layout: the
address of a label looks up to the text from that label on.
`Program.placed_of_valid` derives it from `ValidLayout`.
-/
public import Kraken.StateWP
public import Kraken.MachineWP

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

theorem Layout.frag_map_fst [Layout] (n : Nat) (p : Program) :
    (Layout.frag n p).map (·.1) = p :=
  List.ext_getElem (by simp) (by simp [Layout.frag])

/-! ## Placement -/

/-- A jump to a label of the laid-out program `p` lands on the text from that
label: the address of the label looks up to label cells of size zero,
followed by the laid-out text from the label on. -/
def Program.LabelsPlaced [layout : Layout] (p : Program) : Prop :=
  ∀ l, (Program.blockAt p l).isSome →
    ∃ pre, (layout p).directivesFromAddress ((Executable.labels (layout p)).label l)
        = pre ++ Layout.frag (p.length - (Program.fromLabel p l).length) (Program.fromLabel p l)
      ∧ ∀ c ∈ pre, c.1.isLabel = true ∧ c.2 = 0

/-- A valid layout places every label. -/
theorem Program.placed_of_valid [layout : Layout] {p : Program}
    [hv : Kraken.Executable.ValidLayout (layout p)] (hwf : Program.WF p) :
    Program.LabelsPlaced p := by
  intro l hl
  have hne : Program.fromLabel p l ≠ [] := by
    obtain ⟨blk, hblk⟩ := Option.isSome_iff_exists.mp hl
    rw [Program.fromLabel_block hwf.nodup hblk]
    exact List.cons_ne_nil _ _
  have hlen : (layout p).2.length = p.length := by simp [Layout.apply_snd]
  rw [Program.label_addrOf_drop hwf.nodup (Program.drop_fromLabel p l) hne]
  generalize hi : p.length - (Program.fromLabel p l).length = i
  have hile : i ≤ p.length := by omega
  obtain ⟨j, hji, hj, hleast⟩ := Nat.exists_least_le
    (P := fun j => (layout p).addrOf j = (layout p).addrOf i) rfl
  have hfresh : ∀ k, k < j → (layout p).addrOf k ≠ (layout p).addrOf i := hleast
  rw [Kraken.Executable.directivesFromAddress_addrOf_first (layout p) j i hji (by omega) hj hfresh]
  refine ⟨((layout p).2.drop j).take (i - j), ?_, ?_⟩
  · have hd : p.drop i = Program.fromLabel p l := hi ▸ Program.drop_fromLabel p l
    conv => lhs; rw [← List.take_append_drop (i - j) ((layout p).2.drop j)]
    rw [List.drop_drop, show j + (i - j) = i by omega, Layout.apply_snd, Layout.frag_drop 0 i,
      Nat.zero_add, hd]
  · intro c hc
    obtain ⟨k, hk, hck⟩ := List.getElem_of_mem hc
    simp only [List.length_take, List.length_drop] at hk
    have hkc : (layout p).2[j + k]? = some c := by
      rw [← hck, List.getElem?_eq_getElem (by omega)]
      simp [List.getElem_take, List.getElem_drop]
    obtain ⟨l', z, hlz⟩ := Kraken.Executable.label_between_of_addrOf_eq (layout p)
      (k := j + k) (by omega) (by omega) (by omega) hj
    rw [hkc] at hlz
    cases hlz
    exact ⟨rfl, hv.label_size (j + k) l' z hkc⟩

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

/-! ## The control-flow rule -/

/-- One burst of the laid-out code, from a state and address. -/
theorem straightlineStep_eq_interp [Layout] (e : Executable) (st : MachineState)
    (post : MachineState → Prop) :
    straightlineStep e st post
      = (@Directives.interp (Executable.labels e) (e.directivesFromAddress st.2) st.1 st.2
          fun pc s => .done (s, pc)).All post := by
  unfold straightlineStep Executable.straightline
  rfl

/-- The laid-out text of `p` from the label `l` on. -/
def Program.codeFrom [Layout] (p : Program) (l : Label) : List (Directive × Nat) :=
  Layout.frag (p.length - (Program.fromLabel p l).length) (Program.fromLabel p l)

namespace StateWP

/-- The control-flow rule: one table `T`, one variant `var`, one triple per
block of `Program.blockAt`, under every label table. Each block is
entered with its table entry and the variant snapshotted as `n`. It falls into
the next block with the entry there and the variant not increased, or, as
the last block, falls through the end of the program with `post`. A jump exits
at the address of a mapped label along `Program.EdgeLt`. -/
theorem cfg [layout : Layout] {p p' : Program} {l₀ : Label} {post : MachineState → Prop}
    (T : Label → MachineData → Prop) (var : Label → MachineData → Nat := fun _ _ => 0)
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ n : Nat, ∀ [Labels],
      ⦃ fun s => T l s ∧ var l s = n ⦄
        blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T l' s ∧ var l' s ≤ n
         | none => fun _ s => ∀ pc, post (s, pc));
        fun a s => ∃ l', label l' = a
          ∧ (Program.blockAt p l').isSome ∧ T l' s ∧ Program.EdgeLt p var l n l' s ⦄)
    (hplace : Program.LabelsPlaced p)
    (hp : p = Directive.label l₀ :: p' := by rfl) (hwf : Program.WF p := by decide) :
    ∀ s, T l₀ s → Eventually (straightlineStep (layout p)) post (s, layout.start) := by
  letI : Labels := Executable.labels (layout p)
  have hnd := hwf.nodup
  have hK : ∀ l, Program.blockIdx p l ≤ (Program.view p).2.length := Program.blockIdx_le p
  have key : ∀ x : Label × MachineData, (Program.blockAt p x.1).isSome → T x.1 x.2 →
      ∀ pc, (Directives.interp (Program.codeFrom p x.1) x.2 pc fun pc s => .done (s, pc)).All
        (Eventually (straightlineStep (layout p)) post) := by
    intro x
    induction x using (measure (Program.cfgMeasure p var)).wf.induction with
    | _ x ih =>
      obtain ⟨l, s⟩ := x
      intro hsome hT pc
      dsimp only at hsome hT ⊢
      obtain ⟨blk, hblk⟩ := Option.isSome_iff_exists.mp hsome
      have hidx : Program.blockIdx p l < (Program.view p).2.length :=
        Program.blockIdx_lt hnd hblk
      have htext := Program.fromLabel_block hnd hblk
      have hlen := congrArg List.length htext
      simp only [List.length_cons, List.length_append] at hlen
      have hsuf : (Program.fromLabel p l).length ≤ p.length := by
        have := congrArg List.length (Program.drop_fromLabel p l)
        simp only [List.length_drop] at this
        omega
      have hcode : Program.codeFrom p l
          = (Directive.label l, layout.size (p.length - (Program.fromLabel p l).length))
            :: (Layout.frag (p.length - (Program.fromLabel p l).length + 1) blk.body
              ++ Layout.frag (p.length - (Program.fromLabel p l).length + 1 + blk.body.length)
                (blk.next.elim [] (Program.fromLabel p))) := by
        rw [Program.codeFrom, htext, Layout.frag_cons, Layout.frag_append]
      rw [hcode]
      simp only [Directives.interp, Directive.interp]
      have hrun := (@hblocks l blk hblk (var l s) (Executable.labels (layout p))).1 s ⟨hT, rfl⟩
      refine hrun _ _ _ _ (Layout.frag_map_fst _ _) (fun s' hq => ?_) (fun a s' hE => ?_)
      · cases hn : blk.next with
        | none =>
          rw [hn] at hq
          simp only [Option.elim_none, Layout.frag_nil, Directives.interp]
          exact Eventually.done _ (hq _)
        | some l' =>
          rw [hn] at hq hlen
          obtain ⟨hT', hvar⟩ := hq
          obtain ⟨hsome', hidx'⟩ := Program.blockAt_next hnd hblk hn
          simp only [Option.elim] at hlen ⊢
          have hcode' : Layout.frag (p.length - (Program.fromLabel p l).length + 1 + blk.body.length)
              (Program.fromLabel p l') = Program.codeFrom p l' := by
            rw [Program.codeFrom]
            congr 1
            omega
          rw [hcode']
          refine ih (l', s') ?_ hsome' hT' _
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
        refine Eventually.step _ _ ?_ fun _ h => h
        obtain ⟨pre, hdir, hpre⟩ := hplace l' hsome'
        rw [straightlineStep_eq_interp]
        dsimp only
        rw [hdir, Directives.interp_labels_append hpre, ← Program.codeFrom]
        refine ih (l', s') ?_ hsome' hT' _
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
  refine Eventually.step _ _ ?_ fun _ h => h
  rw [straightlineStep_eq_interp]
  dsimp only
  have hstart : (layout p).directivesFromAddress layout.start = Program.codeFrom p l₀ := by
    rw [Kraken.Executable.directivesFromStart, Program.codeFrom]
    have hfl : Program.fromLabel p l₀ = p := by
      have hnot : Program.fromLabel p' l₀ = [] := Classical.byContradiction fun hne => by
        have hmem := Program.mem_labels_of_cell (Program.fromLabel_mem hne)
        have hnd' := hnd
        rw [hp] at hnd'
        simp only [Program.labels] at hnd'
        exact (List.nodup_cons.mp hnd').1 hmem
      rw [hp]
      simp [hnot]
    rw [hfl, Nat.sub_self]
    simp [Layout.frag]
  rw [hstart]
  exact key (l₀, s) h0 hT _

end StateWP
