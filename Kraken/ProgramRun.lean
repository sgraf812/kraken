module

/-
The run of a program fragment inside the linked program that contains it.
`Program.run p Q E s` says: started at the first cell of `p` in state `s`, the linked program
eventually reaches the end of `p` with `Q`, or an exit `a` with `E a`. The weakest preconditions of
Kraken/StateWP.lean and Kraken/SepWP.lean interpret a `Program` by this run.
-/
public import Kraken.SegmentExtract

@[expose] public section

/-- The linked program that contains the fragment under verification. -/
class LinkedProgram where
  exe : Executable

instance [LinkedProgram] : Labels := Executable.labels LinkedProgram.exe

/-- One cell of the linked program, at its address: for every continuation of the cell, the cell leads to
the continuation of a state in `P`. -/
def LinkedProgram.step [LinkedProgram] (st : MachineState) (P : MachineState → Prop) : Prop :=
  ∃ j d z, LinkedProgram.exe.2[j]? = some (d, z) ∧ st.2 = LinkedProgram.exe.addrOf j ∧
    ∀ (R : MachineState → Prop) (next : MachineData → Effects)
      (jmp : Int64 → MachineData → Effects),
      (∀ s', P (s', LinkedProgram.exe.addrOf (j + 1)) → (next s').All R) →
      (∀ a s', P (s', a) → (jmp a s').All R) →
      (d.interp st.1 ⟨LinkedProgram.exe.addrOf j, LinkedProgram.exe.addrOf (j + 1)⟩ next jmp).All R

/-- `p` sits at cell `k` of the linked program, and every label of `p` resolves to its own cell. -/
def Program.LinkedAt [LinkedProgram] (p : Program) (k : Nat) : Prop :=
  p <+: (LinkedProgram.exe.2.map (·.1)).drop k ∧
  ∀ i l, p[i]? = some (Directive.label l) → label l = LinkedProgram.exe.addrOf (k + i)

def Program.run [LinkedProgram] (p : Program) (Q : MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) : Prop :=
  ∀ k, p.LinkedAt k →
    Eventually LinkedProgram.step
      (fun st => (st.2 = LinkedProgram.exe.addrOf (k + p.length) ∧ Q st.1) ∨ E st.2 st.1)
      (s, LinkedProgram.exe.addrOf k)

theorem Program.run_mono [LinkedProgram] {p : Program} {Q₁ Q₂ : MachineData → Prop}
    {E₁ E₂ : Int64 → MachineData → Prop} (hQ : ∀ s, Q₁ s → Q₂ s) (hE : ∀ a s, E₁ a s → E₂ a s)
    {s : MachineData} (h : Program.run p Q₁ E₁ s) : Program.run p Q₂ E₂ s :=
  fun k hk => eventually_trans _ _ _ _ (h k hk) fun _ hb => Eventually.done _ <|
    hb.imp (fun ⟨ha, hq⟩ => ⟨ha, hQ _ hq⟩) (hE _ _)

theorem List.cons_prefix_drop {α : Type} {d : α} {q L : List α} {k : Nat}
    (h : (d :: q) <+: L.drop k) : L[k]? = some d ∧ q <+: L.drop (k + 1) := by
  obtain ⟨t, ht⟩ := h
  have hk : L.drop k = d :: (q ++ t) := ht.symm
  refine ⟨?_, t, ?_⟩
  · simpa [List.head?_drop] using congrArg List.head? hk
  · rw [← List.drop_drop, hk]
    rfl

theorem Program.LinkedAt.append [LinkedProgram] {a b : Program} {k : Nat}
    (h : Program.LinkedAt (a ++ b) k) : a.LinkedAt k ∧ b.LinkedAt (k + a.length) := by
  obtain ⟨⟨t, ht⟩, hlab⟩ := h
  refine ⟨⟨⟨b ++ t, by rw [← ht, List.append_assoc]⟩, fun i l hi => hlab i l ?_⟩,
    ⟨⟨t, ?_⟩, fun i l hi => ?_⟩⟩
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1]
    exact hi
  · rw [← List.drop_drop, ← ht, List.append_assoc, List.drop_left]
  · rw [hlab (a.length + i) l (by rw [List.getElem?_append_right (by omega)]; simpa using hi),
      Nat.add_assoc]

theorem Program.LinkedAt.drop [LinkedProgram] {p : Program} {k : Nat} (h : p.LinkedAt k) (m : Nat) :
    Program.LinkedAt (p.drop m) (k + m) := by
  by_cases hm : m ≤ p.length
  · have h' := (Program.LinkedAt.append (a := p.take m) (b := p.drop m)
      (by rwa [List.take_append_drop])).2
    rwa [List.length_take_of_le hm] at h'
  · rw [List.drop_eq_nil_of_le (show p.length ≤ m by omega)]
    exact ⟨List.nil_prefix, fun _ _ h => by simp at h⟩

/-- The run of `d :: p` is the run of `d` with the run of `p` as its post. -/
theorem Program.run_cons [LinkedProgram] {d : Directive} {p : Program} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData}
    (h : Program.run [d] (fun s' => Program.run p Q E s') E s) : Program.run (d :: p) Q E s := by
  intro k hk
  obtain ⟨hd, hp⟩ := Program.LinkedAt.append (a := [d]) hk
  refine eventually_trans _ _ _ _ (h k hd) ?_
  rintro ⟨s', a⟩ (⟨ha, hrun⟩ | hE)
  · dsimp only at ha hrun
    subst ha
    refine eventually_trans _ _ _ _ (hrun (k + 1) hp) fun _ hb => Eventually.done _ ?_
    rcases hb with ⟨hend, hq⟩ | hE
    · exact Or.inl ⟨by rw [hend, List.length_cons]; congr 1; omega, hq⟩
    · exact Or.inr hE
  · exact Eventually.done _ (Or.inr hE)

/-! ## One cell -/

theorem LinkedProgram.cell_of_prefix [LinkedProgram] {d : Directive} {p : Program} {k : Nat}
    (h : (d :: p) <+: (LinkedProgram.exe.2.map (·.1)).drop k) : ∃ z, LinkedProgram.exe.2[k]? = some (d, z) := by
  have hd := (List.cons_prefix_drop h).1
  rw [List.getElem?_map] at hd
  cases hc : LinkedProgram.exe.2[k]? with
  | none => rw [hc] at hd; cases hd
  | some c =>
    rw [hc] at hd
    obtain ⟨d', z⟩ := c
    cases hd
    exact ⟨z, rfl⟩

/-- A cell whose every outcome lies in `B`. -/
theorem LinkedProgram.eventually_cell [LinkedProgram] {k : Nat} {d : Directive} {z : Nat}
    (hd : LinkedProgram.exe.2[k]? = some (d, z)) {B : MachineState → Prop} {s : MachineData}
    (h : ∀ (R : MachineState → Prop) (next : MachineData → Effects)
      (jmp : Int64 → MachineData → Effects),
      (∀ s', B (s', LinkedProgram.exe.addrOf (k + 1)) → (next s').All R) →
      (∀ a s', B (s', a) → (jmp a s').All R) →
      (d.interp s ⟨LinkedProgram.exe.addrOf k, LinkedProgram.exe.addrOf (k + 1)⟩ next jmp).All R) :
    Eventually LinkedProgram.step B (s, LinkedProgram.exe.addrOf k) :=
  Eventually.step _ _ ⟨k, d, z, hd, rfl, h⟩ fun _ h => Eventually.done _ h

/-! ## Reading a run back as the baseline judgment -/

theorem Layout.frag_map_fst [Layout] (n : Nat) (p : Program) :
    (Layout.frag n p).map (·.1) = p :=
  List.ext_getElem (by simp) (by simp [Layout.frag])

theorem Layout.text {layout : Layout} {p : Program} : (layout p).2.map (·.1) = p := by
  rw [Layout.apply_snd, Layout.frag_map_fst]

theorem straightlineStep_eq_interp [Layout] (e : Executable) (st : MachineState)
    (post : MachineState → Prop) :
    straightlineStep e st post
      = (@Directives.interp (Executable.labels e) (e.directivesFromAddress st.2) st.1 st.2
          fun pc s => .done (s, pc)).All post := by
  unfold straightlineStep Executable.straightline
  rfl

/-- Cells of no bytes that do nothing cost the burst nothing. -/
theorem Directives.interp_inert_append [Labels] {pre rest : List (Directive × Nat)}
    (hpre : ∀ c ∈ pre, c.2 = 0 ∧ c.1.Inert) (s : MachineData) (pc : Int64)
    (ret : Int64 → MachineData → Effects) :
    Directives.interp (pre ++ rest) s pc ret = Directives.interp rest s pc ret := by
  induction pre with
  | nil => rfl
  | cons c pre ih =>
    obtain ⟨hz, hinert⟩ := hpre c List.mem_cons_self
    obtain ⟨d, z⟩ := c
    dsimp only at hz hinert
    subst hz
    have h0 : pc + Int64.ofNat 0 = pc := by simp
    simp only [List.cons_append, Directives.interp, h0]
    rw [hinert]
    exact ih (fun c hc => hpre c (List.mem_cons_of_mem _ hc))

/-- The cells from `j` up to `j'` occupy no bytes and do nothing. -/
theorem Executable.inert_between (e : Executable) [hv : Kraken.Executable.ValidExecutable e]
    {j j' : Nat} (hjj : j ≤ j') (hj' : j' ≤ e.2.length)
    (hzero : ∀ m, j ≤ m → m < j' → ∃ d, e.2[m]? = some (d, 0)) :
    ∀ c ∈ (e.2.drop j).take (j' - j), c.2 = 0 ∧ c.1.Inert := by
  intro c hc
  obtain ⟨m, hm, hcm⟩ := List.getElem_of_mem hc
  simp only [List.length_take, List.length_drop] at hm
  have hmc : e.2[j + m]? = some c := by
    rw [← hcm, List.getElem?_eq_getElem (by omega)]
    simp [List.getElem_take, List.getElem_drop]
  obtain ⟨d, hd⟩ := hzero (j + m) (by omega) (by omega)
  rw [hmc] at hd
  cases hd
  exact ⟨rfl, hv.zero_inert _ _ hmc⟩

theorem Executable.drop_split (e : Executable) {j j' : Nat} (hjj : j ≤ j') :
    e.2.drop j = (e.2.drop j).take (j' - j) ++ e.2.drop j' := by
  conv => lhs; rw [← List.take_append_drop (j' - j) (e.2.drop j)]
  rw [List.drop_drop, show j + (j' - j) = j' by omega]

/-- Cell steps that end only at the end of the program make up bursts that end there. -/
theorem LinkedProgram.eventually_straightlineStep [Layout] {e : Executable}
    [hv : Kraken.Executable.ValidExecutable e] {B post : MachineState → Prop}
    (hB : ∀ st, B st → st.2 = e.addrOf e.2.length ∧ ∀ pc, post (st.1, pc))
    {st : MachineState} (h : @Eventually _ (@LinkedProgram.step ⟨e⟩) B st) :
    Eventually (straightlineStep e) post st := by
  letI : Labels := Executable.labels e
  let G := Eventually (straightlineStep e) post
  let Burst := fun (j : Nat) (s : MachineData) =>
    (Directives.interp (e.2.drop j) s (e.addrOf j) fun pc s => .done (s, pc)).All G
  have hsame : ∀ j j' s, j ≤ j' → j' ≤ e.2.length → e.addrOf j = e.addrOf j' →
      Burst j s = Burst j' s := by
    intro j j' s hjj hj' heq
    show (Directives.interp _ _ _ _).All G = (Directives.interp _ _ _ _).All G
    rw [Executable.drop_split e hjj, Directives.interp_inert_append
      (Executable.inert_between e hjj hj' fun m hjm hmj' =>
        Kraken.Executable.zero_between_of_addrOf_eq e hjm hmj' hj' heq), heq]
  have hplaced : ∀ j s, j ≤ e.2.length → Burst j s → G (s, e.addrOf j) := by
    intro j s hj hb
    refine Eventually.step _ _ ?_ fun _ h => h
    obtain ⟨j₀, hj₀, hdir, hzero⟩ := Kraken.Executable.exists_cut e hj
    rw [straightlineStep_eq_interp]
    dsimp only
    rw [hdir, Executable.drop_split e hj₀,
      Directives.interp_inert_append (Executable.inert_between e hj₀ hj hzero)]
    exact hb
  have key : ∀ st, @Eventually _ (@LinkedProgram.step ⟨e⟩) B st →
      G st ∧ ∀ j, j ≤ e.2.length → st.2 = e.addrOf j → Burst j st.1 := by
    intro st h
    induction h with
    | done st hb =>
      obtain ⟨s, a⟩ := st
      obtain ⟨hend, hpost⟩ := hB _ hb
      dsimp only at hend hpost
      refine ⟨Eventually.done _ (hpost a), fun j hj hja => ?_⟩
      dsimp only at hja
      show Burst j s
      rw [hsame j e.2.length s hj (Nat.le_refl _) (hja.symm.trans hend)]
      show (Directives.interp (e.2.drop e.2.length) _ _ _).All G
      rw [List.drop_length]
      exact Eventually.done _ (hpost _)
    | step st P hstep _ ih =>
      obtain ⟨j₀, d, z, hcell, hst, hall⟩ := hstep
      obtain ⟨s, a⟩ := st
      dsimp only at hst hall ⊢
      subst hst
      replace hcell : e.2[j₀]? = some (d, z) := hcell
      obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hcell
      have hb0 : Burst j₀ s := by
        show (Directives.interp (e.2.drop j₀) s (e.addrOf j₀) _).All G
        rw [List.drop_eq_getElem_cons hlt, hget]
        simp only [Directives.interp]
        rw [← Kraken.Executable.addrOf_succ _ hcell]
        exact hall G _ _ (fun s' hp => (ih _ hp).2 (j₀ + 1) hlt rfl)
          (fun a' s' hp => (ih _ hp).1)
      refine ⟨hplaced j₀ s (Nat.le_of_lt hlt) hb0, fun j hj hja => ?_⟩
      rcases Nat.le_total j j₀ with hle | hle
      · rw [hsame j j₀ s hle (Nat.le_of_lt hlt) hja.symm]
        exact hb0
      · rw [← hsame j₀ j s hle hj hja]
        exact hb0
  exact (key st h).1

theorem Program.linkedAt_layout [layout : Layout] {p : Program}
    [hv : Kraken.Executable.ValidExecutable (layout p)] :
    @Program.LinkedAt ⟨layout p⟩ p 0 := by
  have hnd : (Program.labels p).Nodup := Layout.text (p := p) ▸ hv.labels_nodup
  refine ⟨?_, fun i l hi => ?_⟩
  · show p <+: ((layout p).2.map (·.1)).drop 0
    rw [Layout.text, List.drop_zero]
    exact List.prefix_refl _
  · show (Executable.labels (layout p)).label l = (layout p).addrOf (0 + i)
    rw [Nat.zero_add]
    have hilt : i < p.length := (List.getElem?_eq_some_iff.mp hi).1
    have hlay : (layout p).2[i]? = some (Directive.label l, Kraken.Layout.size Directive i) := by
      rw [Layout.apply_getElem?, hi]; rfl
    refine Kraken.Executable.label_addrOf (layout p) l i ?_ ?_
    · rw [hlay, hv.label_size i l _ hlay]
    · have htake : ((layout p).2).take i = Layout.frag 0 (p.take i) := by
        rw [Layout.apply_snd]
        conv => lhs; rw [← List.take_append_drop i p, Layout.frag_append]
        exact List.take_left' (by rw [Layout.frag_length, List.length_take]; omega)
      intro dz hdz heq
      rw [htake] at hdz
      have h1 : l ∈ Program.labels (p.take i) :=
        Program.mem_labels_of_cell (heq ▸ Layout.frag_mem hdz)
      have h2 : l ∈ Program.labels (p.drop i) := by
        apply Program.mem_labels_of_cell
        rw [List.drop_eq_getElem_cons hilt, (List.getElem?_eq_some_iff.mp hi).2]
        exact List.mem_cons_self
      have hnd' := hnd
      rw [← List.take_append_drop i p, Program.labels_append] at hnd'
      exact (List.nodup_append.mp hnd').2.2 l h1 l h2 rfl

theorem Program.run_eventually [layout : Layout] {p : Program}
    [Kraken.Executable.ValidExecutable (layout p)] {Q : MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData}
    {post : MachineState → Prop} (h : @Program.run ⟨layout p⟩ p Q E s)
    (hQ : ∀ s', Q s' → ∀ pc, post (s', pc)) (hE : ∀ a s', ¬ E a s') :
    Eventually (straightlineStep (layout p)) post (s, layout.start) := by
  have := LinkedProgram.eventually_straightlineStep (e := layout p) (post := post) ?_
    (h 0 Program.linkedAt_layout)
  · change Eventually _ _ (s, (layout p).addrOf 0) at this
    rwa [Kraken.Executable.addrOf_zero, Layout.apply_fst] at this
  · rintro ⟨s', a⟩ (⟨ha, hq⟩ | he)
    · refine ⟨?_, hQ s' hq⟩
      rw [ha, Nat.zero_add]
      congr 1
      simp [Layout.apply_snd]
    · exact absurd he (hE _ _)
