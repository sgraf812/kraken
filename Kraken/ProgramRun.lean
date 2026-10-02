module

/-
The run of a program fragment inside the executable that hosts it.
`Program.run q Q E s` says: wherever `q` sits in the host, the burst from `q`'s
first cell eventually reaches `post` as soon as the burst after `q` does from
every state satisfying `Q`, and every exit satisfying `E` eventually reaches
`post`. The weakest preconditions of Kraken/StateWP.lean and
Kraken/SepWP.lean interpret a `Program` by this run.
-/
public import Kraken.SegmentExtract

@[expose] public section

/-- The executable that hosts the fragment under verification. -/
class Host where
  exe : Executable

instance [Host] : Labels := Executable.labels Host.exe

/-- `post` holds after finitely many bursts of the host. -/
def Host.Eventually [Host] (post : MachineState → Prop) : MachineState → Prop :=
  _root_.Eventually (fun st P => (Executable.straightline Host.exe st .done).All P) post

/-- The burst that runs the host from index `k` eventually reaches `post`. -/
def Host.burst [Host] (k : Nat) (s : MachineData) (post : MachineState → Prop) : Prop :=
  (Directives.interp (Host.exe.2.drop k) s (Host.exe.addrOf k) fun pc s => .done (s, pc)).All
    (Host.Eventually post)

def Program.run [Host] (q : Program) (Q : MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) : Prop :=
  ∀ k post, q <+: (Host.exe.2.map (·.1)).drop k →
    (∀ s', Q s' → Host.burst (k + q.length) s' post) →
    (∀ a s', E a s' → Host.Eventually post (s', a)) →
    Host.burst k s post

theorem Program.run_mono [Host] {q : Program} {Q₁ Q₂ : MachineData → Prop}
    {E₁ E₂ : Int64 → MachineData → Prop} (hQ : ∀ s, Q₁ s → Q₂ s) (hE : ∀ a s, E₁ a s → E₂ a s)
    {s : MachineData} (h : Program.run q Q₁ E₁ s) : Program.run q Q₂ E₂ s :=
  fun k post hs hQ₂ hE₂ =>
    h k post hs (fun s' h' => hQ₂ s' (hQ s' h')) (fun a s' h' => hE₂ a s' (hE a s' h'))

theorem List.cons_prefix_drop {α : Type} {d : α} {q L : List α} {k : Nat}
    (h : (d :: q) <+: L.drop k) : L[k]? = some d ∧ q <+: L.drop (k + 1) := by
  obtain ⟨t, ht⟩ := h
  have hk : L.drop k = d :: (q ++ t) := ht.symm
  refine ⟨?_, t, ?_⟩
  · simpa [List.head?_drop] using congrArg List.head? hk
  · rw [← List.drop_drop, hk]
    rfl

/-- The run of `d :: q` is the run of `d` with the run of `q` as its post. -/
theorem Program.run_cons [Host] {d : Directive} {q : Program} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData}
    (h : Program.run [d] (fun s' => Program.run q Q E s') E s) : Program.run (d :: q) Q E s := by
  intro k post hs hQ hE
  refine h k post ((List.prefix_append [d] q).trans hs) (fun s' h' => ?_) hE
  have hidx : k + (d :: q).length = k + 1 + q.length := by simp only [List.length_cons]; omega
  exact h' (k + 1) post (List.cons_prefix_drop hs).2 (fun s'' h'' => hidx ▸ hQ s'' h'') hE

/-! ## Bursts at an index of the host -/

theorem Host.cell_of_prefix [Host] {d : Directive} {q : Program} {k : Nat}
    (h : (d :: q) <+: (Host.exe.2.map (·.1)).drop k) : ∃ z, Host.exe.2[k]? = some (d, z) := by
  have hd := (List.cons_prefix_drop h).1
  rw [List.getElem?_map] at hd
  cases hc : Host.exe.2[k]? with
  | none => rw [hc] at hd; cases hd
  | some c =>
    rw [hc] at hd
    obtain ⟨d', z⟩ := c
    cases hd
    exact ⟨z, rfl⟩

theorem Host.burst_cell [Host] {k : Nat} {d : Directive} {z : Nat}
    (hd : Host.exe.2[k]? = some (d, z)) (s : MachineData) (post : MachineState → Prop) :
    Host.burst k s post =
      (Directive.interp d s ⟨Host.exe.addrOf k, Host.exe.addrOf (k + 1)⟩
        (fun s' => Directives.interp (Host.exe.2.drop (k + 1)) s' (Host.exe.addrOf (k + 1))
          fun pc s => .done (s, pc))
        (fun pc s => .done (s, pc))).All (Host.Eventually post) := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hd
  unfold Host.burst
  rw [List.drop_eq_getElem_cons hlt, hget, Kraken.Executable.addrOf_succ _ hd]
  rfl

theorem Host.burst_label [Host] {k : Nat} {l : Label} {z : Nat}
    (hd : Host.exe.2[k]? = some (Directive.label l, z)) (s : MachineData)
    (post : MachineState → Prop) : Host.burst k s post = Host.burst (k + 1) s post := by
  rw [Host.burst_cell hd]
  rfl

theorem Host.burst_end [Host] {k : Nat} (hk : Host.exe.2.length ≤ k) {s : MachineData}
    {post : MachineState → Prop} (h : ∀ pc, post (s, pc)) : Host.burst k s post := by
  unfold Host.burst
  rw [List.drop_eq_nil_of_le hk]
  exact Eventually.done _ (h _)

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

theorem Host.eventually_eq [Layout] (e : Executable) (post : MachineState → Prop) :
    @Host.Eventually (Host.mk e) post = _root_.Eventually (straightlineStep e) post := rfl

theorem Host.eventually_of_burst [layout : Layout] {p : Program} {s : MachineData}
    {post : MachineState → Prop} (h : @Host.burst ⟨layout p⟩ 0 s post) :
    _root_.Eventually (straightlineStep (layout p)) post (s, layout.start) := by
  refine _root_.Eventually.step _ _ ?_ fun _ h => h
  rw [straightlineStep_eq_interp]
  dsimp only
  rw [Kraken.Executable.directivesFromStart]
  unfold Host.burst at h
  rw [Host.eventually_eq] at h
  simpa [Layout.apply_snd, Layout.frag, Kraken.Executable.addrOf_zero, Layout.apply_fst] using h

theorem Program.run_eventually [layout : Layout] {p : Program} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData} {post : MachineState → Prop}
    (h : @Program.run ⟨layout p⟩ p Q E s) (hQ : ∀ s', Q s' → ∀ pc, post (s', pc))
    (hE : ∀ a s', E a s' → post (s', a)) :
    Eventually (straightlineStep (layout p)) post (s, layout.start) := by
  letI : Host := ⟨layout p⟩
  refine Host.eventually_of_burst (h 0 post ?_ (fun s' hq => Host.burst_end ?_ (hQ s' hq))
    (fun a s' he => Eventually.done _ (hE a s' he)))
  · show p <+: ((layout p).2.map (·.1)).drop 0
    rw [Layout.text, List.drop_zero]
    exact List.prefix_refl _
  · show (layout p).2.length ≤ 0 + p.length
    simp [Layout.apply_snd]
