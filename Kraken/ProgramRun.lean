module

/-
The run of a program fragment in the baseline interpreter. `Program.run q Q E s`
says: in any burst that runs `q` from `s` and continues into the rest of its
directive list, `q` falls through with `Q` or exits with `E`. The weakest
preconditions of Kraken/StateWP.lean and Kraken/SepWP.lean interpret a
`Program` by this run.
-/
public import Kraken.X64.OmniSemantics

@[expose] public section

/-! ## The run of a fragment

The run of a fragment is stated over the baseline interpreter's burst:
`Directives.interp` runs a list of directives, falling through from one to
the next and stopping at a jump or at the end of the list, which is how
`straightlineStep` runs a program. The fragment is a prefix of the list, and
the run hands the rest of the list the state the fragment falls through
with. `Program.run_straightlineStep` reads the run of a whole program as the
`straightlineStep` judgment of the laid-out program, for any layout. -/

/-- The address behind a run of directives of sizes `zs` from `pc`. -/
def Program.endPc (pc : Int64) (zs : List Nat) : Int64 := zs.foldl (fun pc z => pc + .ofNat z) pc

/-- The run of the fragment `q` from `s`: whatever label table, directive
sizes and continuation `rest` the fragment sits in, the burst from `pc`
satisfies `Φ` as soon as `rest` does from every state satisfying `Q` at the
end of `q`, and `Φ` holds at every exit satisfying `E`. -/
def Program.run (q : Program) (Q : MachineData → Prop) (E : Int64 → MachineData → Prop)
    (s : MachineData) : Prop :=
  ∀ (L : Labels) (ds rest : List (Directive × Nat)) (pc : Int64) (Φ : MachineState → Prop),
    ds.map (·.1) = q →
    (∀ s', Q s' →
      (@Directives.interp L rest s' (Program.endPc pc (ds.map (·.2))) fun pc s => .done (s, pc)).All Φ) →
    (∀ a s', E a s' → Φ (s', a)) →
    (@Directives.interp L (ds ++ rest) s pc fun pc s => .done (s, pc)).All Φ

/-- A run of a program is the baseline judgment of the laid-out program: from
the layout's start, the burst of `straightlineStep` ends in a state
satisfying `post` when the fall-through and every exit do. -/
theorem Program.run_straightlineStep [layout : Layout] {p : Program} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {e : Executable} {st : MachineState}
    {post : MachineState → Prop} (h : Program.run p Q E st.1) (he : e = layout p)
    (hpc : st.2 = layout.start) (hQ : ∀ st', Q st'.1 → post st')
    (hE : ∀ a s', E a s' → post (s', a)) :
    straightlineStep e st post := by
  obtain ⟨s, pc⟩ := st
  subst he hpc
  show (@Directives.interp (Executable.labels (layout p)) ((layout p).directivesFromAddress
    layout.start) s layout.start fun pc s => .done (s, pc)).All _
  rw [Kraken.Executable.directivesFromStart, ← List.append_nil (p.mapIdx _)]
  exact h (Executable.labels (layout p)) _ [] layout.start _ (List.ext_getElem (by simp) (by simp))
    (fun s' hq => hQ (s', _) hq) hE

/- With a `Directives.interp` that returns its final state as
`Effects MachineState` instead of passing it to `ret`, the run would be the
burst's `.All` of the post, without the continuation `rest` and the post `Φ`:
`(Directives.interp ds s pc).All fun st => (st.2 = endPc pc sizes ∧ Q st.1) ∨ E st.2 st.1`.
`Program.run_cons` would then be the bind law of `Effects.All`, and the lemma
above the instance `ds := (layout p).2`. -/

theorem Program.run_mono {q : Program} {Q₁ Q₂ : MachineData → Prop}
    {E₁ E₂ : Int64 → MachineData → Prop} (hQ : ∀ s, Q₁ s → Q₂ s) (hE : ∀ a s, E₁ a s → E₂ a s)
    {s : MachineData} (h : Program.run q Q₁ E₁ s) : Program.run q Q₂ E₂ s :=
  fun L ds rest pc Φ hds hQ₂ hE₂ =>
    h L ds rest pc Φ hds (fun s' h' => hQ₂ s' (hQ s' h')) (fun a s' h' => hE₂ a s' (hE a s' h'))

/-- The run of `d :: q` is the run of `d` with the run of `q` as its post:
the burst falls through `d` into `q`. -/
theorem Program.run_cons {d : Directive} {q : Program} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData}
    (h : Program.run [d] (fun s' => Program.run q Q E s') E s) : Program.run (d :: q) Q E s := by
  intro L ds rest pc Φ hds hQ hE
  match ds, hds with
  | (d', z) :: ds', hds =>
    obtain ⟨rfl, hq⟩ := List.cons.inj hds
    exact h L [(d', z)] (ds' ++ rest) pc Φ rfl
      (fun s' hrun => hrun L ds' rest (pc + Int64.ofNat z) Φ hq hQ hE) hE
