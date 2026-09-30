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
`straightlineStep` judgment of the laid-out program, for any layout. The
label table is a parameter: a jump names its target through it, and the
read-back fixes it to the labels of the layout. -/

/-- The address behind a run of directives of sizes `zs` from `pc`. -/
def Program.endPc (pc : Int64) (zs : List Nat) : Int64 := zs.foldl (fun pc z => pc + .ofNat z) pc

/-- The run of the fragment `q` from `s` under the label table in scope: for
any directive sizes and continuation `rest` that the fragment sits in, the
burst from `pc` satisfies `Φ` as soon as `rest` does from every state
satisfying `Q` at the end of `q`, and `Φ` holds at every exit satisfying `E`.
An exit is the address the burst jumps to. -/
def Program.run [Labels] (q : Program) (Q : MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) : Prop :=
  ∀ (ds rest : List (Directive × Nat)) (pc : Int64) (Φ : MachineState → Prop),
    ds.map (·.1) = q →
    (∀ s', Q s' →
      (Directives.interp rest s' (Program.endPc pc (ds.map (·.2))) fun pc s => .done (s, pc)).All Φ) →
    (∀ a s', E a s' → Φ (s', a)) →
    (Directives.interp (ds ++ rest) s pc fun pc s => .done (s, pc)).All Φ

/-- A run of a program under the labels of its layout is the baseline
judgment of the laid-out program: from the layout's start, the burst of
`straightlineStep` ends in a state satisfying `post` when the fall-through
and every exit do. -/
theorem Program.run_straightlineStep [layout : Layout] {p : Program} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData} {post : MachineState → Prop}
    (h : @Program.run (Executable.labels (layout p)) p Q E s)
    (hQ : ∀ st', Q st'.1 → post st') (hE : ∀ a s', E a s' → post (s', a)) :
    straightlineStep (layout p) (s, layout.start) post := by
  show (@Directives.interp (Executable.labels (layout p)) ((layout p).directivesFromAddress
    layout.start) s layout.start fun pc s => .done (s, pc)).All _
  rw [Kraken.Executable.directivesFromStart, ← List.append_nil (p.mapIdx _)]
  exact h _ [] layout.start _ (List.ext_getElem (by simp) (by simp))
    (fun s' hq => hQ (s', _) hq) hE

theorem Program.run_mono [Labels] {q : Program} {Q₁ Q₂ : MachineData → Prop}
    {E₁ E₂ : Int64 → MachineData → Prop} (hQ : ∀ s, Q₁ s → Q₂ s) (hE : ∀ a s, E₁ a s → E₂ a s)
    {s : MachineData} (h : Program.run q Q₁ E₁ s) : Program.run q Q₂ E₂ s :=
  fun ds rest pc Φ hds hQ₂ hE₂ =>
    h ds rest pc Φ hds (fun s' h' => hQ₂ s' (hQ s' h')) (fun a s' h' => hE₂ a s' (hE a s' h'))

/-- The run of `d :: q` is the run of `d` with the run of `q` as its post:
the burst falls through `d` into `q`. -/
theorem Program.run_cons [Labels] {d : Directive} {q : Program} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData}
    (h : Program.run [d] (fun s' => Program.run q Q E s') E s) : Program.run (d :: q) Q E s := by
  intro ds rest pc Φ hds hQ hE
  match ds, hds with
  | (d', z) :: ds', hds =>
    obtain ⟨rfl, hq⟩ := List.cons.inj hds
    exact h [(d', z)] (ds' ++ rest) pc Φ rfl
      (fun s' hrun => hrun ds' rest (pc + Int64.ofNat z) Φ hq hQ hE) hE
