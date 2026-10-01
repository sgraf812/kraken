module

/-
The run of a program fragment in the baseline interpreter. `Program.run q Q E s`
says: in any burst that runs `q` from `s` and continues into the rest of its
directive list, `q` falls through with `Q` or exits with `E`. The weakest
preconditions of Kraken/StateWP.lean and Kraken/SepWP.lean interpret a
`Program` by this run.
-/
public import Kraken.SegmentExtract

@[expose] public section

/-- The executable that hosts the fragment under verification. -/
class Host where
  exe : Executable

instance [Host] : Labels := Executable.labels Host.exe

def Directive.isCall : Directive → Bool
  | .instr (.regular _ _ (.call _)) => true
  | _ => false

/-- The address behind a run of directives of sizes `zs` from `pc`. -/
def Program.endPc (pc : Int64) (zs : List Nat) : Int64 := zs.foldl (fun pc z => pc + .ofNat z) pc

/-- The burst runs the host from index `k`, and `Φ` holds of every state whose burst ends in `Φ`. -/
def Program.Hosted [Host] (ds rest : List (Directive × Nat)) (pc : Int64)
    (Φ : MachineState → Prop) : Prop :=
  ∃ k, Host.exe.2.drop k = ds ++ rest ∧ pc = Host.exe.addrOf k
    ∧ ∀ st, (Executable.straightline Host.exe st .done).All Φ → Φ st

/-- The run of the fragment `q` from `s`: for any directive sizes and continuation `rest` that
the fragment sits in, the burst from `pc` satisfies `Φ` as soon as `rest` does from every state
satisfying `Q` at the end of `q`, and `Φ` holds at every exit satisfying `E`. A fragment that
calls runs inside the host. -/
def Program.run [Host] (q : Program) (Q : MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) : Prop :=
  ∀ (ds rest : List (Directive × Nat)) (pc : Int64) (Φ : MachineState → Prop),
    ds.map (·.1) = q →
    (q.any Directive.isCall → Program.Hosted ds rest pc Φ) →
    (∀ s', Q s' →
      (Directives.interp rest s' (Program.endPc pc (ds.map (·.2))) fun pc s => .done (s, pc)).All Φ) →
    (∀ a s', E a s' → Φ (s', a)) →
    (Directives.interp (ds ++ rest) s pc fun pc s => .done (s, pc)).All Φ

theorem Program.run_straightlineStep [layout : Layout] {p : Program} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData} {post : MachineState → Prop}
    (h : @Program.run ⟨layout p⟩ p Q E s) (hcall : p.any Directive.isCall = false)
    (hQ : ∀ st', Q st'.1 → post st') (hE : ∀ a s', E a s' → post (s', a)) :
    straightlineStep (layout p) (s, layout.start) post := by
  show (@Directives.interp (Executable.labels (layout p)) ((layout p).directivesFromAddress
    layout.start) s layout.start fun pc s => .done (s, pc)).All _
  rw [Kraken.Executable.directivesFromStart, ← List.append_nil (p.mapIdx _)]
  exact h _ [] layout.start _ (List.ext_getElem (by simp) (by simp))
    (fun hc => absurd hc (by simp [hcall])) (fun s' hq => hQ (s', _) hq) hE

theorem Program.run_mono [Host] {q : Program} {Q₁ Q₂ : MachineData → Prop}
    {E₁ E₂ : Int64 → MachineData → Prop} (hQ : ∀ s, Q₁ s → Q₂ s) (hE : ∀ a s, E₁ a s → E₂ a s)
    {s : MachineData} (h : Program.run q Q₁ E₁ s) : Program.run q Q₂ E₂ s :=
  fun ds rest pc Φ hds hg hQ₂ hE₂ =>
    h ds rest pc Φ hds hg (fun s' h' => hQ₂ s' (hQ s' h')) (fun a s' h' => hE₂ a s' (hE a s' h'))

/-- The run of `d :: q` is the run of `d` with the run of `q` as its post:
the burst falls through `d` into `q`. -/
theorem Program.run_cons [Host] {d : Directive} {q : Program} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData}
    (h : Program.run [d] (fun s' => Program.run q Q E s') E s) : Program.run (d :: q) Q E s := by
  intro ds rest pc Φ hds hg hQ hE
  match ds, hds with
  | (d', z) :: ds', hds =>
    obtain ⟨rfl, hq⟩ := List.cons.inj hds
    refine h [(d', z)] (ds' ++ rest) pc Φ rfl (fun hc => ?_)
      (fun s' hrun => hrun ds' rest (pc + Int64.ofNat z) Φ hq (fun hc => ?_) hQ hE) hE
    · exact hg (by simp_all [List.any_cons])
    · obtain ⟨k, hdrop, hpc, hclosed⟩ := hg (by simp_all [List.any_cons])
      have hcell : Host.exe.2[k]? = some (d', z) := by
        simpa [List.head?_drop] using congrArg List.head? hdrop
      refine ⟨k + 1, ?_, ?_, hclosed⟩
      · rw [← List.drop_drop, hdrop]
        rfl
      · rw [Kraken.Executable.addrOf_succ _ hcell, hpc]
