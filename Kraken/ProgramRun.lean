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

/-- The address behind a run of directives of sizes `zs` from `pc`. -/
def Program.endPc (pc : Int64) (zs : List Nat) : Int64 := zs.foldl (fun pc z => pc + .ofNat z) pc

/-- The burst runs the host from index `k`, and `Φ` holds of every state whose burst ends in `Φ`. -/
def Program.Hosted [Host] (ds rest : List (Directive × Nat)) (pc : Int64)
    (Φ : MachineState → Prop) : Prop :=
  ∃ k, Host.exe.2.drop k = ds ++ rest ∧ pc = Host.exe.addrOf k
    ∧ ∀ st, (Executable.straightline Host.exe st .done).All Φ → Φ st

/-- The run of the fragment `q` from `s`: for any directive sizes and continuation `rest` that
the fragment sits in, the burst from `pc` satisfies `Φ` as soon as `rest` does from every state
satisfying `Q` at the end of `q`, and `Φ` holds at every exit satisfying `E`. -/
def Program.run [Host] (q : Program) (Q : MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) : Prop :=
  ∀ (ds rest : List (Directive × Nat)) (pc : Int64) (Φ : MachineState → Prop),
    ds.map (·.1) = q →
    Program.Hosted ds rest pc Φ →
    (∀ s', Q s' →
      (Directives.interp rest s' (Program.endPc pc (ds.map (·.2))) fun pc s => .done (s, pc)).All Φ) →
    (∀ a s', E a s' → Φ (s', a)) →
    (Directives.interp (ds ++ rest) s pc fun pc s => .done (s, pc)).All Φ

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
    obtain ⟨k, hdrop, hpc, hclosed⟩ := hg
    have hcell : Host.exe.2[k]? = some (d', z) := by
      simpa [List.head?_drop] using congrArg List.head? hdrop
    refine h [(d', z)] (ds' ++ rest) pc Φ rfl ⟨k, hdrop, hpc, hclosed⟩
      (fun s' hrun => hrun ds' rest (pc + Int64.ofNat z) Φ hq ⟨k + 1, ?_, ?_, hclosed⟩ hQ hE) hE
    · rw [← List.drop_drop, hdrop]
      rfl
    · rw [Kraken.Executable.addrOf_succ _ hcell, hpc]

theorem Layout.frag_map_fst [Layout] (n : Nat) (p : Program) :
    (Layout.frag n p).map (·.1) = p :=
  List.ext_getElem (by simp) (by simp [Layout.frag])

/-! ## Runs at an index of the host -/

/-- The burst that runs the host from index `k`. -/
def Host.burst [Host] (k : Nat) (s : MachineData) (Φ : MachineState → Prop) : Prop :=
  (Directives.interp (Host.exe.2.drop k) s (Host.exe.addrOf k) fun pc s => .done (s, pc)).All Φ

theorem Host.burst_cell [Host] {k : Nat} {d : Directive} {z : Nat}
    (hd : Host.exe.2[k]? = some (d, z)) (s : MachineData) (Φ : MachineState → Prop) :
    Host.burst k s Φ =
      (Directive.interp d s ⟨Host.exe.addrOf k, Host.exe.addrOf (k + 1)⟩
        (fun s' => Directives.interp (Host.exe.2.drop (k + 1)) s' (Host.exe.addrOf (k + 1))
          fun pc s => .done (s, pc))
        (fun pc s => .done (s, pc))).All Φ := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hd
  unfold Host.burst
  rw [List.drop_eq_getElem_cons hlt, hget, Kraken.Executable.addrOf_succ _ hd]
  rfl

theorem Host.burst_label [Host] {k : Nat} {l : Label} {z : Nat}
    (hd : Host.exe.2[k]? = some (Directive.label l, z)) (s : MachineData)
    (Φ : MachineState → Prop) : Host.burst k s Φ = Host.burst (k + 1) s Φ := by
  rw [Host.burst_cell hd]
  rfl

theorem Host.burst_end [Host] {k : Nat} (hk : Host.exe.2.length ≤ k) {s : MachineData}
    {Φ : MachineState → Prop} (h : ∀ pc, Φ (s, pc)) : Host.burst k s Φ := by
  unfold Host.burst
  rw [List.drop_eq_nil_of_le hk]
  exact h _

theorem Program.endPc_addrOf (e : Executable) {k : Nat} {cs : List (Directive × Nat)}
    (h : cs <+: e.2.drop k) :
    Program.endPc (e.addrOf k) (cs.map (·.2)) = e.addrOf (k + cs.length) := by
  induction cs generalizing k with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨t, ht⟩ := h
    have hk : e.2.drop k = c :: (cs ++ t) := ht.symm
    have hc : e.2[k]? = some c := by simpa [List.head?_drop] using congrArg List.head? hk
    have hcs : cs <+: e.2.drop (k + 1) := ⟨t, by rw [← List.drop_drop, hk]; rfl⟩
    obtain ⟨d, z⟩ := c
    have hstep : Program.endPc (e.addrOf k) (((d, z) :: cs).map (·.2))
        = Program.endPc (e.addrOf k + .ofNat z) (cs.map (·.2)) := rfl
    rw [hstep, ← Kraken.Executable.addrOf_succ _ hc, ih hcs, List.length_cons]
    congr 1
    omega

/-- A run of `q` at index `k` of the host, for a `Φ` closed under bursts. -/
theorem Program.run_at [Host] {q : Program} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData} (h : Program.run q Q E s) {k : Nat}
    {Φ : MachineState → Prop} (hs : q <+: (Host.exe.2.map (·.1)).drop k)
    (hclosed : ∀ st, (Executable.straightline Host.exe st .done).All Φ → Φ st)
    (hQ : ∀ s', Q s' → Host.burst (k + q.length) s' Φ) (hE : ∀ a s', E a s' → Φ (s', a)) :
    Host.burst k s Φ := by
  have hds : ((Host.exe.2.drop k).take q.length).map (·.1) = q := by
    rw [List.map_take, List.map_drop]
    exact (List.prefix_iff_eq_take.mp hs).symm
  have hlen : ((Host.exe.2.drop k).take q.length).length = q.length := by
    rw [← List.length_map (f := (·.1)), hds]
  have hsplit : Host.exe.2.drop k
      = (Host.exe.2.drop k).take q.length ++ Host.exe.2.drop (k + q.length) := by
    conv => lhs; rw [← List.take_append_drop q.length (Host.exe.2.drop k)]
    rw [List.drop_drop]
  unfold Host.burst
  rw [hsplit]
  refine h _ _ _ _ hds ⟨k, hsplit, rfl, hclosed⟩ (fun s' hq => ?_) hE
  rw [Program.endPc_addrOf _ (List.take_prefix _ _), hlen]
  exact hQ s' hq

theorem eventually_closed [layout : Layout] (e : Executable) (post : MachineState → Prop)
    (st : MachineState) (h : (Executable.straightline e st .done).All (Eventually (straightlineStep e) post)) :
    Eventually (straightlineStep e) post st :=
  Eventually.step _ _ h fun _ h => h

theorem Layout.text {layout : Layout} {p : Program} : (layout p).2.map (·.1) = p := by
  rw [Layout.apply_snd, Layout.frag_map_fst]

theorem straightlineStep_eq_interp [Layout] (e : Executable) (st : MachineState)
    (post : MachineState → Prop) :
    straightlineStep e st post
      = (@Directives.interp (Executable.labels e) (e.directivesFromAddress st.2) st.1 st.2
          fun pc s => .done (s, pc)).All post := by
  unfold straightlineStep Executable.straightline
  rfl

theorem Effects.All.mono {P R : MachineState → Prop} (h : ∀ st, P st → R st) {eff : Effects}
    (hp : eff.All P) : eff.All R := by
  induction eff <;> simp_all [Effects.All]

theorem closed_of_eventually [Layout] {e : Executable} {R Φ : MachineState → Prop}
    (hR : ∀ st, R st → Φ st) (hclosed : ∀ st, (Executable.straightline e st .done).All Φ → Φ st)
    {st : MachineState} (h : Eventually (straightlineStep e) R st) : Φ st := by
  induction h with
  | done st hr => exact hR st hr
  | step st _ htrans _ ih => exact hclosed st (Effects.All.mono ih htrans)

theorem eventually_of_burst [layout : Layout] {p : Program} {s : MachineData}
    {post : MachineState → Prop}
    (h : @Host.burst ⟨layout p⟩ 0 s (Eventually (straightlineStep (layout p)) post)) :
    Eventually (straightlineStep (layout p)) post (s, layout.start) := by
  refine Eventually.step _ _ ?_ fun _ h => h
  rw [straightlineStep_eq_interp]
  dsimp only
  rw [Kraken.Executable.directivesFromStart]
  unfold Host.burst at h
  simpa [Layout.apply_snd, Layout.frag, Kraken.Executable.addrOf_zero, Layout.apply_fst] using h

theorem Program.run_eventually [layout : Layout] {p : Program} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData} {post : MachineState → Prop}
    (h : @Program.run ⟨layout p⟩ p Q E s) (hQ : ∀ s', Q s' → ∀ pc, post (s', pc))
    (hE : ∀ a s', E a s' → post (s', a)) :
    Eventually (straightlineStep (layout p)) post (s, layout.start) := by
  letI : Host := ⟨layout p⟩
  refine eventually_of_burst (Program.run_at h ?_ (eventually_closed _ _)
    (fun s' hq => Host.burst_end ?_ fun pc => Eventually.done _ (hQ s' hq pc))
    (fun a s' he => Eventually.done _ (hE a s' he)))
  · show p <+: ((layout p).2.map (·.1)).drop 0
    rw [Layout.text, List.drop_zero]
    exact List.prefix_refl _
  · show (layout p).2.length ≤ 0 + p.length
    simp [Layout.apply_snd]
