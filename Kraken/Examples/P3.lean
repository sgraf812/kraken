/-
The squaring loop `p3`: starting from `rdx = 2`, each iteration squares `rdx`
by `mulx` and counts `rbx` down to zero, so the loop computes
`rdx = 2 ^ 2 ^ rbx`. `p3_correct` proves it against the omni-semantics
judgments.

The program is three fragments, `p3.entry ++ p3.loop ++ p3.exit`. `Layout.frag`
lays a fragment out at its position in the program, and the segment a cut point
reaches is the fragments from there on, joined by `++`. `Directives.frag_append_spec`
and `Directives.append_spec` decompose that join and `Directives.frag_cons_spec`
walks into a fragment, so `vcgen` steps each directive once, in the one proof
that specifies its fragment: the prologue in `p3_enter`, the loop in
`p3_body_spec`, the tail in `p3_end_spec`. `Eventually.loop` takes that one body
specification for every `k`, so nothing traverses the loop a second time.

Every result here is a `Triple`, `p3_correct` included: a run of an executable
is a predicate transformer too, and `wp p3 Q ⊥` is the omni-semantics judgment
that a run of the laid-out program reaches `Q`, or leaves the program text at
`E`. `Program.runStep_of_seg` carries a fragment's triple into that run, and
`Program.wp_sound` reads the result back as the omni-semantics judgment.

Each cut point gets an address (`p3_start_addr`, `p3_end_addr`) and the segment
reached from it (`p3_start_segment`, `p3_end_segment`). The segments chain by
`Eventually.step`, and the loop closes by `Eventually.loop` with the invariant
`rbx = k ∧ rdx = 2 ^ 2 ^ (rbx₀ - k)` at the header.
-/
import Kraken.Parser
import Kraken.SegmentExtract
import Kraken.SegmentWP
import Kraken.SegmentWPSound

open Kraken.Parser
open Std.Internal.Do

set_option mvcgen.warning false

/-- The prologue: it sets the base `rdx` holds on entry to the loop. -/
abbrev p3.entry : Program := parse("
init:
  mov $2, %rdx
")

/-- The loop: it squares `rdx` and counts `rbx` down, jumping to `_end` at zero. -/
abbrev p3.loop : Program := parse("
start:
  sub $0, %rbx
  jz _end
  mulx %rdx, %rdx, %rax
  sub $1, %rbx
  jmp start
")

/-- The tail the loop exits to. -/
abbrev p3.exit : Program := parse("
_end:
  nop
")

/-- The program a run of `p3` executes: the prologue, the loop, the tail.

The fragments above are reducible, so `vcgen` walks into their directives; `p3`
and `p3.body` are not, so a proof that cites their specifications never steps
them. -/
def p3 : Program := p3.entry ++ p3.loop ++ p3.exit

/-- The directives a run reaches from the loop header: the loop and the tail it
falls into, laid out past the prologue. -/
def p3.body [Layout] : List (Directive × Nat) :=
  Layout.frag p3.entry.length (p3.loop ++ p3.exit)

/-- The split at the loop header. -/
private theorem p3_eq_entry_append : p3 = p3.entry ++ (p3.loop ++ p3.exit) := by simp [p3]

/-- The split at the exit label. -/
private theorem p3_eq_loop_append : p3 = (p3.entry ++ p3.loop) ++ p3.exit := by simp [p3]

/-- What a run of `p3` computes from the machine it starts on. -/
def p3_spec (d : MachineData) : Nat := 2 ^ 2 ^ d.regs.rbx.toNat

/-- One squaring step of the exponent tower. -/
private theorem pow_sq (e : Nat) : 2 ^ 2 ^ e * 2 ^ 2 ^ e = 2 ^ 2 ^ (e + 1) := by
  rw [← Nat.pow_add, Nat.pow_succ, Nat.mul_two]

/-! ## Segment extraction

The three cut points a run of `p3` visits: the entry, the loop head `start`,
and the exit label `_end`. Each cut point falls on a fragment boundary, so the
text a segment traverses is the suffix of `p3.entry ++ p3.loop ++ p3.exit` that
starts there, laid out with the sizes past the fragments before it. -/

section Extraction

attribute [local simp] p3 Layout.apply_fst Layout.apply_snd

variable [layout : Layout]

/-- From the start the run traverses the prologue and falls into the loop. -/
theorem p3_entry_segment :
    (layout p3).directivesFromAddress layout.start = Layout.frag 0 p3.entry ++ p3.body := by
  have h := Executable.directivesFromAddress_addrOf (layout p3) 0 (Nat.zero_le _)
    (fun k hk => absurd hk (Nat.not_lt_zero k))
  rw [p3.body, ← Nat.zero_add p3.entry.length, ← Layout.frag_append,
    ← p3_eq_entry_append, ← Layout.apply_snd]
  simpa using h

variable [hv : Executable.ValidLayout (layout p3)]

theorem p3_start_addr :
    (layout p3).labels.label "start" = (layout p3).addrOf p3.entry.length := by
  have h2 : (layout p3).2[p3.entry.length]? = some (.label "start", layout.size p3.entry.length) := by
    simp
  with_reducible apply Executable.label_addrOf
  · rw [h2, hv.label_size _ "start" _ h2]
  · simp

/-- From the loop header the run traverses the loop fragment and the tail it
falls into. -/
theorem p3_start_segment :
    (layout p3).directivesFromAddress ((layout p3).labels.label "start")
      = p3.body := by
  rw [p3_start_addr, Executable.directivesFromAddress_addrOf]
  · rw [p3_eq_entry_append, p3.body]
    with_reducible exact Layout.apply_drop p3.entry (p3.loop ++ p3.exit)
  · simp
  · intro k hk
    with_reducible apply Executable.addrOf_ne_of_valid (layout p3) hk <;>
      simp

theorem p3_end_addr :
    (layout p3).labels.label "_end" = (layout p3).addrOf (p3.entry ++ p3.loop).length := by
  have h8 : (layout p3).2[(p3.entry ++ p3.loop).length]?
      = some (.label "_end", layout.size (p3.entry ++ p3.loop).length) := by
    simp
  with_reducible apply Executable.label_addrOf
  · rw [h8, hv.label_size _ "_end" _ h8]
  · simp

/-- From `_end` the run traverses the tail fragment alone. -/
theorem p3_end_segment :
    (layout p3).directivesFromAddress ((layout p3).labels.label "_end")
      = Layout.frag (p3.entry ++ p3.loop).length p3.exit := by
  rw [p3_end_addr, Executable.directivesFromAddress_addrOf]
  · rw [p3_eq_loop_append]
    with_reducible exact Layout.apply_drop (p3.entry ++ p3.loop) p3.exit
  · simp
  · intro k hk
    with_reducible apply Executable.addrOf_ne_of_valid (layout p3) hk <;>
      simp

/-- Traversing the prologue lands on the loop header. -/
theorem p3_start_pc :
    layout.start + .ofNat (layout.size 0) + .ofNat (layout.size 1)
      = (layout p3).labels.label "start" := by
  have h0 : ((layout p3).2[0]?).map (·.2) = some (layout.size 0) := by simp
  have h1 : ((layout p3).2[1]?).map (·.2) = some (layout.size 1) := by simp
  rw [p3_start_addr, show p3.entry.length = 1 + 1 by simp [p3.entry],
    Executable.addrOf_succ' (layout p3) h1, Executable.addrOf_succ' (layout p3) h0,
    Executable.addrOf_zero, Layout.apply_fst]

/-- Traversing the tail fragment ends just past the program text. -/
private theorem p3_end_pc :
    (layout p3).labels.label "_end"
        + .ofNat (layout.size (p3.entry ++ p3.loop).length)
        + .ofNat (layout.size ((p3.entry ++ p3.loop).length + 1))
      = (layout p3).addrOf p3.length := by
  have h8 : ((layout p3).2[(p3.entry ++ p3.loop).length]?).map (·.2)
      = some (layout.size (p3.entry ++ p3.loop).length) := by simp
  have h9 : ((layout p3).2[(p3.entry ++ p3.loop).length + 1]?).map (·.2)
      = some (layout.size ((p3.entry ++ p3.loop).length + 1)) := by simp
  rw [p3_end_addr, ← Executable.addrOf_succ' (layout p3) h8,
    ← Executable.addrOf_succ' (layout p3) h9]
  simp

end Extraction

/-! ## The proof -/

section Proof

variable [layout : Layout] [hv : Executable.ValidLayout (layout p3)]

/-- The loop invariant at the header, indexed by the remaining iteration
count `k`: `rbx` holds `k` and `rdx` holds the `rbx₀ - k`-fold squaring. -/
private abbrev p3_inv (rbx0 k : Nat) (s : MachineData) : Prop :=
  s.regs.rbx.toNat = k ∧ k ≤ rbx0 ∧ s.regs.rdx.toNat = 2 ^ 2 ^ (rbx0 - k) ∧ s.regs.rax = 0

/-- The tail: the label and the `nop` leave the machine unchanged, and the run
falls off the end of the program text. -/
private theorem p3_end_spec (Q : Unit → Labels → MachineState → Prop) :
    ⦃ fun labels st => st.2 = (layout p3).labels.label "_end"
        ∧ Q () labels (st.1, (layout p3).addrOf p3.length) ⦄
      (Layout.frag (p3.entry ++ p3.loop).length p3.exit)
    ⦃ Q ⦄ := by
  with_reducible refine Triple.intro fun labels st ⟨hpc, hq⟩ => ?_
  obtain ⟨m, pc⟩ := st
  simp only at hpc hq
  subst hpc
  vcgen simplifying_assumptions
  rw [p3_end_pc]
  with_reducible exact hq

/-- Where a traversal from the loop header leaves the segment: back at the
header with one iteration accounted for, or at `_end` with the answer. -/
private abbrev p3_exits (rbx0 k : Nat) (st : MachineState) : Prop :=
  (k ≠ 0 ∧ st.2 = (layout p3).labels.label "start" ∧ p3_inv rbx0 (k - 1) st.1)
  ∨ (k = 0 ∧ st.2 = (layout p3).labels.label "_end"
      ∧ st.1.regs.rdx.toNat = 2 ^ 2 ^ rbx0 ∧ st.1.regs.rax = 0)

/-- Both cut points a jump of `p3` targets are directives of `p3`. -/
private theorem p3_exits_inText (rbx0 k : Nat) (st : MachineState)
    (h : st.2 = (layout p3).labels.label "start"
      ∨ (st.2 = (layout p3).labels.label "_end"
          ∧ st.1.regs.rdx.toNat = 2 ^ 2 ^ rbx0 ∧ st.1.regs.rax = 0)) :
    (layout p3).directivesFromAddress st.2 ≠ [] := by
  rcases h with hpc | ⟨hpc, -, -⟩ <;> rw [hpc]
  · rw [p3_start_segment, p3.body]
    simp [p3.loop]
  · rw [p3_end_segment]
    simp [p3.exit]

omit hv in
/-- The loop body: entered at the header with `k` iterations left, the run never
falls off its segment, and every jump exit is one of `p3_exits`. -/
private theorem p3_body_spec (rbx0 k : Nat) (hbound : 2 ^ 2 ^ rbx0 < 2 ^ 64)
    (Q : Unit → Labels → MachineState → Prop) :
    ⦃ fun labels st => labels = (layout p3).labels
        ∧ st.2 = (layout p3).labels.label "start" ∧ p3_inv rbx0 k st.1 ⦄
      p3.body
    ⦃ Q; p3_exits rbx0 k ⦄ := by
  with_reducible refine Triple.intro fun labels st ⟨hlab, hpc, hrbx, hle, hrdx, hrax⟩ => ?_
  subst hlab
  have hlt : k ≠ 0 → st.1.regs.rdx.toNat * st.1.regs.rdx.toNat < 2 ^ 64 := by
    intro _
    rw [hrdx, pow_sq]
    calc 2 ^ 2 ^ (rbx0 - k + 1)
        ≤ 2 ^ 2 ^ rbx0 :=
          Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
      _ < 2 ^ 64 := hbound
  have hsq : k ≠ 0 → st.1.regs.rdx.toNat * st.1.regs.rdx.toNat = 2 ^ 2 ^ (rbx0 - (k - 1)) := by
    intro hk
    rw [hrdx, pow_sq, show rbx0 - (k - 1) = rbx0 - k + 1 from by omega]
  simp only [p3.body]
  vcgen simplifying_assumptions with finish

/-- The prologue sets `rdx` to `2`, which is the invariant at the full count,
and falls into the loop; the segment's exits are the loop's. -/
private theorem p3_enter_spec (rbx0 : Nat) (hbound : 2 ^ 2 ^ rbx0 < 2 ^ 64)
    (Q : Unit → Labels → MachineState → Prop) :
    ⦃ fun labels st => labels = (layout p3).labels ∧ st.2 = layout.start
        ∧ st.1.regs.rbx.toNat = rbx0 ∧ st.1.regs.rax = 0 ⦄
      (Layout.frag 0 p3.entry ++ p3.body)
    ⦃ Q; p3_exits rbx0 rbx0 ⦄ := by
  with_reducible refine Triple.intro fun labels st ⟨hlab, hpc, hrbx, hrax⟩ => ?_
  subst hlab
  obtain ⟨m, pc⟩ := st
  simp only at hpc hrbx hrax
  subst hpc
  have hstart := p3_start_pc (layout := layout)
  vcgen [p3_body_spec rbx0 rbx0 hbound] simplifying_assumptions with finish

/-- From the exit label the tail carries the answer to the end of the text. -/
private theorem p3_finish (rbx0 : Nat) (E : MachineState → Prop) (st : MachineState)
    (h : st.2 = (layout p3).labels.label "_end"
      ∧ st.1.regs.rdx.toNat = 2 ^ 2 ^ rbx0 ∧ st.1.regs.rax = 0) :
    Eventually (Program.runStep p3 E)
      (fun s => s.1.regs.rdx.toNat = 2 ^ 2 ^ rbx0 ∧ s.1.regs.rax = 0) st := by
  obtain ⟨m, pc⟩ := st
  obtain ⟨hpc, hrdx, hrax⟩ := h
  simp only at hpc hrdx hrax
  subst hpc
  refine step_cps _ _ _ (Program.runStep_of_seg p3_end_segment ?_)
  refine Directives.wp_mono
    (Q₁ := fun _ _ mid => Eventually (Program.runStep p3 E)
      (fun s => s.1.regs.rdx.toNat = 2 ^ 2 ^ rbx0 ∧ s.1.regs.rax = 0) mid)
    (E₁ := (Lean.Order.bot : MachineState → Prop))
    _ _ _ (fun _ h => h) (fun _ h => Assertion.bot_elim h) ?_
  exact (p3_end_spec _).le_wp _ _ ⟨rfl, Eventually.done _ ⟨hrdx, hrax⟩⟩

/-- A run of `p3` from a machine whose `rax` is clear reaches a state where
`rdx` holds `2 ^ 2 ^ rbx` and `rax` is clear again. The triple names no
exceptional postcondition: the run never leaves the program text. -/
theorem p3_correct (d : MachineData) (h_bounds : p3_spec d < 2 ^ 64)
    (h_rax : d.regs.rax = 0) :
    ⦃ fun labels st => labels = (layout p3).labels ∧ st = (d, layout.start) ⦄
      p3
    ⦃ fun _ _ st => st.1.regs.rdx.toNat = p3_spec d ∧ st.1.regs.rax = 0 ⦄ := by
  with_reducible refine Triple.intro fun labels st ⟨hlab, hst⟩ => ?_
  subst hlab
  subst hst
  rw [Program.wp_eq]
  simp only [p3_spec] at h_bounds ⊢
  refine Eventually.step _ (p3_exits d.regs.rbx.toNat d.regs.rbx.toNat) ?_ ?_
  · refine Program.runStep_of_seg p3_entry_segment ?_
    refine Directives.wp_mono (Q₁ := fun _ _ _ => False) _ _ _ (fun _ h => h.elim)
      (fun st h => ⟨p3_exits_inText d.regs.rbx.toNat d.regs.rbx.toNat st
        (h.elim (fun hl => Or.inl hl.2.1) (fun hr => Or.inr hr.2)), h⟩) ?_
    exact (p3_enter_spec d.regs.rbx.toNat h_bounds _).le_wp _ _ ⟨rfl, rfl, rfl, h_rax⟩
  · rintro ⟨m, pc⟩ (⟨hne, hpc, hinv⟩ | hexit)
    · subst hpc
      exact Eventually.loop p3_start_segment
        (fun k => p3_body_spec d.regs.rbx.toNat k h_bounds _)
        (fun st h => p3_exits_inText d.regs.rbx.toNat 0 st h)
        (p3_finish d.regs.rbx.toNat _) _ m hinv
    · exact p3_finish d.regs.rbx.toNat _ _ hexit.2

/-- `p3_correct` read as the omni-semantics judgment of `Kraken.OmniSemantics`:
a run of the laid-out program from `(d, layout.start)` reaches a state where
`rdx` holds `2 ^ 2 ^ rbx` and `rax` is clear. The run never leaves the program
text, so the exceptional postcondition is `False` and drops out. -/
theorem p3_correct_run (d : MachineData) (h_bounds : p3_spec d < 2 ^ 64)
    (h_rax : d.regs.rax = 0) :
    Eventually (straightlineStep (layout p3))
      (fun s => s.1.regs.rdx.toNat = p3_spec d ∧ s.1.regs.rax = 0)
      (d, layout.start) :=
  (Program.wp_sound
      ((p3_correct d h_bounds h_rax).le_wp _ _ ⟨rfl, rfl⟩)).mono
    (fun _ _ hst => hst) (fun _ hs => hs.elim id Assertion.bot_elim)

end Proof
