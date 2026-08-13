/-
The squaring loop `p3`: starting from `rdx = 2`, each iteration squares `rdx`
by `mulx` and counts `rbx` down to zero, so the loop computes
`rdx = 2 ^ 2 ^ rbx`. `p3_correct` proves it against the omni-semantics
judgments.

The program is three fragments, `p3.entry ++ p3.loop ++ p3.exit`, and every
spec is a `Triple` over a fragment as written. The `wp` of a `Program`
quantifies over every sizing a layout can give it, so `p3_loop_spec` mentions
no layout, no position, and no program counter. Its parameter `L` is the label
footprint: the assertions name the addresses of `start` and `_end`, nothing
else.

A run enters through `Eventually.enter` at a cut point. Each cut point gets an
address (`p3_start_addr`, `p3_end_addr`) and the fragment reached from it
(`p3_entry_segment`, `p3_start_segment`, `p3_end_segment`), and `vcgen` walks
that fragment through the `Program` specs, so each directive is stepped once.
The loop closes by `Eventually.loop` with the invariant
`rbx = k ∧ rdx = 2 ^ 2 ^ (rbx₀ - k)` at the header, and `Program.run_sound`
reads the run back as the baseline judgment (`p3_correct_run`).
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
is not, so a proof that cites its parts never steps them. -/
def p3 : Program := p3.entry ++ p3.loop ++ p3.exit

/-- The label table of the laid-out program. -/
abbrev p3.labels [layout : Layout] : Labels := (layout p3).labels

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
    (layout p3).directivesFromAddress layout.start
      = Layout.frag 0 (p3.entry ++ (p3.loop ++ p3.exit)) := by
  have h := Executable.directivesFromAddress_addrOf (layout p3) 0 (Nat.zero_le _)
    (fun k hk => absurd hk (Nat.not_lt_zero k))
  rw [← p3_eq_entry_append, ← Layout.apply_snd]
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
      = Layout.frag p3.entry.length (p3.loop ++ p3.exit) := by
  rw [p3_start_addr, Executable.directivesFromAddress_addrOf]
  · rw [p3_eq_entry_append]
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

end Extraction

/-! ## The proof -/

section Proof

variable [layout : Layout] [hv : Executable.ValidLayout (layout p3)]

/-- The loop invariant at the header, indexed by the remaining iteration
count `k`: `rbx` holds `k` and `rdx` holds the `rbx₀ - k`-fold squaring. -/
private abbrev p3_inv (rbx0 k : Nat) (s : MachineData) : Prop :=
  s.regs.rbx.toNat = k ∧ k ≤ rbx0 ∧ s.regs.rdx.toNat = 2 ^ 2 ^ (rbx0 - k) ∧ s.regs.rax = 0

/-- Where a traversal from the loop header leaves the segment: back at the
header with one iteration accounted for, or at `_end` with the answer. -/
private abbrev p3_exits (L : Labels) (rbx0 k : Nat) (st : MachineState) : Prop :=
  (k ≠ 0 ∧ st.2 = L.label "start" ∧ p3_inv rbx0 (k - 1) st.1)
  ∨ (k = 0 ∧ st.2 = L.label "_end"
      ∧ st.1.regs.rdx.toNat = 2 ^ 2 ^ rbx0 ∧ st.1.regs.rax = 0)

/-- Both cut points a jump of `p3` targets are directives of `p3`. -/
private theorem p3_exits_inText (rbx0 : Nat) (st : MachineState)
    (h : st.2 = (layout p3).labels.label "start"
      ∨ (st.2 = (layout p3).labels.label "_end"
          ∧ st.1.regs.rdx.toNat = 2 ^ 2 ^ rbx0 ∧ st.1.regs.rax = 0)) :
    (layout p3).directivesFromAddress st.2 ≠ [] := by
  rcases h with hpc | ⟨hpc, -, -⟩ <;> rw [hpc]
  · rw [p3_start_segment]
    simp [p3.loop, Layout.frag]
  · rw [p3_end_segment]
    simp [p3.exit, Layout.frag]

omit layout hv in
/-- The loop, as a fragment: no layout, no position, no program counter. `L` is
the label footprint, the addresses of the two targets the fragment's jumps
name. Placing the fragment in a concrete program is the use site's obligation,
discharged by its extraction lemmas. -/
private theorem p3_loop_spec (L : Labels) (rbx0 k : Nat)
    (hbound : 2 ^ 2 ^ rbx0 < 2 ^ 64) (Q : Unit → Labels → MachineData → Prop) :
    ⦃ fun labels s => labels = L ∧ p3_inv rbx0 k s ⦄
      (p3.loop ++ p3.exit)
    ⦃ Q; p3_exits L rbx0 k ⦄ := by
  with_reducible refine Triple.intro fun labels s ⟨hlab, hrbx, hle, hrdx, hrax⟩ => ?_
  subst hlab
  have hlt : k ≠ 0 → s.regs.rdx.toNat * s.regs.rdx.toNat < 2 ^ 64 := by
    intro _
    rw [hrdx, pow_sq]
    calc 2 ^ 2 ^ (rbx0 - k + 1)
        ≤ 2 ^ 2 ^ rbx0 :=
          Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
      _ < 2 ^ 64 := hbound
  have hsq : k ≠ 0 → s.regs.rdx.toNat * s.regs.rdx.toNat = 2 ^ 2 ^ (rbx0 - (k - 1)) := by
    intro hk
    rw [hrdx, pow_sq, show rbx0 - (k - 1) = rbx0 - k + 1 from by omega]
  vcgen simplifying_assumptions with finish

/-- From the exit label the tail carries the answer to the end of the text. -/
private theorem p3_finish (rbx0 : Nat) (E : MachineState → Prop) (st : MachineState)
    (h : st.2 = p3.labels.label "_end"
      ∧ st.1.regs.rdx.toNat = 2 ^ 2 ^ rbx0 ∧ st.1.regs.rax = 0) :
    Eventually (Program.runStep p3 E)
      (fun s => s.1.regs.rdx.toNat = 2 ^ 2 ^ rbx0 ∧ s.1.regs.rax = 0) st := by
  obtain ⟨m, pc⟩ := st
  obtain ⟨hpc, hrdx, hrax⟩ := h
  simp only at hpc hrdx hrax
  subst hpc
  refine Eventually.enter p3_end_segment ?_
  vcgen simplifying_assumptions
  with_reducible exact Eventually.done _ ⟨hrdx, hrax⟩

/-- A run of `p3` from a machine whose `rax` is clear reaches a state where
`rdx` holds `2 ^ 2 ^ rbx` and `rax` is clear again. `E` is arbitrary because
the run never leaves the program text. -/
theorem p3_correct (d : MachineData) (h_bounds : p3_spec d < 2 ^ 64)
    (h_rax : d.regs.rax = 0) (E : MachineState → Prop) :
    Eventually (Program.runStep p3 E)
      (fun st => st.1.regs.rdx.toNat = p3_spec d ∧ st.1.regs.rax = 0)
      (d, layout.start) := by
  simp only [p3_spec] at h_bounds ⊢
  refine Eventually.enter p3_entry_segment ?_
  vcgen [p3_loop_spec p3.labels d.regs.rbx.toNat d.regs.rbx.toNat h_bounds]
    simplifying_assumptions
  · grind
  · rename_i st
    intro hst
    refine ⟨fun hnil => absurd hnil (p3_exits_inText d.regs.rbx.toNat st
      (hst.elim (fun a => Or.inl a.2.1) (fun b => Or.inr b.2))), fun _ => ?_⟩
    obtain ⟨m, pc⟩ := st
    rcases hst with ⟨hne, hpc, hinv⟩ | ⟨h0, hpc, hrdx, hrax⟩
    · simp only at hpc hinv
      subst hpc
      exact Eventually.loop p3_start_segment
        (fun k => p3_loop_spec p3.labels d.regs.rbx.toNat k h_bounds _)
        (fun st h => p3_exits_inText d.regs.rbx.toNat st h)
        (fun st hx => p3_finish d.regs.rbx.toNat E st hx) _ m hinv
    · exact p3_finish d.regs.rbx.toNat E _ ⟨hpc, hrdx, hrax⟩

/-- `p3_correct` read as the omni-semantics judgment of `Kraken.OmniSemantics`:
a run of the laid-out program from `(d, layout.start)` reaches a state where
`rdx` holds `2 ^ 2 ^ rbx` and `rax` is clear. The run never leaves the program
text, so its exits land in `False` and drop out. -/
theorem p3_correct_run (d : MachineData) (h_bounds : p3_spec d < 2 ^ 64)
    (h_rax : d.regs.rax = 0) :
    Eventually (straightlineStep (layout p3))
      (fun s => s.1.regs.rdx.toNat = p3_spec d ∧ s.1.regs.rax = 0)
      (d, layout.start) :=
  (Program.run_sound (p3_correct d h_bounds h_rax (fun _ => False))).mono
    (fun _ _ hst => hst) (fun _ hs => hs.elim id False.elim)

end Proof
