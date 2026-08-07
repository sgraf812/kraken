/-
Weakest preconditions on the deep embedding. The program of a triple is the
sized directive segment that `Executable.directivesFromAddress` yields, and
its predicate transformer runs the baseline omni-semantics: the wp of a
segment `ds` at `(env, rip, s)` demands `Effects.All` of the postcondition
over `Directives.interp ds s rip`, applied at each exit `(pc', s')` with the
exit's program counter in the rip slot. The baseline delivers a jump out of
the segment and running past its final directive to the same continuation, so
every exit reaches the success postcondition and the transformer is constant
in the exception postcondition. `straightlineStep_of_wp` converts the
transformer into the judgment that `Eventually` composes.
-/
import Kraken.OmniSemantics
import Kraken.X64M

open Std.Internal.Do

/-- `Effects.All` is monotone in the postcondition. -/
theorem Effects.All.mono {p q : MachineState → Prop} (h : ∀ st, p st → q st) :
    ∀ e : Effects, e.All p → e.All q := by
  intro e
  induction e with
  | done a => exact h a
  | unimplemented _ => exact id
  | nonmem_load _ _ _ _ => exact id
  | nonmem_store _ _ _ _ => exact id
  | undefined _ ih => exact fun hp v => ih v (hp v)
  | require_read_access _ _ _ ih => exact fun hp => ih () hp
  | require_write_access _ _ _ ih => exact fun hp => ih () hp
  | require_exec_access _ _ ih => exact fun hp => ih () hp

/-- The predicate transformer of a straightline segment: every resolution of
the baseline omni-semantics reaches an exit `(pc', s')` satisfying the
postcondition at rip `pc'`. -/
def Directives.wpTrans (ds : List (Directive × Nat)) :
    PredTrans (Kraken.Env → Int64 → MachineData → Prop) (X64Exit → MachineData → Prop) Unit :=
  ⟨fun Q _E env rip s =>
    (@Directives.interp env.labels ds s rip (fun pc s' => .done (s', pc))).All
      (fun st => Q () env st.2 st.1)⟩

instance instWPDirectives :
    WP (List (Directive × Nat)) Unit (Kraken.Env → Int64 → MachineData → Prop)
      (X64Exit → MachineData → Prop) where
  wpTrans := Directives.wpTrans
  wp_trans_monotone _ _ _ _ _ _ hQ := fun env _ _ =>
    Effects.All.mono (fun st => hQ () env st.2 st.1) _

@[simp] theorem Directives.wp_nil (Q : Unit → Kraken.Env → Int64 → MachineData → Prop)
    (E : X64Exit → MachineData → Prop) (env : Kraken.Env) (rip : Int64) (s : MachineData) :
    wp ([] : List (Directive × Nat)) Q E env rip s = Q () env rip s := rfl

/-- A segment triple establishes the omni-semantics straightline judgment: the
segment at `pc` is the wp's program, the judgment's postcondition is the wp's,
read off the rip and machine slots at the exit. -/
theorem straightlineStep_of_wp [Layout] {e : Executable} {s : MachineData} {pc : Int64}
    {post : MachineState → Prop} {n : Nat} {E : X64Exit → MachineData → Prop}
    (h : wp (e.directivesFromAddress pc) (fun _ _ pc' s' => post (s', pc')) E ⟨e.labels, n⟩ pc s) :
    straightlineStep e (s, pc) post :=
  h
