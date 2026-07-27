/-
Kraken - Proof Tactics

Straightline judgment over the `EStateM` instruction semantics, expressed with
the stock `WP`/`Triple` instance for `EStateM` from `Std.Internal.Do`.
-/

import Kraken.Semantics
import Std.Tactic.Do

open Std.Internal.Do

set_option mvcgen.warning false
set_option grind.warning false

-- PROOF INFRASTRUCTURE

abbrev Post {State : Type} := State → Prop

-- NOTE: 'initial' cannot be moved to the left of the colon as a parameter
-- because it varies in the recursive call in the 'step' constructor (it becomes 'mid').
inductive Eventually {State : Type} (trans : State → Post → Prop) (post : Post) : Post
  | done (initial: State):
      post initial →
      Eventually trans post initial
  | step (initial: State):
      (mid_p: Post) →
      trans initial mid_p →
      (forall (mid: State), mid_p mid → Eventually trans post mid) →
      Eventually trans post initial

theorem step_cps {State : Type} (trans : State → Post → Prop) (post : Post) (initial : State) :
  trans initial (fun mid => Eventually trans post mid) → Eventually trans post initial :=
  by
    intro
    apply Eventually.step
    <;> try assumption
    grind

theorem eventually_trans {State : Type} (trans : State → Post → Prop) (p q : Post) (initial : State)
  (e : Eventually trans p initial)
  (h : ∀ s, p s → Eventually trans q s) :
    Eventually trans q initial
  := by
    induction e with
    | done =>
        grind
    | step initial mid_p step_hyp rest_hyp ind_h =>
        apply Eventually.step
        <;> assumption

/-- Exception postcondition of a straightline run: a `jump` exit re-enters the
same postcondition at the jump target; every other exit is unreachable in
straightline register-only code. -/
def exitPost (post : MachineState → Prop) : X64Exit → MachineData → Prop
  | .jump pc, sd => post (sd, pc)
  | _, _ => False

/-- The straightline judgment: running `e` from `s.2` with initial state `s.1`
lands in `post`, whether it falls through (fall-through pc in the value
postcondition) or jumps (target pc in the exception postcondition). -/
def straightlineStep [Layout] (e : Executable) (s : MachineState) (post : @Post MachineState) : Prop :=
  ⦃fun sd => sd = s.1⦄
    (e.straightline s.2)
  ⦃fun pc sd => post (sd, pc); fun ex sd => exitPost post ex sd⦄

def step1 [Layout] (e : Executable) (s : MachineState) (post : @Post MachineState) : Prop :=
  ⦃fun sd => sd = s.1⦄
    (e.step s.2)
  ⦃fun pc sd => post (sd, pc); fun ex sd => exitPost post ex sd⦄
