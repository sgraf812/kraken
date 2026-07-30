/-
`kfold`: fold a verification condition along its state chain in one pass.

Symbolic execution emits, per program step, a fresh state and one equation per
state component, each defined from the previous state. Discharging that with
`simp only [*]` hands the simplifier every equation as a rewrite rule, so rule
matching is linear in the chain length at every rewrite step.

Since `Sym.preprocessMVar` makes every term pointer-canonical, those equations
form a substitution keyed by pointer, and looking one up is a single hash
probe. `Sym.Simp` then expands each component exactly once as it traverses the
goal bottom-up, caching by pointer, and collapses the value on the spot.
-/
import Lean
import Kraken.AccessorSpecs
import KrakenTactics.ClearDead
import Std.Tactic.BVDecide

open Lean Meta Elab Tactic Sym Sym.Simp

namespace Kraken.Fold

/-- The rewrite lemmas the chain's values reduce with. Ground arithmetic is
left to `evalGround`, and conditions to `simpControl`. -/
def lemmaNames : Array Name := #[
  ``Int64.toBitVec_ofNat, ``BitVec.ofNat_eq_ofNat, ``BitVec.setWidth_eq,
  ``Reg64s.get64_set64,
  ``BitVec.add_zero, ``BitVec.unsigned_eq, ``BitVec.toNat_ofNat,
  ``Nat.zero_mod, ``Int.add_zero, ``bne_self_eq_false, ``Bool.toNat_false ]

/-- Reassociation, so a chain over a symbolic start presents adjacent literals
to `evalGround`. -/
theorem add_assoc_rev {w : Nat} (a b c : BitVec w) : a + (b + c) = a + b + c :=
  (BitVec.add_assoc a b c).symm

/-- Reassociate a literal-prefixed sum so the two literals become adjacent.

Stated as a simproc rather than a rewrite rule because reassociation is an
AC-permutation, which the rewriter only applies when it decreases the term
order; here it always pays, since `evalGround` collapses the pair immediately.
-/
def collapseAdd : Simproc := fun e => do
  let_expr HAdd.hAdd _ _ _ _ a rest := e | return .rfl
  let_expr HAdd.hAdd _ _ _ _ b c := rest | return .rfl
  let some _ ← getBitVecValue? a | return .rfl
  let some _ ← getBitVecValue? b | return .rfl
  let proof ← mkAppM ``add_assoc_rev #[a, b, c]
  let ab ← mkAdd a b
  let e' ← Sym.share (← mkAdd ab c)
  return .step e' proof

/-- Substitution built from the goal's equation hypotheses, keyed by pointer. -/
abbrev SubstEnv := Lean.PHashMap ExprPtr (Expr × Expr)

/-- Rewrite a state component to its defining value in one hash probe. -/
def substSimproc (env : SubstEnv) : Simproc := fun e => do
  match env.find? { expr := e } with
  | some (rhs, h) => return .step rhs h
  | none => return .rfl

/-- Collect `lhs = rhs` hypotheses into a pointer-keyed substitution. -/
def mkSubstEnv (mvarId : MVarId) : SymM SubstEnv := mvarId.withContext do
  let mut env : SubstEnv := {}
  for d in ← getLCtx do
    if d.isImplementationDetail || d.value?.isSome then continue
    if let some (_, lhs, rhs) := d.type.eq? then
      env := env.insert { expr := lhs } (rhs, d.toExpr)
  return env

/-- Fold the goal along the state chain. -/
def foldGoal (mvarId : MVarId) : MetaM (Option MVarId) := SymM.run do
  let mvarId ← preprocessMVar mvarId
  let env ← mkSubstEnv mvarId
  let mut thms : Theorems := {}
  for n in lemmaNames do
    thms := thms.insert (← mkTheoremFromDecl n)
  let methods : Methods :=
    { pre := simpControl
      post := substSimproc env >> collapseAdd >> evalGround >> thms.rewrite }
  let target ← mvarId.withContext do instantiateMVars (← mvarId.getType)
  let (result, _) ← SimpM.run (Sym.Simp.simp target) methods { maxSteps := 1000000 } {}
  match ← result.toSimpGoalResult mvarId with
  | .closed => return none
  | .goal mvarId => return some mvarId
  | .noProgress => return some mvarId

end Kraken.Fold

/-- Fold a verification condition along its state chain. -/
elab "kfold" : tactic => liftMetaTactic1 Kraken.Fold.foldGoal

/-- Fold a verification condition, drop the equations it consumed, and decide
what is left. Clearing matters: the folded goal is small, but a solver that
processes the local context still pays for every equation in the chain. -/
macro "kfold_discharge" : tactic => `(tactic| (kfold; clear_dead; bv_decide))
