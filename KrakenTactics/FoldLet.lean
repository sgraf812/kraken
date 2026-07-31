/-
`kfold_let`: `kfold` for verification conditions produced by the let-form specs
of `KrakenTactics/LetSpecs.lean`.

Those conditions carry the state chain as nested record literals, so the
rewrite set gains the record-projection lemmas that turn a projection of a
literal back into the component it was built from, and the substitution
environment is seeded from `let`-declaration values as well as from equation
hypotheses.
-/
import Lean
import Kraken.AccessorSpecs
import KrakenTactics.LetSpecs
import KrakenTactics.ClearDead
import KrakenTactics.Fold
import Std.Tactic.BVDecide

open Lean Meta Elab Tactic Sym Sym.Simp

namespace Kraken.FoldLet

open Kraken.Fold

/-- `Kraken.Fold.lemmaNames` plus the record-projection lemmas, so a read of a
component of a state literal resolves to the write chain that literal carries. -/
def lemmaNames : Array Name :=
  Kraken.Fold.lemmaNames ++ #[
    ``MachineData.regs_mk, ``MachineData.zmms_mk, ``MachineData.status_mk, ``MachineData.dmem_mk,
    ``StatusFlags.cf_from_result ]

/-- Collect the substitution sources in declaration order: an equation
hypothesis contributes its two sides, a `let`-declaration its variable and
value. -/
def collectDefs (mvarId : MVarId) : SymM (Array (Expr × Expr × Expr)) := mvarId.withContext do
  let mut defs := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if let some v := d.value? then
      defs := defs.push (d.toExpr, v, ← Sym.mkEqRefl d.toExpr)
    else if let some (_, lhs, rhs) := d.type.eq? then
      defs := defs.push (lhs, rhs, d.toExpr)
  return defs

/-- Fold a let-form verification condition along its state chain. -/
def foldGoal (mvarId : MVarId) : MetaM (Option MVarId) := SymM.run do
  let mut mvarId ← preprocessMVar mvarId
  let defs ← collectDefs mvarId
  let mut thms : Theorems := {}
  for n in lemmaNames do
    thms := thms.insert (← mkTheoremFromDecl n)
  let mkMethods (env : SubstEnv) : Methods :=
    { pre := simpControl
      post := substSimproc env >> collapseAdd >> Kraken.Fold.reduceCtorEq >> evalGround >> thms.rewrite }
  let mut values : SubstEnv := {}
  let mut state : Sym.Simp.State := {}
  let mut nStep := 0
  for (lhs, rhs, h) in defs do
    let (r, state') ← SimpM.run (Sym.Simp.simp rhs) (mkMethods values) { maxSteps := 100000 } state
    state := state'
    match r with
    | .rfl .. =>
      values := values.insert { expr := lhs } (rhs, h)
    | .step rhs' hr .. =>
      nStep := nStep + 1
      let prf ← Sym.Simp.mkEqTrans lhs rhs h rhs' hr
      let ty ← Sym.share (← mkEq lhs rhs')
      let mvarId' ← mvarId.define ((`hfold).appendIndexAfter nStep) ty prf
      let (fvar, mvarId'') ← mvarId'.intro1P
      mvarId := mvarId''
      values := values.insert { expr := lhs } (rhs', .fvar fvar)
  let target ← mvarId.withContext do instantiateMVars (← mvarId.getType)
  let (result, _) ← SimpM.run (Sym.Simp.simp target) (mkMethods values) { maxSteps := 1000000 } state
  match ← result.toSimpGoalResult mvarId with
  | .closed => return none
  | .goal mvarId' => return some mvarId'
  | .noProgress => return some mvarId

end Kraken.FoldLet

/-- Fold a let-form verification condition along its state chain. -/
elab "kfold_let" : tactic => liftMetaTactic1 Kraken.FoldLet.foldGoal

/-- Fold a let-form verification condition, drop what it consumed, and decide
what is left. -/
macro "kfold_let_discharge" : tactic => `(tactic| (kfold_let <;> clear_dead <;> bv_decide))
