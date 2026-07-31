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

/-- Reading the register just written, with no condition to discharge. -/
theorem get64_set64_self (s : Reg64s) (r : Reg64) (v : Width.W64.type) :
    (s.set64 r v).get64 r = v := by
  cases r <;> simp [Reg64s.set64, Reg64s.get64]

/-- Writing a register that is written again later leaves no trace. Without
this the value of a state's register file is a write chain as long as the
program, and every read has to look through all of it. -/
theorem set64_set64_self (s : Reg64s) (r : Reg64) (v w : Width.W64.type) :
    (s.set64 r v).set64 r w = s.set64 r w := by
  cases r <;> simp [Reg64s.set64]

/-- Reassociation, so a chain over a symbolic start presents adjacent literals
to `evalGround`. -/
theorem add_assoc_rev {w : Nat} (a b c : BitVec w) : a + (b + c) = a + b + c :=
  (BitVec.add_assoc a b c).symm

/-- The rewrite lemmas the chain's values reduce with. Ground arithmetic is
left to `evalGround`, conditions to `simpControl` and `reduceGroundIte`. -/
def lemmaNames : Array Name := #[
  ``Int64.toBitVec_ofNat, ``BitVec.ofNat_eq_ofNat, ``BitVec.setWidth_eq,
  ``get64_set64_self, ``Reg64s.get64_set64, ``set64_set64_self,
  ``Reg64s.rax_set64, ``Reg64s.rbx_set64, ``Reg64s.rcx_set64, ``Reg64s.rdx_set64, ``Reg64s.rsi_set64, ``Reg64s.rdi_set64, ``Reg64s.rbp_set64, ``Reg64s.r8_set64, ``Reg64s.r9_set64, ``Reg64s.r10_set64, ``Reg64s.r11_set64, ``Reg64s.r12_set64, ``Reg64s.r13_set64, ``Reg64s.r14_set64, ``Reg64s.r15_set64,
  ``BitVec.add_zero, ``BitVec.unsigned_eq, ``BitVec.toNat_ofNat,
  ``Nat.zero_mod, ``Int.add_zero, ``Int.cast_ofNat_Int, ``BitVec.unsigned_eq, ``bne_self_eq_false, ``Bool.toNat_false ]

/-- Reassociate a literal-prefixed sum so the two literals become adjacent.

A simproc rather than a rewrite rule because reassociation is an
AC-permutation, which the rewriter only applies when it decreases the term
order; here it always pays, since `evalGround` collapses the pair at once. -/
def collapseAdd : Simproc := fun e => do
  let_expr HAdd.hAdd _ _ _ _ a rest := e | return .rfl
  let_expr HAdd.hAdd _ _ _ _ b c := rest | return .rfl
  let some _ ← getBitVecValue? a | return .rfl
  let some _ ← getBitVecValue? b | return .rfl
  let proof ← mkAppM ``add_assoc_rev #[a, b, c]
  let e' ← Sym.share (← mkAdd (← mkAdd a b) c)
  return .step e' proof

/-- Decide an equality between two constructors, so that `Sym`'s own
`simpIte` sees a condition that became `True`/`False` and rewrites the
conditional with its `ite_cond_eq_true`/`ite_cond_eq_false` proof term. -/
def reduceCtorEq : Simproc := fun e => do
  let_expr Eq _ l r := e | return .rfl
  unless l.isConst && r.isConst do return .rfl
  unless (← isConstructorApp l) && (← isConstructorApp r) do return .rfl
  -- Return the shared `True`/`False`: `simpIte` tests them with pointer
  -- equality, so a freshly built constant leaves the conditional standing.
  if l == r then
    return .step (← getTrueExpr) (← mkAppM ``eq_self #[l])
  else
    -- `noConfusion` derives the disequality structurally. Deciding it instead
    -- would make the kernel evaluate the `Decidable` instance to check the
    -- proof, which is the work this is meant to avoid.
    let hne ← withLocalDeclD `h e fun h => do
      mkLambdaFVars #[h] (← mkNoConfusion (mkConst ``False) h)
    return .step (← getFalseExpr) (← mkAppM ``eq_false #[hne])

/-- Substitution built from the goal's equation hypotheses, keyed by pointer. -/
abbrev SubstEnv := Lean.PHashMap ExprPtr (Expr × Expr)

/-- Rewrite a state component to its defining value in one hash probe. -/
def substSimproc (env : SubstEnv) : Simproc := fun e => do
  match env.find? { expr := e } with
  | some (rhs, h) => return .step rhs h
  | none => return .rfl

/-- Collect the equation hypotheses in declaration order. -/
def collectEqs (mvarId : MVarId) : SymM (Array (Expr × Expr × Expr)) := mvarId.withContext do
  let mut eqs := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail || d.value?.isSome then continue
    if let some (_, lhs, rhs) := d.type.eq? then
      eqs := eqs.push (lhs, rhs, d.toExpr)
  return eqs

/--
Fold the chain component by component, asserting each folded equation as a
hypothesis.

Each step's right-hand side mentions the previous state's component twice (the
register file as write base and under the read), so inlining the derived proof
at its use sites doubles the proof tree per instruction: the certificate's DAG
stays linear while its tree is 2^n, and the kernel pays in between because its
instantiations produce fresh, unshared copies. Asserting `s_k.regs = v_k` into
the context makes every later use an atomic fvar reference: each proof appears
once, and sharing goes through the local context, which the kernel respects.
-/
def foldGoal (mvarId : MVarId) : MetaM (Option MVarId) := SymM.run do
  let mut mvarId ← preprocessMVar mvarId
  let eqs ← collectEqs mvarId
  let mut thms : Theorems := {}
  for n in lemmaNames do
    thms := thms.insert (← mkTheoremFromDecl n)
  let mkMethods (env : SubstEnv) : Methods :=
    { pre := simpControl
      post := substSimproc env >> collapseAdd >> reduceCtorEq >> evalGround >> thms.rewrite }
  let mut values : SubstEnv := {}
  let mut state : Sym.Simp.State := {}
  let mut nStep := 0
  for (lhs, rhs, h) in eqs do
    let (r, state') ← SimpM.run (Sym.Simp.simp rhs) (mkMethods values) { maxSteps := 100000 } state
    state := state'
    match r with
    | .rfl .. =>
      -- The hypothesis is already in folded form; its fvar is the shared proof.
      values := values.insert { expr := lhs } (rhs, h)
    | .step rhs' hr .. =>
      nStep := nStep + 1
      let prf ← Sym.Simp.mkEqTrans lhs rhs h rhs' hr
      let ty ← Sym.share (← mkEq lhs rhs')
      -- `define`, not `assert`: an asserted hypothesis becomes `?goal prf`, and
      -- instantiating that metavariable beta-reduces, splicing `prf` back into
      -- every use site. A `let` survives instantiation, so the proof appears
      -- once and uses stay atomic.
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

end Kraken.Fold

/-- Fold a verification condition along its state chain. -/
elab "kfold" : tactic => liftMetaTactic1 Kraken.Fold.foldGoal

/-- Fold a verification condition, drop the equations it consumed, and decide
what is left. -/
macro "kfold_discharge" : tactic => `(tactic| (kfold <;> clear_dead <;> bv_decide))
