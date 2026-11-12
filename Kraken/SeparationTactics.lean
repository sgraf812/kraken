module

import Kraken.Separation
public meta import Lean.Elab.Tactic
public meta import Lean.Meta.Tactic.AC

public meta section

open Lean Elab Tactic Meta

namespace Kraken.Tactic

/-- The separation algebra `ecancel` cancels over: the connective and its
unit by head constant, the carrier the instance serves, and how to rebuild a
clause list at a predicate type. Two optional hooks carry domain knowledge:
`normalize` brings both sides to a common spelling before matching and
returns the equation it used, and `split?` pays an atom that has no partner
by splitting a closed atom at an address, returning the split spelling, its
equation and a side goal. -/
structure SepOps where
  sep : Name
  emp : Name
  isCarrier : Expr → MetaM Bool
  mkSep : Expr → Expr → Expr → MetaM Expr
  mkEmp : Expr → MetaM Expr
  normalize : Expr → MetaM (Expr × Option Expr) := fun e => pure (e, none)
  split? : Expr → Expr → MetaM (Option (Expr × Expr × MVarId)) := fun _ _ => pure none
  /-- The address of an atom, if it has one; `split?` is tried at it. -/
  addr? : Expr → Option Expr := fun _ => none

/-- The algebra of predicates over a byte memory, `Std.ExtHashMap.sep`. -/
def extHashMapOps : SepOps where
  sep := ``Std.ExtHashMap.sep
  emp := ``Std.ExtHashMap.emp
  isCarrier := fun ty => do return (← whnf ty).isForall
  mkSep := fun _ p q => mkAppM ``Std.ExtHashMap.sep #[p, q]
  mkEmp := fun predType => do
    let predType ← whnf predType
    withLocalDeclD `m predType.bindingDomain! fun m => do
      let body ← mkAppM ``Std.ExtHashMap.emp #[m]
      mkLambdaFVars #[m] body (etaReduce := true)

/-- The registered algebras, tried in order by `ecancel`. -/
initialize sepOpsRef : IO.Ref (List SepOps) ← IO.mkRef [extHashMapOps]

private partial def denoteClauses (ops : SepOps) (predType : Expr) : List Expr → MetaM Expr
  | [] => ops.mkEmp predType
  | [p] => pure p
  | p :: ps => do ops.mkSep predType p (← denoteClauses ops predType ps)

partial def reifyClauses (ops : SepOps) (e : Expr) : MetaM (List Expr) := do
  let e ← instantiateMVars e
  if e.getAppFn.constName? == some ops.emp then
    return []
  if e.getAppFn.constName? == some ops.sep then
    let args := e.getAppArgs
    let p ← reifyClauses ops args[args.size - 2]!
    let q ← reifyClauses ops args[args.size - 1]!
    return p ++ q
  return [e]

private def assignNaked (ops : SepOps) (predType : Expr) (lhs rhs : List Expr) : MetaM Bool := do
  let [.mvar mvarId] := lhs | return false
  isDefEq (.mvar mvarId) (← denoteClauses ops predType rhs)

private def reduceProjectionApp (e : Expr) : MetaM Expr := do
  let some declName := e.getAppFn.constName? | return e
  let some info ← getProjectionFnInfo? declName | return e
  if info.fromClass then return e
  let some unfolded ← unfoldDefinition? e | return e
  let some fn ← reduceProj? unfolded.getAppFn | return e
  return mkAppN fn unfolded.getAppArgs

-- fuel: bound definitional unfolding to avoid expensive general reduction.
private partial def matchClosed (lhs rhs : Expr) (fuel : Nat := 2) : MetaM Bool := do
  let lhs ← reduceProjectionApp lhs
  let rhs ← reduceProjectionApp rhs
  if lhs == rhs then return true
  if lhs.getAppFn == rhs.getAppFn then
    let lhsArgs := lhs.getAppArgs
    let rhsArgs := rhs.getAppArgs
    unless lhsArgs.size == rhsArgs.size do return false
    for lhsArg in lhsArgs, rhsArg in rhsArgs do
      unless ← matchClosed lhsArg rhsArg fuel do return false
    return true
  if fuel == 0 then return false
  if let some lhs ← unfoldDefinition? lhs then
    if ← matchClosed lhs rhs (fuel - 1) then return true
  if let some rhs ← unfoldDefinition? rhs then
    if ← matchClosed lhs rhs (fuel - 1) then return true
  return false

private def matchAtom (lhs rhs : Expr) : MetaM Bool := do
  if lhs == rhs then return true
  if lhs.hasExprMVar || rhs.hasExprMVar then isDefEq lhs rhs
  else matchClosed lhs rhs

private def isNakedMVar : Expr → Bool
  | .mvar _ => true
  | _ => false

-- Closed clauses can be cancelled greedily: unlike clauses containing
-- metavariables, matching them cannot constrain a later cancellation choice.
-- `matchFn` decides a pair; the syntactic pass runs before the unfolding one,
-- so a pair that agrees on the nose never pays for unfolding a mismatch.
private partial def cancelClosedClauses (matchFn : Expr → Expr → MetaM Bool) :
    List Expr → List Expr → MetaM (List Expr × List Expr)
  | [], rhs => return ([], rhs)
  | l :: ls, rhs => do
    if l.hasExprMVar then
      let (ls, rhs) ← cancelClosedClauses matchFn ls rhs
      return (l :: ls, rhs)
    let some j ← rhs.toArray.findIdxM? (fun r => do
        if r.hasExprMVar then return false
        matchFn l r) | do
      let (ls, rhs) ← cancelClosedClauses matchFn ls rhs
      return (l :: ls, rhs)
    cancelClosedClauses matchFn ls (rhs.eraseIdx j)

private partial def cancelClauses (ops : SepOps) (predType : Expr) (lhs rhs : List Expr) : MetaM Bool := do
  let (lhs, rhs) ← cancelClosedClauses (fun l r => pure (l == r)) lhs rhs
  let (lhs, rhs) ← cancelClosedClauses (fun l r => matchClosed l r) lhs rhs
  if lhs.isEmpty && rhs.isEmpty then return true
  for i in List.range lhs.length do
    for j in List.range rhs.length do
      let l := lhs[i]!
      let r := rhs[j]!
      -- Closed matches have already been removed. A naked metavariable is
      -- reserved for assignment to the conjunction of all remaining clauses
      -- below.
      if (l.hasExprMVar || r.hasExprMVar) && !isNakedMVar l && !isNakedMVar r then
        let matched ← commitWhen do
          unless ← matchAtom l r do return false
          -- Matching may instantiate metavariables in the remaining clauses.
          let lhs ← (lhs.eraseIdx i).mapM instantiateMVars
          let rhs ← (rhs.eraseIdx j).mapM instantiateMVars
          cancelClauses ops predType lhs rhs
        if matched then return true
  assignNaked ops predType lhs rhs <||> assignNaked ops predType rhs lhs

private partial def alignClauses : List Expr → List Expr → MetaM (Option (List Expr))
  | [], [] => return some []
  | lhs, r :: rs => do
    -- Alignment tolerates spelling differences the cancellation phase resolved
    -- by unification: fall back to reducible defeq, and only when no atom
    -- matches syntactically, so the common case pays nothing.
    let i? := lhs.toArray.findIdx? (· == r)
    let i? ← match i? with
      | some i => pure (some i)
      | none => lhs.toArray.findIdxM? (fun l => matchAtom l r)
    let some i ← (match i? with
      | some i => pure (some i)
      | none => lhs.toArray.findIdxM? (fun l => isDefEq l r))
      | return none
    let some rest ← alignClauses (lhs.eraseIdx i) rs | return none
    return some (lhs[i]! :: rest)
  | _, _ => return none

/--
Rebuilds `e` while preserving its sep/emp tree structure and replacing each
atomic leaf, from left to right, with the next entry in `clauses`.
Returns none if there are not enough clauses to replace every atomic leaf.
Returns some (rebuilt expr, unused clauses) otherwise.
-/
private partial def canonicalize (ops : SepOps) (e : Expr) (clauses : List Expr) :
    MetaM (Option (Expr × List Expr)) := do
  let e ← instantiateMVars e
  if e.getAppFn.constName? == some ops.emp then
    return some (e, clauses)
  if e.getAppFn.constName? == some ops.sep then
    let args := e.getAppArgs
    let some (p, clauses) ← canonicalize ops args[args.size - 2]! clauses | return none
    let some (q, clauses) ← canonicalize ops args[args.size - 1]! clauses | return none
    -- Rebuild with the operator as spelled, so the AC proof is stated at the
    -- goal's own type and instances.
    return some (mkAppN e.getAppFn (args.extract 0 (args.size - 2) ++ #[p, q]), clauses)
  return match clauses with
  | c :: clauses => some (c, clauses)
  | [] => none

private def proveSeqEq (ops : SepOps) (lhs rhs : Expr) : MetaM (Option Expr) :=
  commitWhenSomeNoEx? do
    let lhs ← instantiateMVars lhs
    let rhs ← instantiateMVars rhs
    let lhsClauses ← reifyClauses ops lhs
    let rhsClauses ← reifyClauses ops rhs
    let some rhsClauses ← alignClauses lhsClauses rhsClauses | return none
    let some (lhs, []) ← canonicalize ops lhs lhsClauses | return none
    let some (rhs, []) ← canonicalize ops rhs rhsClauses | return none
    let proof ← mkFreshExprMVar (← mkEq lhs rhs)
    Lean.Meta.AC.rewriteUnnormalizedRefl proof.mvarId!
    return some (← instantiateMVars proof)

/-- Prove `lhs = rhs` for two clause lists equal up to AC, assigning the
metavariables of open atoms by matching and a naked metavariable to the
remaining clauses. -/
def solveSepEq (ops : SepOps) (lhs rhs : Expr) : MetaM (Option Expr) := do
  let lhs ← instantiateMVars lhs
  let rhs ← instantiateMVars rhs
  if lhs == rhs then
    return some (← mkEqRefl lhs)
  let predType ← inferType lhs
  let lhsClauses ← reifyClauses ops lhs
  let rhsClauses ← reifyClauses ops rhs
  unless ← cancelClauses ops predType lhsClauses rhsClauses do return none
  proveSeqEq ops lhs rhs

private def solveFromHypothesis (ops : SepOps) (target : Expr) (localDecl : LocalDecl) : MetaM (Option Expr) := do
  let target ← instantiateMVars target
  let hypType ← instantiateMVars localDecl.type
  unless hypType.isApp do return none
  let targetFn := target.appFn!
  let targetArg := target.appArg!
  let hypFn := hypType.appFn!
  let hypArg := hypType.appArg!
  unless ← matchAtom (← reduceProjectionApp targetArg) (← reduceProjectionApp hypArg) do
    return none
  let some hSeps ← solveSepEq ops hypFn targetFn | return none
  let hFunEq ← mkAppM ``congrFun #[hSeps, hypArg]
  return some (← mkAppM ``Eq.mp #[hFunEq, localDecl.toExpr])

syntax (name := ecancel) "ecancel" : tactic

@[tactic ecancel]
def evalEcancel : Tactic :=
  fun _stx : Syntax => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  -- Existential witnesses introduced by tactics are synthetic-opaque goals;
  -- `ecancel` intentionally instantiates them as part of cancellation.
  -- the algebra of the goal's carrier
  let carrierOf (e : Expr) : MetaM (Option SepOps) := do
    let ty ← inferType e
    for ops in ← sepOpsRef.get do
      if ← ops.isCarrier ty then return some ops
    return none
  let solved ← withConfig (fun config => { config with assignSyntheticOpaque := true }) do
    if target.isAppOfArity ``Eq 3 then
      let args := target.getAppArgs
      if let some ops ← carrierOf args[1]! then
        if let some proof ← solveSepEq ops args[1]! args[2]! then
          goal.assign proof
          return true
    -- An entailment between two clause lists that are equal up to AC.
    if target.isAppOfArity ``Lean.Order.PartialOrder.rel 4 then
      let args := target.getAppArgs
      if let some ops ← carrierOf args[2]! then
        if let some proof ← solveSepEq ops args[2]! args[3]! then
          goal.assign (← mkAppOptM ``Lean.Order.PartialOrder.rel_of_eq
            #[args[0]!, args[1]!, args[2]!, args[3]!, proof])
          return true
    if target.isApp then
      if let some ops ← carrierOf target.appFn! then
        for localDecl? in (← getLCtx).decls.toArray.reverse do
          if let some localDecl := localDecl? then
            if let some proof ← solveFromHypothesis ops target localDecl then
              goal.assign proof
              return true
    return false
  unless solved do
    throwError "ecancel: could not automatically solve goal {target}"
end Kraken.Tactic
