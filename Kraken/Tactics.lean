/-
The `easm` grind-mode tactic: discharge a `Mem.loadInt … = some ?i` side goal by
reading the value off the internalized local context.

`vcgen` applies the memory primitive specs with an undetermined witness `?i`,
emitting a side goal `lhs = some ?i` (an equality with an assignable metavariable
on one side). The internalized local context holds the `h_load` facts and the
address/state bridges, so `lhs` reduces to a constructor-headed `some V`. `easm`
performs that reduction (read-over-write projections plus the local equations),
assigns `?i := V` by definitional unification, and closes the goal by the
reduction proof. The assignment is visible to the sibling continuation VC, which
shares the metavariable.
-/
import Kraken.OmniSemantics
import Kraken.AccessorSpecs
import Std.Tactic.Do

open Lean Meta
open Lean.Elab.Tactic.Grind

namespace Kraken

/-- Read-over-write projections and the address/data-memory reductions that
`easm` uses to expose the `Mem.loadInt`/`Mem.storeInt` skeleton of the queried
side before the `h_load` facts fire. -/
private def projLemmas : List Name :=
  [``MachineData.dmem_setDmem, ``MachineData.regs_setDmem, ``MachineData.status_setDmem,
   ``MachineData.zmms_setDmem, ``MachineData.dmem_setReg, ``MachineData.regs_setReg,
   ``MachineData.status_setReg, ``MachineData.zmms_setReg, ``MachineData.dmem_mk,
   ``MachineData.regs_mk, ``MachineData.status_mk, ``MachineData.zmms_mk,
   ``Addr.eval_setDmem]

/-- Effective-address canonicalization used in `easm`'s second normalization pass:
unfold `Addr.eval`, resolve register reads over writes, and push the
`UInt64`/`BitVec`/`Int64` coercions, so an indexed load address (whose base
register a preceding `lea` overwrote) matches the separation-derived address. -/
private def addrUnfolds : List Name := [``Addr.eval, ``Reg64s.get64]
private def addrLemmas : List Name :=
  [``Reg64s.get64_set64, ``Reg64s.get_low64, ``Reg64s.set_low64,
   ``Int64.toBitVec_lit, ``BitVec.ofInt_add, ``BitVec.ofInt_mul, ``BitVec.ofInt_toInt,
   ``BitVec.ofInt_toInt_int64, ``BitVec.add_zero,
   ``BitVec.ofInt_neg, ``BitVec.ofInt_ofNat, ``UInt64.toBitVec_sub, ``UInt64.toBitVec_ofNat,
   ``UInt64.ofBitVec_toBitVec, ``UInt64.ofBitVec_add, ``UInt64.ofBitVec_sub,
   ``UInt64.ofBitVec_ofNat]

/-- Whether `e` is headed by a constructor or is a literal. -/
private def isCtorHeaded (e : Expr) : MetaM Bool := do
  if e.isLit then return true
  let .const declName _ := e.getAppFn | return false
  return (← getEnv).find? declName |>.any fun
    | .ctorInfo _ => true
    | _ => false

/-- Discharge an `_ = some ?i` side goal by reading its value off the local
context. Returns `true` on success, having assigned `?i` and closed `mvarId`. -/
private def easmCore (mvarId : MVarId) : MetaM Bool := mvarId.withContext do
  let target ← instantiateMVars (← mvarId.getType)
  let some (_, lhs, rhs) := target.eq? | return false
  -- Exactly one side carries an assignable metavariable: that side is the query,
  -- the other is the `known` term whose value we read from the context.
  let (known, query, knownIsLhs) ←
    if rhs.hasExprMVar && !lhs.hasExprMVar then pure (lhs, rhs, true)
    else if lhs.hasExprMVar && !rhs.hasExprMVar then pure (rhs, lhs, false)
    else return false
  -- Fire only when the metavariable side is constructor-headed (e.g. `some ?i`)
  -- or a bare metavariable. A goal like `<projection with ?i> = 99` is left to the
  -- continuation discharge.
  unless query.isMVar || (← isCtorHeaded query) do return false
  -- Simp set: the read-over-write projections plus every closed propositional
  -- hypothesis. The `h_load` facts rewrite `Mem.loadInt … → some V`; the state
  -- equalities and address bridges align the load's memory and address with them.
  -- The first pass keeps `Addr.eval` folded (matching a folded `h_load`); if the
  -- queried side does not reduce to a value, a second pass canonicalizes the
  -- address so an indexed load matches its separation-derived form.
  let mkThms (thmExtra unfoldExtra : List Name) : MetaM SimpTheorems := do
    let mut thms : SimpTheorems := {}
    for n in projLemmas ++ thmExtra do thms ← thms.addConst n
    for n in unfoldExtra do thms ← thms.addDeclToUnfold n
    for decl in (← getLCtx) do
      unless decl.isImplementationDetail do
        if (← isProp decl.type) && !decl.type.hasExprMVar then
          -- Some hypotheses (e.g. inequalities) are not orientable as simp lemmas.
          thms ← try thms.add (.fvar decl.fvarId) #[] (mkFVar decl.fvarId) catch _ => pure thms
    return thms
  let ctx1 ← Simp.mkContext (simpTheorems := #[← mkThms [] []]) (congrTheorems := ← getSimpCongrTheorems)
  let mut res := (← simp known ctx1).1
  unless ← isCtorHeaded res.expr do
    let ctx2 ← Simp.mkContext (simpTheorems := #[← mkThms addrLemmas addrUnfolds])
      (congrTheorems := ← getSimpCongrTheorems)
    res := (← simp known ctx2).1
  let knownV := res.expr  -- expected `some V`
  unless ← isCtorHeaded knownV do return false
  -- `hKnown : known = knownV`; `knownV` is constructor-headed, so unifying it with
  -- the query pins the metavariable (`some ?i` ↦ `some V`).
  let hKnown ← res.proof?.getDM (mkEqRefl known)
  unless ← withAssignableSyntheticOpaque (isDefEq query knownV) do return false
  mvarId.assign (← if knownIsLhs then pure hKnown else mkEqSymm hKnown)
  return true

syntax (name := easmStx) "easm" : grind

@[grind_tactic easmStx]
def evalEasm : GrindTactic := fun _stx => do
  let goal ← getMainGoal
  unless ← liftMetaM (easmCore goal.mvarId) do
    throwError "easm: goal is not an assignable `_ = some ?i` reducible from the context"
  replaceMainGoal []

end Kraken
