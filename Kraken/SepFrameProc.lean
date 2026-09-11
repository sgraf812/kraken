/-
The frame inference procedure of the separation wp, with `ecancel` as its
engine. At a spec application `vcgen` hands over the goal's precondition and
the spec's precondition with its logical variables live;
`Kraken.Tactic.solveSepEq` cancels the spec's footprint out of the goal,
assigning the logical variables by matching and the remainder to the frame,
and certifies the split with one AC equation. `SepWP.split_of_pointwise`
turns that certificate into the split VC's proof, and `SepWP.frames`
discharges the frame-rule side goal for every program and frame.
-/
import Kraken.SepSpecs
import Lean.Elab.Tactic.VCGen.FrameProc

open Lean Meta Sym Sym.Internal Elab Tactic VCGen
open Std.WP
open Lean.Order
open scoped SepWP

namespace SepWP

/-- The `emp` frame acts as the identity, and so does its adjoint: the
wrappers the frame rule leaves at an `emp` framing collapse away. -/
@[simp] theorem frameOp_emp (P : Reg64s → RegZmms → StatusFlags → MProp 64) :
    SepWP.frameOp MProp.emp P = P := by
  funext r z f
  exact MProp.emp_sep (P r z f)

@[simp] theorem frameOpE_emp (E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64) :
    SepWP.frameOpE MProp.emp E = E := by
  funext a
  exact frameOp_emp (E a)

@[simp] theorem upperAdjoint_frameOp_emp (P : Reg64s → RegZmms → StatusFlags → MProp 64) :
    PreservesSup.upperAdjoint (SepWP.frameOp MProp.emp) P = P := by
  refine PartialOrder.rel_antisymm ?_ ?_
  · have h := PreservesSup.upperAdjoint_le (SepWP.frameOp MProp.emp) P
    rwa [frameOp_emp] at h
  · exact PreservesSup.le_upperAdjoint _ (PartialOrder.rel_of_eq (frameOp_emp P))

@[simp] theorem upperAdjoint_frameOpE_emp
    (E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64) :
    PreservesSup.upperAdjoint (SepWP.frameOpE MProp.emp) E = E := by
  refine PartialOrder.rel_antisymm ?_ ?_
  · have h := PreservesSup.upperAdjoint_le (SepWP.frameOpE MProp.emp) E
    rwa [frameOpE_emp] at h
  · exact PreservesSup.le_upperAdjoint _ (PartialOrder.rel_of_eq (frameOpE_emp E))

/-- The trivial split: frame `emp`, the goal precondition pays the spec. -/
theorem split_emp {P T : MProp 64} (h : P ⊑ T) : P ⊑ MProp.sep MProp.emp T :=
  PartialOrder.rel_trans h (PartialOrder.rel_of_eq (MProp.emp_sep T).symm)

/-- Chaining through a wand-composite spec: the goal's precondition splits
into the spec's footprint and a remainder, and the remainder enters the wand,
so the tail runs with the updated footprint next to the remainder. `hnext` is
the next wp goal. -/
theorem chain_wand {P fp R new T : MProp 64}
    (hc : P = MProp.sep fp R) (hnext : MProp.sep new R ⊑ T) :
    P ⊑ MProp.sep fp (MProp.wand new T) := by
  rw [hc]
  exact MProp.sep_mono_right fp (MProp.wand_intro hnext)

/-- Phase two. A wand-composite spec (`fp ∗ (new -∗ T)`) splits by `ecancel`:
the footprint cancels against the goal's precondition, the remainder becomes
the frame riding through the wand, and the wand's body is emitted as the next
wp goal. A spec without sep structure chains by a plain entailment subgoal.
The frame-rule frame is `emp` either way: the wand carries the real frame. -/
def sepFrameSplit (i : FrameInferenceInfo) (goal : FrameGoal) :
    Lean.Meta.Grind.GrindM FrameSplit := do
  let pre ← instantiateMVars i.pre
  let specPre ← instantiateMVars goal.specPre
  let mprop64 := mkApp (mkConst ``MProp) (mkNatLit 64)
  -- the frame rule contributes nothing; the wand carries the frame
  goal.frame.assign (← shareCommon (← mkAppOptM ``MProp.emp #[mkNatLit 64]))
  goal.footprint.assign (← shareCommon specPre)
  let preVCTy ← goal.preVC.getType
  goal.preVC.withContext do
    goal.preVC.assign (← mkAppOptM ``Lean.Order.PartialOrder.rel_refl
      #[none, none, preVCTy.appFn!.appArg!])
  let clauses ← Kraken.Tactic.reifyClauses specPre
  let (wands, fps) := clauses.partition (·.getAppFn.constName? == some ``MProp.wand)
  match wands, fps with
  | [wandAtom], [fp] => do
    -- fp ∗ (new -∗ T): cancel fp, the remainder R goes through the wand
    let new := wandAtom.appFn!.appArg!
    let T := wandAtom.appArg!
    let R ← mkFreshExprMVar mprop64
    let target ← mkAppM ``MProp.sep #[fp, R]
    let some hc ← withConfig (fun c => { c with assignSyntheticOpaque := true })
        (withTransparency .default (Kraken.Tactic.solveSepEq pre target))
      | throwError "sep frameproc: no footprint of{indentExpr fp}
in{indentExpr pre}"
    let R ← instantiateMVars R
    let nextTy ← mkAppNS (← mkAppNS i.le #[← mkAppM ``MProp.sep #[new, R]]) #[T]
    let hnext ← mkFreshExprSyntheticOpaqueMVar nextTy
    let chained ← mkAppM ``SepWP.chain_wand #[hc, hnext]
    let prf ← mkAppM ``SepWP.split_emp
      #[← mkAppM ``Lean.Order.PartialOrder.rel_trans #[chained, goal.specProof]]
    return { splitVCProof := prf, subgoals := [hnext.mvarId!] }
  | [], _ => do
    -- no wand: a register spec; chain by one entailment subgoal
    let subTy ← mkAppNS (← mkAppNS i.le #[pre]) #[specPre]
    let hsub ← mkFreshExprSyntheticOpaqueMVar subTy
    let prf ← mkAppM ``SepWP.split_emp
      #[← mkAppM ``Lean.Order.PartialOrder.rel_trans #[hsub, goal.specProof]]
    return { splitVCProof := prf, subgoals := [hsub.mvarId!] }
  | _, _ => throwError "sep frameproc: unsupported spec precondition shape{indentExpr specPre}"

/-- Phase one: always frame; the state vector is the goal's own. -/
def sepFrameProc : FrameInferenceProc := fun i => do
  return .commit i.unframedApp.excessArgs (sepFrameSplit i)

@[frameproc] def sepFP : FrameProc where
  prog := ``List
  opHead := ``SepWP.frameOp
  mkOpAppM := fun _ => pure (mkConst ``SepWP.frameOp)
  mkResourceTy := fun _ => pure (mkApp (mkConst ``MProp) (mkNatLit 64))
  proc := sepFrameProc

end SepWP
