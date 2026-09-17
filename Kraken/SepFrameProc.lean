/-
The frame inference procedure of the separation wp, with `ecancel` as its
engine. At a spec application `vcgen` hands over the goal's precondition and
the spec's precondition with its logical variables live.
`Kraken.Tactic.solveSepEq` cancels the spec's footprint out of the goal
precondition, assigning the logical variables by matching and the remainder
to the frame, and certifies the split with one AC equation.
`SepWP.split_of_eq` turns that equation into the split VC's proof, and
`SepWP.frames_directive` is the frame-rule side goal.

Every instruction spec is a triple of one directive, so the procedure is
keyed on `Directive`: that is where `vcgen` applies a spec with a footprint.
-/
import Kraken.SepSpecs
import Lean.Elab.Tactic.VCGen.FrameProc

open Lean Meta Sym Sym.Internal Elab Tactic VCGen
open Std.WP
open Lean.Order
open scoped SepWP

namespace SepWP

/-- The split VC of a frame `R` and a footprint `fp`: the precondition is
`fp ∗ R` by AC, and the spec runs at `fp`. -/
theorem split_of_eq {pre fp R : MProp 64}
    {W : Reg64s → RegZmms → StatusFlags → MProp 64} {r : Reg64s} {z : RegZmms}
    {f : StatusFlags} (hc : pre = fp ∗ R) (hspec : fp ⊑ W r z f) :
    pre ⊑ frameOp R W r z f := by
  rw [frameOp_apply, hc, MProp.sep_comm]
  exact MProp.sep_mono_right R hspec

/-- The split VC when the spec's precondition is `⌜φ⌝ ⊓ fp`: the footprint `fp`
is matched, and `φ` is a subgoal of the frameproc. -/
theorem split_of_eq_ofProp {pre fp R : MProp 64}
    {W : Reg64s → RegZmms → StatusFlags → MProp 64} {r : Reg64s} {z : RegZmms}
    {f : StatusFlags} {φ : Prop} (hc : pre = fp ∗ R) (hφ : φ)
    (hspec : ⌜φ⌝ ⊓ fp ⊑ W r z f) : pre ⊑ frameOp R W r z f := by
  rw [frameOp_apply, hc, MProp.sep_comm]
  refine MProp.sep_mono_right R (PartialOrder.rel_trans ?_ hspec)
  exact le_meet _ _ _ (le_ofProp _ _ hφ) PartialOrder.rel_refl

/-- The wand of the frame operator at a state is the wand of `∗` at that
state: `EFrame.upperAdjoint_pointwise` through the three layers. -/
theorem upperAdjoint_frameOp_pointwise (R : MProp 64)
    (X : Reg64s → RegZmms → StatusFlags → MProp 64) (r : Reg64s) (z : RegZmms)
    (f : StatusFlags) :
    PreservesSup.upperAdjoint (frameOp R) X r z f
      = PreservesSup.upperAdjoint (MProp.sep R) (X r z f) := by
  unfold SepWP.frameOp
  rw [EFrame.upperAdjoint_pointwise, EFrame.upperAdjoint_pointwise, EFrame.upperAdjoint_pointwise]

/-- The wand of the empty frame is the identity. -/
theorem upperAdjoint_frameOp_emp
    (X : Reg64s → RegZmms → StatusFlags → MProp 64) (r : Reg64s) (z : RegZmms)
    (f : StatusFlags) :
    PreservesSup.upperAdjoint (frameOp MProp.emp) X r z f = X r z f := by
  rw [upperAdjoint_frameOp_pointwise]
  refine PartialOrder.rel_antisymm ?_ ?_
  · have h := PreservesSup.upperAdjoint_le (MProp.sep MProp.emp) (X r z f)
    rwa [MProp.emp_sep] at h
  · exact PreservesSup.le_upperAdjoint _ (PartialOrder.rel_of_eq (MProp.emp_sep _))

/-- The trivial split: frame `emp`, the whole precondition pays the spec. -/
theorem split_emp {pre : MProp 64}
    {W : Reg64s → RegZmms → StatusFlags → MProp 64} {r : Reg64s} {z : RegZmms}
    {f : StatusFlags} (h : pre ⊑ W r z f) : pre ⊑ frameOp MProp.emp W r z f := by
  rw [frameOp_apply, MProp.emp_sep]
  exact h

/-- Normalize the register reads of an address: `(r.set64 x v).get64 y` reads
through the write. The atoms of a precondition were stated at an earlier
register file than the address the current instruction computes. -/
def normalizeRegs (e : Expr) : MetaM (Expr × Option Expr) := do
  let thms ← ({} : SimpTheorems).addConst ``Reg64s.get64_set64
  let thms ← thms.addConst ``eq_self_iff_true
  let ctx ← Simp.mkContext {} (simpTheorems := #[thms])
  let (r, _) ← Meta.simp e ctx (simprocs := #[← Simp.getSimprocs])
  return (r.expr, r.proof?)

/-- The region atoms of a precondition: `bytesAt L a₀` whose bytes are not a
stored value `Int.toBytes …`. -/
def regionAtoms (pre : Expr) : MetaM (List Expr) := do
  let clauses ← Kraken.Tactic.reifyClauses pre
  return clauses.filter fun c =>
    c.isAppOfArity ``MProp.bytesAt 3 && !(c.appFn!.appArg!.isAppOf ``Int.toBytes)

/-- Phase two. The spec's precondition is `⌜φ⌝ ⊓ fp` or a bare `fp`. `fp` is
the footprint: `solveSepEq` proves `pre = fp ∗ ?R` with `?R` a fresh clause
that absorbs the remainder, assigning the spec's logical variables on the way.
`?R` becomes the frame and the pre VC closes by reflexivity. The pure
conjunct `φ` is the post entailment `new ⊑ Q () r z f`, and after the frame
rule `Q () r z f` is the wand `upperAdjoint (frameOp R) X r z f`. The
frameproc rewrites it with `upperAdjoint_frameOp_pointwise` and emits
`new ⊑ upperAdjoint (MProp.sep R) (X r z f)`, which the lattice split of
`vcgen` turns into `R ∗ new ⊑ X r z f`. When no split exists, the frame is
`emp` and the pre VC `pre ⊑ specPre` stays open for the user. -/
def sepFrameSplit (i : FrameInferenceInfo) (goal : FrameGoal) :
    Lean.Meta.Grind.GrindM FrameSplit := do
  let ss := goal.framedApp.excessArgs
  let W := goal.framedApp.expr.stripArgsN ss.size
  let w64 ← shareCommon (mkNatLit 64)
  let specPre ← instantiateMVarsS goal.specPre
  -- peel a pure conjunct `⌜φ⌝ ⊓ fp`
  let (pure?, fp) :=
    if specPre.isAppOfArity ``Lean.Order.meet 4 then
      let a := specPre.appFn!.appArg!
      if a.isAppOfArity ``Lean.Order.CompleteLattice.ofProp 3 then (some a.appArg!, specPre.appArg!)
      else (none, specPre)
    else (none, specPre)
  let sep ← mkConstS ``MProp.sep
  -- Match against register-normalized spellings; `hpre : i.pre = pre'`,
  -- `hfp : fp = fp'` are the normalization equations, or `none` when unchanged.
  let (pre', hpre) ← normalizeRegs i.pre
  let (fp', hfp) ← normalizeRegs fp
  -- The footprint `bytesAt ?bs addr` pays with the atom at `addr`: the address
  -- is compared syntactically, never unified, and `?bs` takes that atom's
  -- bytes. When no atom sits at `addr`, a region is sliced at `addr`, and
  -- its slot atom pays; the bound is a subgoal.
  let mut pre'' := pre'
  let mut hslice : Option Expr := none
  let mut sliceGoals : List MVarId := []
  let mut paid := false
  if fp'.isAppOfArity ``MProp.bytesAt 3 then
    let addr := fp'.appArg!
    let payer? := (← Kraken.Tactic.reifyClauses pre').find? fun c =>
      c.isAppOfArity ``MProp.bytesAt 3 && c.appArg! == addr
    match payer? with
    | some c =>
      paid ← withConfig (fun c => { c with assignSyntheticOpaque := true }) <|
        withTransparency .instances (isDefEq fp' c)
      trace[Elab.Tactic.Do.vcgen] "sep frameproc: footprint paid by{indentExpr c}"
    | none =>
      for atom in ← regionAtoms pre' do
        let L := atom.appFn!.appArg!
        let a₀ := atom.appArg!
        let hb ← mkFreshExprSyntheticOpaqueMVar
          (← mkAppNS (← mkConstS ``MProp.SliceBound) #[L, a₀, addr])
        let heq ← mkAppNS (← mkConstS ``MProp.bytesAt_slice) #[L, a₀, addr, hb]
        let some (_, _, sliced) := (← instantiateMVarsS (← Sym.inferType heq)).eq? | continue
        -- the slot atom of the slice sits at `addr`
        let some slot := (← Kraken.Tactic.reifyClauses sliced).find? fun c =>
            c.isAppOfArity ``MProp.bytesAt 3 && c.appArg! == addr | continue
        unless ← withConfig (fun c => { c with assignSyntheticOpaque := true }) <|
            withTransparency .instances (isDefEq fp' slot) do continue
        let mprop ← mkAppNS (← mkConstS ``MProp) #[w64]
        let ctx := Expr.lam `x mprop (pre'.replace fun e => if e == atom then some (.bvar 0) else none) .default
        hslice := some (← mkAppNS (← mkConstS ``congrArg [.succ .zero, .succ .zero])
          #[mprop, mprop, atom, sliced, ctx, heq])
        pre'' := pre'.replace fun e => if e == atom then some sliced else none
        sliceGoals := [hb.mvarId!]
        paid := true
        trace[Elab.Tactic.Do.vcgen] "sep frameproc: sliced{indentExpr atom}\nat{indentExpr addr}"
        break
  let fp' ← instantiateMVarsS fp'
  let R ← mkFreshExprMVar (← mkAppNS (← mkConstS ``MProp) #[w64])
  let target ← mkAppNS sep #[w64, fp', R]
  let hc? ← if paid then
      withConfig (fun c => { c with assignSyntheticOpaque := true }) <|
        withTransparency .default <| Kraken.Tactic.solveSepEq pre'' target
    else pure none
  if hc?.isNone then
    trace[Elab.Tactic.Do.vcgen] "sep frameproc: no split of{indentExpr pre'}\nfor{indentExpr fp'}"
  else
    trace[Elab.Tactic.Do.vcgen] "sep frameproc: cancelled"
  match hc? with
  | some _ =>
    -- The naked remainder comes back as a clause list ending in `emp`. Rebuild
    -- the frame from its clauses and certify the split against that spelling.
    let clauses ← Kraken.Tactic.reifyClauses (← instantiateMVarsS R)
    let R ← match clauses.reverse with
      | [] => mkAppNS (← mkConstS ``MProp.emp) #[w64]
      | c :: cs => cs.foldlM (fun acc c => mkAppNS sep #[w64, c, acc]) c
    let R ← shareCommon R
    trace[Elab.Tactic.Do.vcgen] "sep frameproc: frame{indentExpr R}"
    let fp' ← instantiateMVarsS fp'
    let target ← mkAppNS sep #[w64, fp', R]
    let some hc'' ← withTransparency .default (Kraken.Tactic.solveSepEq pre'' target)
      | throwError "sep frameproc: the remainder{indentExpr R}\ndoes not recombine with the footprint"
    trace[Elab.Tactic.Do.vcgen] "sep frameproc: recombined"
    -- `hc : i.pre = fp ∗ R` from `i.pre = pre' = pre'' = fp' ∗ R = fp ∗ R`
    let mprop ← mkAppNS (← mkConstS ``MProp) #[w64]
    let eqTrans ← mkConstS ``Eq.trans [.succ .zero]
    let trans (a b c h₁ h₂ : Expr) : Lean.Meta.Grind.GrindM Expr :=
      mkAppNS eqTrans #[mprop, a, b, c, h₁, h₂]
    let fp ← instantiateMVarsS fp
    let fpR ← mkAppNS sep #[w64, fp, R]
    let fp'R ← mkAppNS sep #[w64, fp', R]
    let mut hc := hc''
    let mut preL := pre''
    if let some hs := hslice then
      hc ← trans pre' pre'' fp'R hs hc; preL := pre'
    if let some hp := hpre then
      hc ← trans i.pre pre' fp'R hp hc; preL := i.pre
    if let some hf := hfp then
      -- `fp' ∗ R = fp ∗ R` from `fp = fp'`
      let hfR ← mkAppNS (← mkConstS ``congrArg [.succ .zero, .succ .zero])
        #[mprop, mprop, fp', fp, Expr.lam `x mprop (← mkAppNS sep #[w64, .bvar 0, R]) .default,
          ← mkAppNS (← mkConstS ``Eq.symm [.succ .zero]) #[mprop, fp, fp', hf]]
      hc ← trans preL fp'R fpR hc hfR
    goal.frame.assign R
    trace[Elab.Tactic.Do.vcgen] "sep frameproc: equations chained"
    let specPre ← shareCommon (← instantiateMVarsS specPre)
    let fp ← shareCommon (← instantiateMVarsS fp)
    goal.footprint.assign specPre
    -- `i.le` is `@PartialOrder.rel α inst`; reuse its carrier and instance.
    let leArgs := i.le.getAppArgs
    goal.preVC.assign (← mkAppNS
      (← mkConstS ``Lean.Order.PartialOrder.rel_refl i.le.getAppFn.constLevels!)
      #[leArgs[0]!, leArgs[1]!, specPre])
    match pure? with
    | some φ =>
      let φ ← shareCommon (← instantiateMVarsS φ)
      let hφ ← do
        let some (_, _, lhs, rhs) := φ.app4? ``Lean.Order.PartialOrder.rel | pure none
        let args := rhs.getAppArgs
        if rhs.isAppOfArity ``Lean.Order.PreservesSup.upperAdjoint 7
            && args[2]!.isAppOfArity ``SepWP.frameOp 1 then
          let X := args[3]!
          let Xs ← shareCommon (mkAppN X #[args[4]!, args[5]!, args[6]!]).headBeta
          -- `heq : rhs = rhs'`, the wand pushed through the layers; `rhs'` is read
          -- off the equation's type, so its instance is the lemma's own.
          let heq ← if clauses.isEmpty then
              mkAppNS (← mkConstS ``SepWP.upperAdjoint_frameOp_emp)
                #[X, args[4]!, args[5]!, args[6]!]
            else
              mkAppNS (← mkConstS ``SepWP.upperAdjoint_frameOp_pointwise)
                #[R, X, args[4]!, args[5]!, args[6]!]
          let some (_, _, rhs') := (← instantiateMVarsS (← Sym.inferType heq)).eq?
            | throwError "sep frameproc: not an equation{indentExpr heq}"
          let rhs' ← shareCommon (if clauses.isEmpty then Xs else rhs')
          let φ' ← mkAppNS i.le #[lhs, rhs']
          let hsub ← mkFreshExprSyntheticOpaqueMVar φ'
          -- `hφ : φ` from `hsub : φ'` by `Eq.mpr (congrArg (lhs ⊑ ·) heq)`
          let mprop ← mkAppNS (← mkConstS ``MProp) #[w64]
          let hcongr ← mkAppNS (← mkConstS ``congrArg [.succ .zero, .succ .zero])
            #[mprop, mkSort .zero, rhs, rhs', ← mkAppNS i.le #[lhs], heq]
          let hφ ← mkAppNS (← mkConstS ``Eq.mpr [.zero]) #[φ, φ', hcongr, hsub]
          pure (some (hφ, hsub.mvarId!))
        else pure none
      let (hφ, sub) ← match hφ with
        | some (hφ, sub) => pure (hφ, sub)
        | none =>
          let hφ ← mkFreshExprSyntheticOpaqueMVar φ
          pure (hφ, hφ.mvarId!)
      let prf ← mkAppNS (← mkConstS ``SepWP.split_of_eq_ofProp)
        #[i.pre, fp, R, W, ss[0]!, ss[1]!, ss[2]!, φ, hc, hφ, goal.specProof]
      return { splitVCProof := prf, subgoals := sub :: sliceGoals }
    | none =>
      let prf ← mkAppNS (← mkConstS ``SepWP.split_of_eq)
        #[i.pre, fp, R, W, ss[0]!, ss[1]!, ss[2]!, hc, goal.specProof]
      return { splitVCProof := prf, subgoals := sliceGoals }
  | none =>
    goal.frame.assign (← mkAppNS (← mkConstS ``MProp.emp) #[w64])
    goal.footprint.assign i.pre
    let prf ← mkAppNS (← mkConstS ``SepWP.split_emp)
      #[i.pre, W, ss[0]!, ss[1]!, ss[2]!, goal.specProof]
    return { splitVCProof := prf, subgoals := [] }

/-- Phase one: always frame, at the goal's own state. -/
def sepFrameProc : FrameInferenceProc := fun i =>
  return .commit i.unframedApp.excessArgs (sepFrameSplit i)

@[frameproc] def sepFP : FrameProc where
  prog := ``Directive
  opHead := ``SepWP.frameOp
  mkOpAppM := fun _ => pure (mkConst ``SepWP.frameOp)
  mkResourceTy := fun _ => pure (mkApp (mkConst ``MProp) (mkNatLit 64))
  proc := sepFrameProc

end SepWP

/-! ## Smoke tests

A store and a register write with the goal owning exactly the slot; two
stores into two slots, where each store's footprint is one slot and the other
slot is the frame `solveSepEq` finds; and a store followed by an `add` from
the other slot. -/

section Smoke

open Kraken.X64.Parser

attribute [local grind .] Lean.Order.PartialOrder.rel_refl

example [CodeEnv] (bs : List UInt8) (hlen : bs.length = 8) :
    ⦃ fun r z f => MProp.bytesAt bs (r.get64 .rdx + BitVec.ofInt 64 (136 : Int64).toInt) ⦄
      (parse("movq %rax, 136(%rdx)\nmovq $1, %rbx"))
    ⦃ fun _ r z f => MProp.bytesAt (Int.toBytes 8 (r.get64 .rax).toInt)
        (r.get64 .rdx + BitVec.ofInt 64 (136 : Int64).toInt) ⦄ := by
  vcgen with finish

example [CodeEnv] (bs cs : List UInt8) (hb : bs.length = 8) (hc : cs.length = 8) :
    ⦃ fun r z f => MProp.bytesAt bs (r.get64 .rdx + BitVec.ofInt 64 (136 : Int64).toInt)
        ∗ MProp.bytesAt cs (r.get64 .rdx + BitVec.ofInt 64 (144 : Int64).toInt) ⦄
      (parse("movq %rax, 136(%rdx)\nmovq %rbx, 144(%rdx)"))
    ⦃ fun _ r z f => MProp.bytesAt (Int.toBytes 8 (r.get64 .rax).toInt)
          (r.get64 .rdx + BitVec.ofInt 64 (136 : Int64).toInt)
        ∗ MProp.bytesAt (Int.toBytes 8 (r.get64 .rbx).toInt)
          (r.get64 .rdx + BitVec.ofInt 64 (144 : Int64).toInt) ⦄ := by
  vcgen with finish

example [CodeEnv] (bs cs : List UInt8) (hb : bs.length = 8) (hc : cs.length = 8) :
    ⦃ fun r z f => MProp.bytesAt bs (r.get64 .rdx + BitVec.ofInt 64 (136 : Int64).toInt)
        ∗ MProp.bytesAt cs (r.get64 .rdx + BitVec.ofInt 64 (144 : Int64).toInt) ⦄
      (parse("movq %rax, 136(%rdx)\naddq 144(%rdx), %rbx"))
    ⦃ fun _ r z f => MProp.bytesAt (Int.toBytes 8 (r.get64 .rax).toInt)
          (r.get64 .rdx + BitVec.ofInt 64 (136 : Int64).toInt)
        ∗ MProp.bytesAt cs (r.get64 .rdx + BitVec.ofInt 64 (144 : Int64).toInt) ⦄ := by
  vcgen with finish

end Smoke
