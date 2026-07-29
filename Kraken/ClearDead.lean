/-
Dead-hypothesis elimination for VC discharge. EXPERIMENTAL: correct on
register-only chains, but over-prunes on carry chains (see TODO.md).

Accessor-style stepping emits one equation per state component per
instruction; a postcondition typically reads only a few. `clear_dead`
keeps the equations reachable from the goal through equation LHS→RHS
edges and clears the rest, so `bv_decide` does not bitblast components
no one queries. Reachability is directed, so an equation whose value is
read by a later instruction (a carry consumed by `adc`) stays live.
-/
import Lean
open Lean Elab Tactic Meta

elab "clear_dead" : tactic => do
  liftMetaTactic1 fun g => g.withContext do
    let addSub (acc : Std.HashSet Expr) (e : Expr) : Std.HashSet Expr := Id.run do
      let mut acc := acc; let mut stack := #[e]
      while stack.size > 0 do
        let t := stack.back!; stack := stack.pop
        if acc.contains t then continue
        acc := acc.insert t
        match t with
        | .app f a => stack := (stack.push f).push a
        | .proj _ _ b | .mdata _ b => stack := stack.push b
        | .lam _ ty b _ | .forallE _ ty b _ => stack := (stack.push ty).push b
        | .letE _ ty v b _ => stack := ((stack.push ty).push v).push b
        | _ => pure ()
      return acc
    let mut reach := addSub {} (← instantiateMVars (← g.getType))
    let mut eqs : Array (FVarId × Expr × Expr) := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail || d.value?.isSome then continue
      let ty ← instantiateMVars d.type
      if let some (_, l, r) := ty.eq? then eqs := eqs.push (d.fvarId, l, r)
    -- The equations are topologically ordered (a state's components are defined
    -- from the previous state's), so one reverse pass reaches the fixpoint.
    let mut live : Std.HashSet FVarId := {}
    for (fv, lhs, rhs) in eqs.reverse do
      if reach.contains lhs then
        live := live.insert fv; reach := addSub reach rhs
    let mut g := g
    for (fv, _, _) in eqs do
      unless live.contains fv do g ← g.tryClear fv
    return g
