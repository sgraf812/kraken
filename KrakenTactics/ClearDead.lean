/-
Dead-hypothesis elimination.

`clear_dead` keeps the equation hypotheses reachable from the goal through
equation LHS→RHS edges and clears the rest. Symbolic execution emits one
equation per state component per step while a postcondition reads few of
them, and a solver such as `bv_decide` otherwise processes every one.

The analysis is directed, so an equation whose value a later step reads
stays live, and it is closed under rewriting of projection paths, so
components read at different granularities (a whole record field by one
step, a subfield by the next) stay connected.

Nothing here is domain-specific: the input is equation hypotheses and a
goal, the output is the goal with unreachable equations cleared.
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
    -- Reachability is closed under rewriting by live equations, but only over
    -- projection-path terms (`cf (status x)`): components are read at different
    -- granularities, so a live `status x = status y` must carry a reachable
    -- `cf (status x)` over to `cf (status y)`. Restricting the rewrite to paths
    -- keeps this linear; rewriting every reachable subterm does not scale.
    let isPath (e : Expr) : Bool := Id.run do
      let mut t := e
      let mut depth := 0
      while depth < 8 do
        match t with
        | .app f a => if f.isConst then t := a; depth := depth + 1 else return false
        | .proj _ _ b => t := b; depth := depth + 1
        | .fvar _ => return depth > 0
        | _ => return false
      return false
    -- Collect path-shaped terms among all reachable subterms.
    let collectPaths (ps : Std.HashSet Expr) (acc : Std.HashSet Expr) : Std.HashSet Expr := Id.run do
      let mut ps := ps
      for t in acc do
        if isPath t then ps := ps.insert t
      return ps
    let mut paths : Std.HashSet Expr := collectPaths {} reach
    let mut live : Std.HashSet FVarId := {}
    let mut changed := true
    while changed do
      changed := false
      for (fv, lhs, rhs) in eqs.reverse do
        unless live.contains fv do
          if reach.contains lhs then
            live := live.insert fv
            changed := true
            let sub := addSub {} rhs
            reach := addSub reach rhs
            paths := collectPaths paths sub
            let mut rewritten := #[]
            for t in paths do
              let t' := t.replace fun e => if e == lhs then some rhs else none
              unless t' == t do rewritten := rewritten.push t'
            for t' in rewritten do
              let sub' := addSub {} t'
              reach := addSub reach t'
              paths := collectPaths paths sub'
    let mut g := g
    for (fv, _, _) in eqs do
      unless live.contains fv do g ← g.tryClear fv
    return g
