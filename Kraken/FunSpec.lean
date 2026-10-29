module

public import Kraken.StateCfg
public meta import Lean.Elab.Command

open Std.WP
open Lean.Order
open scoped Program.WP

public structure CallingConvention where
  calleeSaved : List Reg64
  paramArea : Nat → Nat

@[expose] public def CallingConvention.SysV : CallingConvention :=
  ⟨[.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], fun k => 8 * k⟩

@[expose] public def CallingConvention.Win64 : CallingConvention :=
  ⟨[.rbx, .rbp, .rdi, .rsi, .r12, .r13, .r14, .r15, .rsp], fun k => 32 + 8 * k⟩

namespace FunSpec

variable [Host] [FunDecls]

public theorem autoframes {f : Label} {g : Fragment} (h : FunDecls.at (label f) = some g)
    {P : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    {X : MachineData → Int64 → MachineData → Prop} {Fr : MachineData → MachineData → Prop}
    (hp : ∀ s ra, ⦃ fun s₀ => s₀ = s.push64 ra ∧ P s ⦄ g.prog
      ⦃ fun _ _ => False; fun a s' => (a = ra → Q s s' ∧ s'.regs.rsp = s.regs.rsp ∧ Fr s s')
        ∧ (a ≠ ra → X s a s' ∧ Fr s s') ⦄) :
    ∀ s ra (Q' : Unit → MachineData → Prop) (E' : Int64 → MachineData → Prop),
      ⦃ fun s₀ => s₀ = s.push64 ra ∧ P s
          ∧ (∀ s', Q s s' ∧ s'.regs.rsp = s.regs.rsp ∧ Fr s s' → E' ra s')
          ∧ (∀ a s', a ≠ ra → X s a s' ∧ Fr s s' → E' a s') ⦄
        FunDecls.body f
      ⦃ Q'; E' ⦄ := by
  refine fun s ra Q' E' => ⟨fun s₀ ⟨h₀, hpre, hok, hexit⟩ => ?_⟩
  rw [FunDecls.body_eq h]
  refine Program.wp_mono (fun _ h => False.elim h) (fun u hu => ?_) ((hp s ra).1 s₀ ⟨h₀, hpre⟩)
  by_cases ha : u.pc = ra
  · exact ha ▸ hok u.data (hu.1 ha)
  · exact hexit u.pc u.data ha (hu.2 ha)

public theorem autoframes_of_ret {f : Label} {g : Fragment} (h : FunDecls.at (label f) = some g)
    {P : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    {Fr : MachineData → MachineData → Prop}
    (hp : ∀ s ra, ⦃ fun s₀ => s₀ = s.push64 ra ∧ P s ⦄ g.prog
      ⦃ fun _ _ => False; fun a s' => a = ra ∧ Q s s' ∧ s'.regs.rsp = s.regs.rsp ∧ Fr s s' ⦄) :
    ∀ s ra (Q' : Unit → MachineData → Prop) (E' : Int64 → MachineData → Prop),
      ⦃ fun s₀ => s₀ = s.push64 ra ∧ P s
          ∧ (∀ s', Q s s' ∧ s'.regs.rsp = s.regs.rsp ∧ Fr s s' → E' ra s') ⦄
        FunDecls.body f
      ⦃ Q'; E' ⦄ := by
  refine fun s ra Q' E' => ⟨fun s₀ ⟨h₀, hpre, hok⟩ => ?_⟩
  rw [FunDecls.body_eq h]
  exact Program.wp_mono (fun _ h => False.elim h) (fun u hu => hu.1 ▸ hok u.data hu.2)
    ((hp s ra).1 s₀ ⟨h₀, hpre⟩)

public theorem plain {f : Label} {g : Fragment} (h : FunDecls.at (label f) = some g)
    {P : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    {X : MachineData → Int64 → MachineData → Prop}
    (hp : ∀ s ra, ⦃ fun s₀ => s₀ = s.push64 ra ∧ P s ⦄ g.prog
      ⦃ fun _ _ => False; fun a s' => (a = ra → Q s s') ∧ (a ≠ ra → X s a s') ⦄) :
    ∀ s ra, ⦃ fun s₀ => s₀ = s.push64 ra ∧ P s ⦄ FunDecls.body f
      ⦃ fun _ _ => False; fun a s' => (a = ra → Q s s') ∧ (a ≠ ra → X s a s') ⦄ :=
  FunDecls.body_eq h ▸ hp

end FunSpec

namespace FunSpec

open Lean Elab Command Term Meta

declare_syntax_cat funspecClause

syntax "calling_conv " term : funspecClause
syntax "paramSlots " term : funspecClause
syntax "reserve " term : funspecClause
syntax "preserves" (ppSpace ident)+ : funspecClause
syntax "writes " term,+ : funspecClause

syntax (name := funspecCmd) "funspec " ident ppSpace str (ppSpace bracketedBinder)* " at " ident
  (" requires " term ";")? " ensures " ident " => " term
  (";" " exits " ident ident " => " term)?
  (" autoframes" (ppSpace funspecClause)*)? " := " term (Lean.Parser.Term.whereDecls)? : command

meta def regOrder : List Name :=
  [`rax, `rbx, `rcx, `rdx, `rsi, `rdi, `rsp, `rbp, `r8, `r9, `r10, `r11, `r12, `r13, `r14, `r15]

meta def regField (x : Ident) (field : Name) : Ident :=
  mkIdent (x.getId ++ `regs ++ field)

meta def ccTerm (cc : Term) : CommandElabM Term :=
  `((open CallingConvention in ($cc : CallingConvention)))

meta def reduceInTerm (stx : Term) : CommandElabM Expr := liftTermElabM do
  let e ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  Meta.reduce (← instantiateMVars e)

meta def calleeSaved (cc : Term) : CommandElabM (List Name) := do
  let e ← reduceInTerm (← `(CallingConvention.calleeSaved $(← ccTerm cc)))
  let some (_, rs) := e.listLit?
    | throwErrorAt cc "calleeSaved of {cc} does not reduce to a list literal"
  rs.mapM fun r => match r with
    | .const n _ => if n.getPrefix == ``Reg64 then pure (Name.mkSimple n.getString!)
        else throwErrorAt cc "unexpected register {r}"
    | _ => throwErrorAt cc "unexpected register {r}"

meta def paramArea (cc k : Term) : CommandElabM Nat := do
  let e ← reduceInTerm (← `(CallingConvention.paramArea $(← ccTerm cc) $k))
  let some n ← liftTermElabM (Meta.evalNat e).run
    | throwErrorAt k "paramArea of {k} does not reduce to a numeral"
  pure n

meta def block (stx : Term) : CommandElabM Term :=
  match stx with
  | `($b[*...<$n]) => `(($b, $n))
  | `($b[$a...<$e]) => `(($b + BitVec.ofNat 64 $a, $e - $a))
  | _ => throwErrorAt stx "expected a block `b[*...<n]` or `b[a...<e]`"

meta def conj (ts : Array Term) (last : Term) : CommandElabM Term :=
  ts.foldrM (fun t acc => `($t ∧ $acc)) last

meta def elabWhere (name : Ident) (ds : Array Syntax) : CommandElabM Unit := do
  if ds.isEmpty then return
  elabCommand (← `(command| namespace $name:ident))
  for d in ds do
    match d with
    | `(Lean.Parser.Term.letRecDecl| $[@[$attrs?,*]]? $x:ident $bs* : $ty := $val) =>
      let bs : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := bs.map (⟨·.raw⟩)
      elabCommand <| ← match attrs? with
        | some attrs => `(command| @[$attrs,*] private abbrev $x:ident $bs* : $ty := $val)
        | none => `(command| private abbrev $x:ident $bs* : $ty := $val)
    | _ => throwErrorAt d "funspec expects `where` declarations `x binders* : type := value`"
  elabCommand (← `(command| end $name:ident))

@[command_elab funspecCmd] public meta def elabFunspec : CommandElab := fun stx => do
  let `(funspec $name $f $binders* at $c $[requires $P? ;]? ensures $tQ => $Q
      $[; exits $aX? $tX? => $X?]? $[autoframes $clauses?*]? := $proof $[$wds?]?) := stx
    | throwUnsupportedSyntax
  let wdecls := match wds? with
    | some wd => wd.raw[1].getSepArgs
    | none => #[]
  let P ← P?.getDM `(True)
  let some (h, p) ← binders.findSomeM? fun b => do
      match b with
      | `(bracketedBinder| ($h:ident : FunDecls.at (label $_) = some ⟨$p⟩)) => pure (some (h, p))
      | _ => pure none
    | throwErrorAt stx "funspec expects a binder `(h : FunDecls.at (label {f}) = some ⟨p⟩)`"
  let aX : Ident := aX?.getD (mkIdent `a)
  if let some tX := tX? then
    unless tX.getId == tQ.getId do
      throwErrorAt tX "exits must bind the state as {tQ}, the binder of ensures"
  let X ← X?.getDM `(False)
  let some clauses := clauses? | do
    elabWhere name wdecls
    let proof ← if wdecls.isEmpty then pure proof else `(open $name:ident in $proof)
    elabCommand (← `(command|
      open scoped Program.WP in
      @[spec] theorem $name:ident $binders* : ∀ ($c : MachineData) (ra : Int64),
          Std.WP.Triple (FunDecls.body $f) (fun s => s = MachineData.push64 $c ra ∧ $P)
            (fun _ _ => False) (fun $aX $tQ => ($aX = ra → $Q) ∧ ($aX ≠ ra → $X)) :=
        FunSpec.plain $h (P := fun $c => $P) (Q := fun $c $tQ => $Q) (X := fun $c $aX $tQ => $X)
          (show ∀ ($c : MachineData) (ra : Int64),
            Std.WP.Triple $p (fun s => s = MachineData.push64 $c ra ∧ $P)
              (fun _ _ => False) (fun $aX $tQ => ($aX = ra → $Q) ∧ ($aX ≠ ra → $X)) from $proof)))
  let mut cc? : Option Term := none
  let mut slots : Term ← `(0)
  let mut rsv : Term ← `(0)
  let mut kept₀ : Array Ident := #[]
  let mut written : Array Term := #[]
  for cl in clauses do
    match cl with
    | `(funspecClause| calling_conv $cc) => cc? := some cc
    | `(funspecClause| paramSlots $k) => slots := k
    | `(funspecClause| reserve $k) => rsv := k
    | `(funspecClause| preserves $rs*) => kept₀ := kept₀ ++ rs
    | `(funspecClause| writes $bs,*) => written := written ++ (← bs.getElems.mapM block)
    | _ => throwErrorAt cl "unexpected autoframes clause"
  for r in kept₀ do
    unless regOrder.contains r.getId do throwErrorAt r "{r} is not a 64-bit register"
  let saved ← match cc? with
    | some cc => calleeSaved cc
    | none => pure []
  let kept := regOrder.filter fun r => r != `rsp && (saved.contains r || kept₀.any (·.getId == r))
  let eqs ← kept.toArray.mapM fun r => `($(regField tQ r) = $(regField c r))
  let rsp := regField c `rsp
  let mut blocks : Array Term := #[← `(Mem.Block.ofStackSlots $rsp $rsv)]
  if let some cc := cc? then
    let n ← paramArea cc slots
    if n > 0 then
      let base := mkIdent (rsp.getId ++ `toBitVec)
      blocks := blocks.push (← `(($base, $(Syntax.mkNumLit (toString n)))))
  blocks := blocks ++ written
  let mem ← `(Mem.WritesOnly [$blocks,*] $(mkIdent (c.getId ++ `dmem))
    $(mkIdent (tQ.getId ++ `dmem)))
  let frame := mkIdent (name.getId ++ `Frame)
  elabCommand (← `(command|
    abbrev $frame:ident ($c:ident $tQ:ident : MachineData) : Prop := $(← conj eqs mem)))
  let tRsp := regField tQ `rsp
  elabWhere name wdecls
  let ok ← `(∀ $tQ:ident, $Q ∧ $tRsp = $rsp ∧ $frame $c $tQ → E' ra $tQ)
  let pre ← if X?.isSome then
      `(fun s => s = MachineData.push64 $c ra ∧ $P ∧ $ok
        ∧ (∀ ($aX : Int64) ($tQ : MachineData), $aX ≠ ra → $X ∧ $frame $c $tQ → E' $aX $tQ))
    else `(fun s => s = MachineData.push64 $c ra ∧ $P ∧ $ok)
  let stmt ← `(∀ ($c : MachineData) (ra : Int64) (Q' : Unit → MachineData → Prop)
      (E' : Int64 → MachineData → Prop), Std.WP.Triple (FunDecls.body $f) $pre Q' E')
  let pf ← if X?.isSome then
      `(FunSpec.autoframes $h (P := fun $c => $P) (Q := fun $c $tQ => $Q)
          (X := fun $c $aX $tQ => $X) (Fr := $frame)
          (show ∀ ($c : MachineData) (ra : Int64),
            Std.WP.Triple $p (fun s => s = MachineData.push64 $c ra ∧ $P) (fun _ _ => False)
              (fun $aX $tQ => ($aX = ra → $Q ∧ $tRsp = $rsp ∧ $frame $c $tQ)
                ∧ ($aX ≠ ra → $X ∧ $frame $c $tQ)) from open $name:ident in $proof))
    else
      `(FunSpec.autoframes_of_ret $h (P := fun $c => $P) (Q := fun $c $tQ => $Q) (Fr := $frame)
          (show ∀ ($c : MachineData) (ra : Int64),
            Std.WP.Triple $p (fun s => s = MachineData.push64 $c ra ∧ $P) (fun _ _ => False)
              (fun a $tQ => a = ra ∧ $Q ∧ $tRsp = $rsp ∧ $frame $c $tQ)
            from open $name:ident in $proof))
  elabCommand (← `(command|
    open scoped Program.WP in
    @[spec] theorem $name:ident $binders* : $stmt := $pf))

end FunSpec
