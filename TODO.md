# TODO

- Engine (lean4/grind): `internalize` does not share/canonicalize its argument
  (`Grind.add`/`addFactStep` likewise); the hash-consing invariant `mkEqProof`
  relies on is unmaintainable caller-side (accessor-obtained terms are only
  sometimes pointer-identical to session nodes, see Kraken.easm mechanism
  trace). Fix: `internalize` runs `preprocessLight`-class sharing itself;
  defense in depth: `mkCongrDefaultProof` treats the all-`isSameExpr` case as
  `rfl`. Reproducer: mkEqProof-panic-mwe.lean. Until then easm carries the
  workaround (preprocessLight before internalize).
- Engine (lean4/grind): directed fold of stratified equation chains
  (constant propagation / hypothesis-chain evaluation). Blocks: Sdyn.lean
  reload VCs (the remaining sorry), adc>=20 under finish, multireg under
  finish.
- Engine (vcgen): normalize `And` at Prop-valued preconditions to the lattice
  meet so the spec-authoring trap (raw `∧` stops the driver) disappears.

- Dead-hypothesis elimination (Kraken/ClearDead.lean, EXPERIMENTAL): accessor
  stepping emits one equation per state component per instruction; a
  postcondition reads few of them. Pruning the unreachable ones cuts
  `bv_decide` from 3.84s to 0.70s at n=640 (5.5x) on the register chain,
  because dead flag equations are no longer bitblasted.
  Status: the reachability criterion (goal -> equation LHS/RHS edges) prunes
  correctly on `addRI` chains (43 -> 19 hypotheses at n=8) but over-prunes on
  `adc` chains, where a proof that passes without it fails with it. Cause not
  identified; suspect term-representation mismatch between an equation LHS and
  its occurrences in other RHSs (projection vs. projection-function form), so
  the criterion needs representation-insensitive matching rather than
  structural `Expr` equality.
  Note `Lean.Elab.Tactic.Do.elimLets` already carries the use-counting
  (zero/one/many) analysis and scans the local context, but only eliminates
  let-bound decls (`decl.value?`), so it is a no-op on these equation
  hypotheses (measured: identical times with and without).
