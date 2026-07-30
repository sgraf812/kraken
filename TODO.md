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

- Dead-hypothesis elimination (KrakenTactics/ClearDead.lean): pruning the
  equation hypotheses unreachable from the goal cuts `bv_decide` from 3.84s to
  0.69s at n=640 (5.5x), since dead component equations are no longer
  bitblasted. Whole-file wall time 8.83s -> 8.10s; the remainder is vcgen
  stepping, kernel typechecking and compiling the benchmark program.
  The analysis needs closure under rewriting of projection paths: steps read
  components at different granularities (`movRI` relates a whole `status`,
  `addRI` defines its `cf` field, `adc` reads that field), so without the
  closure the carry clear a chain depends on is classified dead. Closing over
  every reachable subterm is correct but takes 180s at n=160; restricting the
  rewrite to path-shaped terms is correct and cheap.
  `Lean.Elab.Tactic.Do.elimLets` carries a use-counting (zero/one/many)
  analysis and scans the local context, but only eliminates let-bound decls
  (`decl.value?`), so it is a no-op on equation hypotheses (measured: identical
  times with and without). Use-counting also cannot express this criterion: the
  dead flag equation and the needed register equation both have zero fvar-uses.
  The tactic lives in the `KrakenTactics` lean_lib with `precompileModules`,
  without which it runs interpreted (4.02s of a 8.9s run vs 3.87ms compiled).
