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
  reload VCs (the remaining sorry).
- Engine (vcgen): normalize `And` at Prop-valued preconditions to the lattice
  meet so the spec-authoring trap (raw `∧` stops the driver) disappears.
- Engine (vcgen): `simplifying_assumptions` accepts rewrite theorems only. Its
  methods are `simpControl >> simpArrowTelescope` and `evalGround >> rewrite`,
  and named `Sym.simp` variants are rejected, so a workload cannot contribute a
  simproc. That is why register identity goes through `Reg64.idx`: the pass can
  compare two `Nat` numerals but not two constructors. Either expose a simproc
  hook, or give `evalGround` enum-constructor equality.

- The spec style is one `@[spec]` triple per instruction whose precondition is
  the postcondition applied to a record update of the pre-state. Stating the
  post-state as a `let` instead builds the identical rule, since `Sym`'s
  `preprocessType` zeta-reduces every rule type and `Pattern` cannot represent
  `letE`; measured, the two differ by three nodes in the certificate DAG.

- Kernel checking is super-linear in these proofs because each congruence node
  carries a type that deepens with the chain: cost is the sum over nodes of the
  type size, not the shared term size. Isolated in
  kernel-congr-quadratic-mwe.lean, where holding node count fixed and shrinking
  only the node types takes n=1600 from 3593ms to 4ms. A spine of non-adjacent
  binders is quadratic for the same reason: kernel-letchain-superlinear-mwe.lean.
  Under the current pipeline the exponent is down to about 1.4 (AddChain kernel
  13/54/356 ms at n=40/160/640) from about 1.7, but it is still the largest
  single item at n=640 and the one to attack next.

- `clear_dead` (KrakenTactics/ClearDead.lean) prunes the equation hypotheses
  unreachable from the goal. The analysis needs closure under rewriting of
  projection paths, since steps read components at different granularities;
  closing over every reachable subterm is correct but takes 180s at n=160,
  restricting the rewrite to path-shaped terms is correct and cheap.
  `Lean.Elab.Tactic.Do.elimLets` cannot express the criterion: it only
  eliminates let-bound decls, and use-counting does not separate a dead flag
  equation from a needed register equation, since both have zero fvar-uses.
  The tactic lives in the `KrakenTactics` lean_lib with `precompileModules`,
  without which it runs interpreted (4.02s of a 8.9s run vs 3.87ms compiled).
  It cannot move into `SymM`: rewriting the local context is outside what `Sym`
  supports, so it stays a `MetaM` tactic.

- Proof-sharing through the goal: asserted hypotheses do not survive
  instantiation (`assert` produces `?goal prf`, and instantiating the
  metavariable beta-reduces, splicing `prf` into every use site), while
  `define`d `let`s do. `kfold` `define`s each folded component equation, so the
  certificate tree went from 2^n (Eq.trans count 2^(n+2)-1, from the two
  occurrences of the previous register file per step) to linear, verified by a
  DAG-memoized tree-size count. Pretty-printed size is a misleading proxy:
  indentation alone contributes depth x lines = n^2 bytes.

- Lazy program unfolding: passing the recursive program to vcgen as an equation
  spec (`vcgen [AddChain.chain]` with no upfront unfold) keeps the residual
  program folded in every wp type and makes stepping ~4x faster and linear.
  The bench driver's upfront-unfold path is the slow variant.

- Benchmark harness and the current numbers: bench/README.md.
