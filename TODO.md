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

- Benchmarks follow the lean4 `tests/bench/vcgen` setup (bench/lib/Driver.lean
  is a copy): the program is a recursive function of `n`, so a run elaborates
  a fixed amount of source at any size, and the driver reports stepping,
  discharge and kernel time separately. The generator in bench/gen.py emits
  `n` lines of source instead, which at n=640 spends 1.8s compiling the
  program; prefer the Cases/ form for anything scaling-related.
  Phase split on the register add chain (ms): stepping 57/229/1166 at
  n=40/160/640 (linear), kernel 14/101/1210, discharge 131/549/4572 plain and
  55/303/3119 with `clear_dead`. Stepping and kernel scale; the discharge does
  not, and is where the remaining work is.

- `kfold` now leaves the read-over-write conditional to `Sym.Simp.simpIte`,
  which supplies its own `ite_cond_eq_false` proof term; a simproc only decides
  the condition. Getting that to fire required returning the *shared* `True` /
  `False` from `Sym.getTrueExpr`/`getFalseExpr`, since `simpIte` tests them
  with pointer equality and a freshly built `mkConst ``False` leaves the
  conditional standing.
  The disequality is proved with `Meta.mkNoConfusion`, structurally, so the
  kernel never evaluates a `Decidable` instance.
  None of this closes the kernel gap on carry chains: AdcChain(640) kernel is
  ~5.2-5.6s against ~4.3s for the `simp only` discharge, the same as with the
  earlier defeq-justified conditional (5226ms) and with a decide-based
  disequality (5196ms). Three proof shapes, one number, so the conditional is
  not where the kernel time goes. Note `Sym.Simp.evalGround` justifies every
  ground evaluation with `Eq.refl` by design ("the kernel verifies
  correctness"), so a defeq-heavy certificate is inherent to folding this way.
  What has not been measured is which part of the certificate the kernel
  actually spends its time on: the substitution spine, `collapseAdd`'s
  `add_assoc_rev` applications, or `evalGround`'s refl steps. Measure before
  optimising further.
- `clear_dead` cannot move into `SymM`: rewriting the local context is outside
  what `Sym` supports, so it stays a `MetaM` tactic.

- Kernel checking is super-linear in these proofs because each congruence node
  carries a type that deepens with the chain: cost is the sum over nodes of the
  type size, not the shared term size. Isolated in
  kernel-congr-quadratic-mwe.lean, where holding node count fixed and shrinking
  only the node types takes n=1600 from 3593ms to 4ms.
  The fix is to fold at the component level rather than inside the term:
  forward-substitute to each queried component's final value, emit one small
  equation per component (`s_n.regs.get64 rax = 1920#64`), and rewrite the goal
  once with those, so every node's type stays constant-size. `kfold` currently
  rewrites the goal, so `Sym.Simp` descends into the state term and builds the
  growing-type shape; that is why both discharges scale identically and why no
  discharge-level tuning changes the exponent.

- The component-level fold is implemented in `kfold` (a loop over the chain
  that computes each equation's right-hand side against the values already
  known) but it does NOT yet fix the kernel scaling: certificate and kernel
  time are unchanged (AddChain n=320: DAG 52776, kernel ~350ms either way).
  The reason is that the loop keys its environment on the equation left-hand
  sides, which are whole record components (`s_k.regs`), whose value is a write
  chain as long as the program. Adding write-over-write collapse
  (`set64_set64_self`) does not help either, and slightly grows the
  certificate.
  What is needed is to key on the *reads*: maintain `(state, register) ↦
  (literal, proof)` and derive step k's read value from step k-1's, so each
  proved equation is `s_k.regs.get64 r = <literal>` with both sides
  constant-size, and the goal is then rewritten in one step at depth one. As
  implemented the final rewrite still descends into `s_n.regs.get64 r`, and
  that descent is what builds the congruence nodes whose types deepen.

- Proof-sharing through the goal: asserted hypotheses do not survive
  instantiation (`assert` produces `?goal prf`, and instantiating the
  metavariable beta-reduces, splicing `prf` into every use site), while
  `define`d `let`s do. `kfold` now `define`s each folded component equation, so
  the certificate tree went from 2^n (Eq.trans count 2^(n+2)-1, from the two
  occurrences of the previous register file per step) to linear, verified by a
  DAG-memoized tree-size count (97k -> 191k for n=4 -> 8). Pretty-printed size
  is a misleading proxy: indentation alone contributes depth x lines = n^2
  bytes.
- Lazy program unfolding: passing the recursive program to vcgen as an equation
  spec (`vcgen [AddChain.chain]` with no upfront unfold) keeps the residual
  program folded in every wp type and makes stepping ~4x faster and linear.
  The bench driver's upfront-unfold path is the slow variant.
- clear_dead reverse sweep: also drops let-bound fold proofs and unreachable
  plain hypotheses; after kfold the solver sees a single hypothesis.
- REMAINING: kernel time is still ~n^1.7 on a certificate whose tree, DAG and
  depth are all linear and whose visible argument types are constant-size.
  Refuted so far: unfolding counts, defeq-heuristic counts, eagerReduce,
  certificate size/sharing/depth, context size, interleaved single-binder
  lambdas (linear in isolation), flat Eq.trans chains (linear), growing-type
  congruence chains are quadratic in isolation but the audited certificate
  shows no growing types. Next suspects, unmeasured: is_def_eq forced
  reductions of `chain <literal>` through `Nat.rec`/`brecOn` (unary literal
  recursion at each step), and beta-expansion of `le_forall` motives during
  application checking.
