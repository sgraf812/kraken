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

- `kfold` reduces a ground read-over-write conditional with a step justified by
  definitional unfolding of the `Decidable` instance (`Meta.mkEqRefl`), which
  the kernel then repeats: AdcChain(640) kernel time is 8.3s against 6.4s for
  the `simp only` discharge, so the defeq route is measurably paid for twice.
  The idiomatic fix is to reduce the *condition* to `True`/`False` and let
  `Sym.Simp.simpIte` (Simp/ControlFlow.lean:22) rewrite the conditional with
  its own `ite_cond_eq_true`/`ite_cond_eq_false` proof term; `simpIte` already
  calls `simp` on the condition, so a constructor-equality simproc in `post` is
  all that is missing. An attempt at that (`eq_self` / `eq_false` with
  `mkDecideProof`) did not fire and the failure was swallowed by a `try`; it
  needs one debugging pass with the catch removed. Cost of not doing it, on
  AdcChain(640): discharge 258ms against 844ms for the `simp only` route, but
  kernel 5226ms against 4337ms, so the extra kernel work exceeds the discharge
  saving and the fold is a net loss on carry chains. AddChain and DecChain do
  not pay this. Note `Sym.Simp.simpMatch`
  (Simp/ControlFlow.lean:124) justifies matcher iota-reduction with `mkEqRefl`
  too, so a defeq-justified step is the framework's own idiom for iota; the
  question is only whether evaluating a `Decidable` instance is as cheap as
  matcher iota, and the kernel numbers above say it is not.
  Unfolding the register file so that a concrete read reduces is worse:
  AddChain(160) discharge goes 31ms to 97ms and AdcChain exceeds simp's step
  budget (12.7s). `getEqnsFor?` gives the smart unfolding (one equation per
  constructor, so no matcher is ever exposed), and the two halves differ:
  `get64`'s equations are cheap, each rewriting a read to a field projection,
  but `set64`'s rewrite a write to a full sixteen-field record literal, and a
  chain of writes then carries one such literal per step. The shape worth
  trying is `get64`'s equations together with the per-field read-over-write
  lemmas kraken already has (`Reg64s.rax_set64` and friends), which keep the
  write folded; they still leave a conditional, but on a ground register.
- `clear_dead` cannot move into `SymM`: rewriting the local context is outside
  what `Sym` supports, so it stays a `MetaM` tactic.
