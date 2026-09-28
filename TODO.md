# TODO

- Fragments. The p3 extraction layer restates the program: `p3_dirs`
  (Kraken/Examples/P3.lean) spells the laid-out directive list a second time,
  and the loop and exit segments exist only as `List.drop` computations inside
  proofs. Writing each directive once needs subprograms that carry their own
  sizes, which `Layout.size : Nat → Nat` cannot give: a position is a
  coordinate the enclosing list imposes, so it changes when a subprogram is
  embedded. Key the sizes on the directive and the address instead, both of
  which are stable under embedding:

      abbrev Sizing := Directive → Int64 → Nat
      class LawfulSizing (sz : Sizing) : Prop where
        label_zero : ∀ l a, sz (.label l) a = 0
        instr_pos  : ∀ d a, (∀ l, d ≠ .label l) → 0 < sz d a
      def Program.layoutAt (sz : Sizes) (base : Int64) : Program → List (Directive × Nat)

  The directive argument carries its weight twice over: an instruction's length
  depends on its content, and `sz d a` reads as "if `d` were placed at `a` it
  occupies this many bytes", so the function is total without junk values. The
  address argument keeps alignment expressible, since `nopalign`'s padding is a
  function of the current address. `Directive.fakeSize` is a sizing, and
  `ToBytes`'s byte length will be another. The word "layout" stays with the
  operation and its result, so that the rule and the placed program keep
  separate names.

  Then: the composition equation
  `(as ++ bs).layoutAt sz base = as.layoutAt sz base ++ bs.layoutAt sz (base + as.byteLen sz base)`,
  and the label congruence `wpE` reads the label table only at the labels a
  segment mentions, which a fragment lemma needs as soon as the fragment jumps.

  `ValidLayout` can then say that the executable is what a lawful sizing
  produced:

      class ValidLayout (e : Executable) : Prop where
        laid_out : ∃ sz, LawfulSizing sz ∧ e.2 = e.program.layoutAt sz e.1
        no_wrap  : (e.2.map (·.2)).sum < 2 ^ 64

  The two readings accept the same executables. A lawful sizing gives labels
  size zero and every other directive a positive size. In the other direction,
  `sz d a` is the recorded size when `d` sits at `a`, and one elsewhere, which
  is well defined because addresses increase past every non-label directive.
  The current three fields survive as lemmas, so call sites keep their names,
  and a suffix inherits validity from the same witness:
  `ValidLayout (e.addrOf n, e.2.drop n)`.

  When `ToBytes` provides a total `Directive → Int64 → List UInt8`, a sizing
  arrives as its length: `fun d a => (enc d a).length`.

- Deep-pipeline goals duplicate machine states: each spec application splices
  the successor state literal into the continuation, so a k-step segment goal
  nests k states and the branch hypotheses carry copies. Extract each distinct
  state into a local hypothesis: `kfold`'s pointer-keyed substitution
  machinery (KrakenTactics/Fold.lean) walking the other direction, `define`-ing
  one let per distinct state literal and rewriting its occurrences to the
  variable. `define`d lets survive metavariable instantiation, and a
  `let`-bound post-state in the spec statement itself is zeta-reduced away by
  `Sym.preprocessType` before the rule is built.

- Toolchain: the `lean4-hom` pin cannot move to a stock nightly yet. Nightly
  2026-08-12 ships the `[grind hom]` attribute and its rule store
  (`Lean/Meta/Tactic/Grind/Homo.lean`, `Init/Grind/Homo/*`) but not the solver
  extension `Lean/Meta/Tactic/Grind/Homomorphism.lean`, and `Grind.Config` has no
  `homo` field, so the attribute is accepted and inert. `Kraken/Specs.lean`'s
  `@[grind hom] BitVec.unsigned_hom` then buys nothing and `grind` can no longer
  cross `UInt64.toNat`/`BitVec.toNat`, which fails `p3_enter`, `p3_body` and
  `p3_exit`. One line shows it:
  `example (x : UInt64) (h : x = ⟨2#64⟩) : x.toNat = 2 := by grind`, which the
  pinned toolchain closes and the nightly does not; `grind -homo` on the pinned
  toolchain reproduces the nightly's failures with identical case names. `vcgen`
  itself is not implicated: the verification conditions are byte-identical under
  both toolchains. Everything else needed for the bump is already done, so once
  the hom solver lands upstream the pin can move.

- Engine (vcgen, parked): PR #14746 (draft, branch `sg/vcgen-split-conditional-pre`,
  head bf6a55ec03) splits a case analysis on the right-hand side of an entailment,
  so a spec whose precondition branches on a decidable state condition applies and
  each branch steps on. `mkBackwardRuleForTopLevelSplit` mirrors the program-level
  `mkBackwardRuleForSplit` (discriminant abstraction, eta-reduced matcher alts,
  `useSplitter := true`, excess-argument binders, congruence proof, per-shape cache);
  the strategy `splitRhsCase?` replaces the earlier `splitTarget?` call, so no MetaM
  tactic remains in the pipeline. Verified: ite, dite, matcher, and a non-empty state
  telescope, each failing before and silent after; `tests/elab/vcgenImp.lean` gains a
  branch VC per arm. Left to do before review: rebase onto master (it predates #14747,
  which also touches Solve.lean) and add a `@[frameproc]`-monad test, since the
  `isConjunctiveIn` arm is currently unexercised (`defaultFrameInferenceProc` frames
  only under a `frames` clause) and `isConjunctiveIn` has no matcher arm at all.

- Engine (lean4/vcgen): a spec whose exception postcondition is `epost⟨E⟩` with `E`
  schematic is applied at `E := ⊥`. `mkSpecBackwardProof`'s guard
  (`RuleConstruction.lean:228`) runs `isDefEqGuarded epostSpec ⊥`, which assigns the
  metavariable instead of rejecting, and `wp_econs_bot_le` then weakens the goal's
  exception postcondition away. Completeness bug, not soundness: the VC becomes the
  strictly stronger `⊥`. Reproducer: spec `⦃E "boom"⦄ boom ⦃post; epost⟨E⟩⦄` for
  `def boom : ExceptT String (StateM Nat) Unit := throw "boom"` applied to a goal with
  `epost⟨fun msg s => msg = "boom" ∧ s = 0⟩` yields `⊢ ⊥`; stating the whole `EPost`
  schematic yields the correct `⊢ s = 0`. The throw must sit behind a named `def` or the
  builtin `Spec.throw_MonadExcept` wins. The `tests/bench/vcgen` specs use the
  `epost⟨epost⟩` spelling and escape it only because their goals already carry `⊥`.

- Engine (lean4/grind): `internalize` does not share/canonicalize its argument
  (`Grind.add`/`addFactStep` likewise); the hash-consing invariant `mkEqProof`
  relies on is unmaintainable caller-side (accessor-obtained terms are only
  sometimes pointer-identical to session nodes). Fix: `internalize` runs
  `preprocessLight`-class sharing itself;
  defense in depth: `mkCongrDefaultProof` treats the all-`isSameExpr` case as
  `rfl`. Reproducer: mkEqProof-panic-mwe.lean.
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
  Kernel checking is the largest single item at n=640 in bench/README.md.

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
  spec (`vcgen [SegAdcChain.chain]` with no upfront unfold) keeps the residual
  program folded in every wp type and makes stepping ~4x faster and linear.
  The bench driver's upfront-unfold path is the slow variant.

- Benchmark harness and the current numbers: bench/README.md.
