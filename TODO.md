# TODO

- The p3 extraction layer restates the program: `p3_dirs`
  (Kraken/Examples/P3.lean) spells the laid-out directive list a second time,
  and the loop and exit segments exist only as `List.drop` computations inside
  proofs. Give each subprogram its own def, build `p3` from those defs, and
  state the extraction lemmas against them, so every directive is written
  once.

- The deep segment instance (Kraken/SegmentWP.lean) reads only `env.labels`:
  respell its assertion language over `Labels` and drop the `⟨e.labels, n⟩`
  reader argument from `straightlineStep_of_wp`. `Env.curSize` carries the
  current instruction's extent for the shallow layer, which cannot read it off
  the syntax: `execDir` sets it per instruction via `withCurSize`, and
  `evalAddr`, the memory specs and `liftBaseline` build the position range
  `.mk rip (rip + curSize)` from it. `Env` stays that layer's reader and
  retires with it.

- Whole-program adequacy against the baseline: chain
  `Executable.straightlineM_adequate` (Kraken/Adequacy.lean) through the
  baseline's `Eventually`, so a k-segment monadic run discharges into
  `Eventually (straightlineStep e) (· = st)`, and connect
  `execProgram`/`liftProgram` (AdequacyProgram.lean) to it through the `lm_*`
  dictionary.

- Engine (lean4/kernel): the kernel defeq relating the monadic and CPS
  elaborations of the AVX memory access (`AvxRegOrMem.interpM`'s mem arm
  against `AvxRegOrMem.interp`, both heading
  `(AddrExpr.interp …).zeroExtend _` at `AvxWidth`) takes ~330s, a kernel
  deterministic timeout at default heartbeats; the `Width`-side twin of the
  same shape checks in milliseconds, and the elaborator closes both instantly.
  The AVX monadic re-encoding was dropped rather than pay this per build (AVX
  instructions throw `unimplemented` in `Instr.interpM`); to reproduce,
  re-add `MachineData.loadAvxM` and `AvxRegOrMem.interpM` to Kraken/X64M.lean
  and prove `(AvxRegOrMem.interp (.mem a) s p ret).All post` from the
  `MachineM.Outcomes` hypothesis by `exact MachineData.loadAvxM_All h`.

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

- `easm` address canonicalization does not bridge a write to a non-address
  register. When an instruction writes a register that the accessed address does
  not mention, the memory VC carries `Addr.eval a (regs.set64 r v)` while the
  provided `h_load` fact is stated over `Addr.eval a regs`. The first simp pass
  keeps `Addr.eval` folded, so the two addresses differ syntactically and the
  fact does not fire; the second pass unfolds `Addr.eval` and `Reg64s.get64` in
  the VC but leaves the folded fact unmatched. Repro: `Kraken/Examples/AluMem.lean`
  with a `movq $42, %rax` before the store (the `rax` write shifts the store
  address off `s₀.regs`). The examples work around it by keeping addresses
  register-write-free at each access, or by supplying the address equality as a
  hypothesis (`ha8'` in `Kraken/Examples/Move2RegsToHeap.lean`). Fix: canonicalize
  register reads over writes at the folded level (add `Reg64s.get64_set64` to the
  first pass), or pre-normalize the added hypotheses with the address-unfold set so
  both sides of the match are unfolded together. A stack address `get64 rsp` over
  `set64` writes does not hit this: `simplifying_assumptions` folds it to a literal
  offset that matches the store, so `Kraken/Examples/PushPop.lean` composes `push`,
  a clobber and `pop` back with `easm` reading the mapped-ness and stored value.

- Conditional jumps compose through the `@[spec]` triple. `Op.jnz_spec`'s
  precondition `if s.status.zf then Q () s else E (.jump l) s` is premise-free and
  conjunctive in the schematic posts, so `vcgen` applies it directly; a `vcgen`
  strategy then splits the precondition on `s.status.zf`, threading the decided flag
  into context, stepping the fall-through continuation under the set-flag branch and
  sending the jump target to the exception post under the clear-flag branch.
  `Kraken/Examples/Cond.lean` runs `dec %rax; jnz; mov` through `vcgen [condProg]`.
  Two toolchain changes back this: `isConjunctiveIn` treats an `ite`/`dite` with a
  post-free condition as conjunctive, and `solve` splits a top-level `ite`/`dite`/
  matcher on the entailment RHS.

- MMIO and DMA compose through the device layer (`Kraken/Device.lean`). Device
  state `D` is the `device` component of `Sys D`, alongside the CPU `machine`, so
  it lives in the exception-carrying state of `X64M D` and a `jump` preserves it.
  Register and arithmetic actions stay polymorphic in `D`: they read and write
  `machine` and thread `device`, stepping unchanged under their existing `@[spec]`
  triples. Only the memory primitives become device-aware: `Op.devLoad`/`Op.devStore`
  consult a `Device D` model on an unmapped address instead of faulting. A device
  handler reads and returns data memory alongside device state, so a load or store
  transitions the device and either one moves ownership of a memory range between
  `dmem` and the device: all four transfers of the MMIO/DMA matrix. Each spec's
  precondition matches on the address being mapped and on the device accepting it,
  premise-free and conjunctive in the schematic posts, so `vcgen` applies it
  directly and splits per branch. `Kraken/Examples/Increment{MMIO,DMA}.lean` run
  device programs through `vcgen` with no unfolding.

- Benchmark harness and the current numbers: bench/README.md.
